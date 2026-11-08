/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include <vector>
#include <cstring>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {

struct replace_cache {
    static constexpr size_t CAPACITY = 65536;
    static constexpr size_t MASK = CAPACITY - 1;
    struct slot {
        lean_object * key;
        lean_object * val;
        uint32_t      offset;
        uint32_t      epoch;
    };
    slot                        m_slots[CAPACITY];
    std::vector<lean_object *>  m_to_dec;
    uint32_t                    m_epoch = 1;
    uint32_t                    m_depth = 0;

    replace_cache() {
        std::memset(m_slots, 0, sizeof(m_slots));
        m_to_dec.reserve(1024);
    }
    ~replace_cache() {
        for (lean_object * o : m_to_dec) {
            lean_dec_ref(o);
        }
        m_to_dec.clear();
    }

    uint32_t enter() {
        if (m_depth == 0 && m_epoch > 0xFFFF0000u) {
            std::memset(m_slots, 0, sizeof(m_slots));
            m_epoch = 1;
        }
        ++m_depth;
        return ++m_epoch;
    }

    void leave() {
        lean_assert(m_depth > 0);
        if (--m_depth == 0) {
            for (lean_object * o : m_to_dec) {
                lean_dec_ref(o);
            }
            m_to_dec.clear();
        }
    }

    lean_object * find(lean_object * key, uint32_t offset, uint32_t my_epoch) const {
        size_t idx = static_cast<size_t>(hash(static_cast<unsigned>((uintptr_t)key >> 3), offset)) & MASK;
        for (unsigned i = 0; i < 4; ++i) {
            slot const & s = m_slots[(idx + i) & MASK];
            if (s.epoch == my_epoch) {
                if (s.key == key && s.offset == offset)
                    return s.val;
            } else if (s.epoch < my_epoch) {
                break;
            }
        }
        return nullptr;
    }

    void insert(lean_object * key, uint32_t offset, uint32_t my_epoch, lean_object * val) {
        if (!lean_is_scalar(val) && lean_has_rc(val)) {
            lean_inc_ref(val);
            m_to_dec.push_back(val);
        }
        size_t idx = static_cast<size_t>(hash(static_cast<unsigned>((uintptr_t)key >> 3), offset)) & MASK;
        for (unsigned i = 0; i < 3; ++i) {
            slot & s = m_slots[(idx + i) & MASK];
            if (s.epoch != my_epoch) {
                s.key    = key;
                s.val    = val;
                s.offset = offset;
                s.epoch  = my_epoch;
                return;
            }
        }
        slot & s = m_slots[(idx + 3) & MASK];
        s.key    = key;
        s.val    = val;
        s.offset = offset;
        s.epoch  = my_epoch;
    }
};

replace_cache & get_thread_replace_cache();

template<typename Policy>
class replace_custom_fn {
    replace_cache & m_cache;
    Policy const &  m_policy;
    uint32_t        m_epoch;
    bool            m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared) {
            m_cache.insert(e.raw(), offset, m_epoch, r.raw());
        }
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        if (m_policy.should_return_self(e, offset)) {
            return e;
        }
        if (Policy::only_atomic && is_atomic(e)) {
            return m_policy.visit_atomic(e, offset);
        }
        bool shared = false;
        if (m_use_cache && !is_likely_unshared(e)) {
            if (lean_object * cached = m_cache.find(e.raw(), offset, m_epoch)) {
                return expr(cached, true);
            }
            shared = true;
        }
        if (!Policy::only_atomic) {
            if (optional<expr> r = m_policy.visit(e, offset)) {
                return save_result(e, offset, std::move(*r), shared);
            }
        }
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return save_result(e, offset, e, shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e), offset);
            return save_result(e, offset, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e), offset);
            return save_result(e, offset, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e), offset);
            expr new_a = apply(app_arg(e), offset);
            return save_result(e, offset, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e), offset);
            expr new_b = apply(binding_body(e), offset+1);
            return save_result(e, offset, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e), offset);
            expr new_v = apply(let_value(e), offset);
            expr new_b = apply(let_body(e), offset+1);
            return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
        }
        }
        lean_unreachable();
    }
public:
    replace_custom_fn(Policy const & policy, bool use_cache = true):
        m_cache(get_thread_replace_cache()),
        m_policy(policy),
        m_epoch(m_cache.enter()),
        m_use_cache(use_cache) {}
    ~replace_custom_fn() {
        m_cache.leave();
    }
    expr operator()(expr const & e) { return apply(e, 0); }
};

template<typename Policy>
inline expr replace_custom(expr const & e, Policy const & policy, bool use_cache = true) {
    return replace_custom_fn<Policy>(policy, use_cache)(e);
}

/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}
}
