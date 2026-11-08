/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <cstring>
#include <memory>
#include "runtime/alloc.h"
#include "runtime/interrupt.h"
#include "runtime/thread.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "util/alloc.h"

namespace lean {

struct expr_eq_cache {
    static constexpr size_t CAPACITY = 16384;
    static constexpr size_t MASK = CAPACITY - 1;
    struct slot {
        lean_object * a;
        lean_object * b;
        uint32_t      epoch;
    };
    slot     m_slots[CAPACITY];
    uint32_t m_epoch = 0;
    uint32_t m_depth = 0;

    uint32_t enter() {
        if (LEAN_UNLIKELY(m_depth == 0 && m_epoch > 0xFFFF0000u)) {
            std::memset(m_slots, 0, sizeof(m_slots));
            m_epoch = 0;
        }
        ++m_depth;
        return ++m_epoch;
    }

    void leave() {
        --m_depth;
    }

    bool check_and_insert(lean_object * a, lean_object * b, uint32_t my_epoch) {
        size_t idx = static_cast<size_t>(hash(static_cast<unsigned>((uintptr_t)a >> 3), static_cast<unsigned>((uintptr_t)b >> 3))) & MASK;
        unsigned insert_pos = 3;
        for (unsigned i = 0; i < 4; ++i) {
            slot const & s = m_slots[(idx + i) & MASK];
            if (s.epoch == my_epoch) {
                if (s.a == a && s.b == b)
                    return true;
            } else {
                if (insert_pos == 3)
                    insert_pos = i;
                if (s.epoch < my_epoch)
                    break;
            }
        }
        slot & dst = m_slots[(idx + insert_pos) & MASK];
        dst.a     = a;
        dst.b     = b;
        dst.epoch = my_epoch;
        return false;
    }
};

static thread_local expr_eq_cache g_expr_eq_cache;

/**
\brief Functional object for comparing expressions.

Remark if CompareBinderInfo is true, then functional object will also compare
binder information attached to lambda and Pi expressions
*/
template<bool CompareBinderInfo>
class expr_eq_fn {
    uint32_t m_epoch = 0;
    size_t m_counter = 0;
    bool check_cache(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        if (m_epoch == 0)
            m_epoch = g_expr_eq_cache.enter();
        return g_expr_eq_cache.check_and_insert(a.raw(), b.raw(), m_epoch);
    }
    bool apply(expr const & a, expr const & b, bool root = false) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        switch (a.kind()) {
        case expr_kind::BVar: return bvar_idx(a) == bvar_idx(b);
        case expr_kind::Lit:  return lit_value(a) == lit_value(b);
        case expr_kind::MVar: return mvar_name(a) == mvar_name(b);
        case expr_kind::FVar: return fvar_name(a) == fvar_name(b);
        case expr_kind::Sort: return sort_level(a) == sort_level(b);
        default: break;
        }
        if (!root && check_cache(a, b)) {
            return true;
        }
        /*
           We increase the number of heartbeats here because some code (e.g., `simp`) may spend a lot of time comparing
           `Expr`s (e.g., checking a cache with many collisions) without allocating any significant amount of memory.
           We use the counter to invoke `add_heartbeats` later. Reason: heartbeat is a thread local storage, and morexpensive to update.
         */
        m_counter++;
        switch (a.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
        case expr_kind::MVar:
        case expr_kind::FVar:
        case expr_kind::Sort:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MData:
            return
                apply(mdata_expr(a), mdata_expr(b)) &&
                mdata_data(a) == mdata_data(b);
        case expr_kind::Proj:
            return
                apply(proj_expr(a), proj_expr(b)) &&
                proj_sname(a) == proj_sname(b) &&
                proj_idx(a) == proj_idx(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::App: {
            if (!apply(app_arg(a), app_arg(b))) return false;
            expr const * curr_a = &app_fn(a);
            expr const * curr_b = &app_fn(b);
            while (true) {
                if (!is_app(*curr_a)) break;
                if (!is_app(*curr_b)) return false;
                if (!apply(app_arg(*curr_a), app_arg(*curr_b))) return false;
                curr_a = &app_fn(*curr_a);
                curr_b = &app_fn(*curr_b);
            }
            return apply(*curr_a, *curr_b);
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            return
                apply(binding_domain(a), binding_domain(b)) &&
                apply(binding_body(a), binding_body(b)) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            return
                apply(let_type(a), let_type(b)) &&
                apply(let_value(a), let_value(b)) &&
                apply(let_body(a), let_body(b)) &&
                let_nondep(a) == let_nondep(b) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    expr_eq_fn() {}
    ~expr_eq_fn() {
        if (m_epoch != 0) g_expr_eq_cache.leave();
        if (m_counter > 0) add_heartbeats(m_counter);
    }
    bool operator()(expr const & a, expr const & b) { return apply(a, b, true); }
};

bool is_equal(expr const & a, expr const & b) {
    return expr_eq_fn<false>()(a, b);
}

extern "C" LEAN_EXPORT uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<false>()(TO_REF(expr, a), TO_REF(expr, b));
}

extern "C" LEAN_EXPORT uint8 lean_expr_equal(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<true>()(TO_REF(expr, a), TO_REF(expr, b));
}
}
