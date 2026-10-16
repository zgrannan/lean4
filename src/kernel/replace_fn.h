/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include <type_traits>
#include <functional>
#include <cstdlib>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {
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

/* Open-addressing hash table from (object, binder offset) to the replaced expression. */
class replace_cache {
    struct entry {
        lean_object * m_key;
        unsigned      m_offset;
        lean_object * m_value;
    };
    entry * m_table = nullptr;
    size_t  m_mask = 0;
    size_t  m_size = 0;

    static size_t hash_of(lean_object * k, unsigned offset) {
        uint64_t h = (static_cast<uint64_t>(reinterpret_cast<uintptr_t>(k)) >> 3) * 0x9E3779B97F4A7C15ull;
        h ^= (static_cast<uint64_t>(offset) + 1) * 0xC2B2AE3D27D4EB4Full;
        return static_cast<size_t>(h ^ (h >> 29));
    }
    void grow() {
        size_t new_cap = m_table ? (m_mask + 1) * 2 : 32;
        entry * old = m_table;
        size_t old_cap = m_table ? m_mask + 1 : 0;
        m_table = static_cast<entry *>(calloc(new_cap, sizeof(entry)));
        if (!m_table) lean_internal_panic_out_of_memory();
        m_mask = new_cap - 1;
        for (size_t i = 0; i < old_cap; i++) {
            if (old[i].m_key) {
                size_t j = hash_of(old[i].m_key, old[i].m_offset) & m_mask;
                while (m_table[j].m_key) j = (j + 1) & m_mask;
                m_table[j] = old[i];
            }
        }
        free(old);
    }
public:
    replace_cache() {}
    replace_cache(replace_cache const &) = delete;
    ~replace_cache() {
        if (m_table) {
            for (size_t i = 0; i <= m_mask; i++) {
                if (m_table[i].m_key) lean_dec(m_table[i].m_value);
            }
            free(m_table);
        }
    }
    /* Returns the cached result (borrowed) or `nullptr`. */
    lean_object * find(lean_object * k, unsigned offset) const {
        if (!m_table) return nullptr;
        size_t j = hash_of(k, offset) & m_mask;
        while (m_table[j].m_key) {
            if (m_table[j].m_key == k && m_table[j].m_offset == offset) return m_table[j].m_value;
            j = (j + 1) & m_mask;
        }
        return nullptr;
    }
    /* Remembers `v` (a new reference is taken) as the result for `(k, offset)`, which must not be present. */
    void insert(lean_object * k, unsigned offset, lean_object * v) {
        if (2 * (m_size + 1) > (m_table ? m_mask + 1 : 0)) grow();
        size_t j = hash_of(k, offset) & m_mask;
        while (m_table[j].m_key) {
            if (m_table[j].m_key == k && m_table[j].m_offset == offset) return;
            j = (j + 1) & m_mask;
        }
        lean_inc(v);
        m_table[j] = { k, offset, v };
        m_size++;
    }
};

/* The functor type is a template parameter so that the callback can be inlined; see `replace`.
   With `Cheap`, the callback takes constant time on the subterms it returns unchanged and returns
   such a subterm itself; the cache is then neither consulted nor filled for those and for leaves. */
template<typename F, bool Cheap = false>
class replace_rec_fn_t {
    replace_cache m_cache;
    F const &     m_f;
    bool          m_use_cache;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), offset, r.raw());
        return r;
    }

    static bool is_leaf(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort: case expr_kind::BVar:
        case expr_kind::Lit:   case expr_kind::MVar: case expr_kind::FVar:
            return true;
        default:
            return false;
        }
    }

    expr apply(expr const & e, unsigned offset) {
        bool shared = false;
        optional<expr> r;
        if constexpr (Cheap) {
            r = m_f(e, offset);
            if (r) {
                if (r->raw() == e.raw()) return std::move(*r);
            } else if (is_leaf(e)) {
                return e;
            }
        }
        if (m_use_cache && !is_likely_unshared(e)) {
            if (lean_object * c = m_cache.find(e.raw(), offset))
                return expr(c, true);
            shared = true;
        }
        if constexpr (!Cheap) r = m_f(e, offset);
        if (r) {
            return save_result(e, offset, std::move(*r), shared);
        } else {
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
    }
public:
    replace_rec_fn_t(F const & f, bool use_cache) : m_f(f), m_use_cache(use_cache) {}
    expr operator()(expr const & e) { return apply(e, 0); }
};

/* `replace` for callbacks that satisfy the `Cheap` condition of `replace_rec_fn_t`. */
template<typename F>
expr replace_cheap(expr const & e, F const & f, bool use_cache = true) {
    return replace_rec_fn_t<F, true>(f, use_cache)(e);
}

/* Overload for callbacks given as lambdas, which avoids the `std::function` indirection. */
template<typename F>
requires std::is_invocable_r_v<optional<expr>, F const &, expr const &, unsigned> &&
         (!std::is_same_v<std::remove_cvref_t<F>, std::function<optional<expr>(expr const &, unsigned)>>)
expr replace(expr const & e, F const & f, bool use_cache = true) {
    return replace_rec_fn_t<F>(f, use_cache)(e);
}
}
