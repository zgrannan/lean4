/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {

struct abstract_policy {
    static constexpr bool only_atomic = true;
    unsigned     m_n;
    expr const * m_subst;
    bool should_return_self(expr const & m, unsigned) const {
        return !has_fvar(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        if (is_fvar(m)) {
            name const & fn = fvar_name(m);
            unsigned i = m_n;
            while (i > 0) {
                --i;
                if (fvar_name(m_subst[i]) == fn)
                    return mk_bvar(offset + m_n - i - 1);
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(e); }));
    if (!has_fvar(e) || n == 0)
        return e;
    return replace_custom(e, abstract_policy{n, subst});
}

struct abstract_raw_policy {
    static constexpr bool only_atomic = true;
    size_t   m_n;
    object * m_subst;
    bool should_return_self(expr const & m, unsigned) const {
        return !has_fvar(m) && !has_mvar(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        bool fv = is_fvar(m);
        bool mv = is_mvar(m);
        if (fv || mv) {
            size_t i = m_n;
            while (i > 0) {
                --i;
                object * v = lean_array_get_core(m_subst, i);
                if (fv && is_fvar_core(v) && fvar_name_core(v) == fvar_name(m))
                    return mk_bvar(offset + m_n - i - 1);
                if (mv && is_mvar_core(v) && mvar_name_core(v) == mvar_name(m))
                    return mk_bvar(offset + m_n - i - 1);
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

static object * lean_expr_abstract_core(object * e0, size_t n, object * subst) {
    lean_assert(n <= lean_array_size(subst));
    expr const & e = reinterpret_cast<expr const &>(e0);
    if ((!has_fvar(e) && !has_mvar(e)) || n == 0) {
        lean_inc(e0);
        return e0;
    }
    expr r = replace_custom(e, abstract_raw_policy{n, subst});
    return r.steal();
}

extern "C" LEAN_EXPORT object * lean_expr_abstract_range(object * e, object * n, object * subst) {
    if (!lean_is_scalar(n))
        return lean_expr_abstract_core(e, lean_array_size(subst), subst);
    else
        return lean_expr_abstract_core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
}

extern "C" LEAN_EXPORT object * lean_expr_abstract(object * e, object * subst) {
    return lean_expr_abstract_core(e, lean_array_size(subst), subst);
}
}
