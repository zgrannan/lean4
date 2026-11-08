/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include "kernel/replace_fn.h"
#include "kernel/declaration.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"

namespace lean {

struct instantiate_policy {
    static constexpr bool only_atomic = true;
    unsigned     m_s;
    unsigned     m_n;
    expr const * m_subst;
    bool should_return_self(expr const & m, unsigned offset) const {
        unsigned s1 = m_s + offset;
        return s1 < m_s || s1 >= get_loose_bvar_range(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        if (is_bvar(m)) {
            nat const & vidx = bvar_idx(m);
            unsigned s1 = m_s + offset;
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= s1) {
                    unsigned h = s1 + m_n;
                    if (h < s1 || idx < h) {
                        return lift_loose_bvars(m_subst[idx - s1], offset);
                    } else {
                        return mk_bvar(nat::of_size_t(idx - m_n));
                    }
                }
            } else if (vidx >= s1) {
                unsigned h = s1 + m_n;
                if (h < s1 || vidx < h) {
                    return lift_loose_bvars(m_subst[vidx.get_small_value() - s1], offset);
                } else {
                    return mk_bvar(vidx - nat(m_n));
                }
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (s >= get_loose_bvar_range(a) || n == 0)
        return a;
    return replace_custom(a, instantiate_policy{s, n, subst});
}

expr instantiate(expr const & e, unsigned n, expr const * s) { return instantiate(e, 0, n, s); }
expr instantiate(expr const & e, unsigned i, expr const & s) { return instantiate(e, i, 1, &s); }
expr instantiate(expr const & e, expr const & s) { return instantiate(e, 0, s); }

extern "C" LEAN_EXPORT object * lean_expr_instantiate1(object * a0, object * e0) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a)) {
        lean_inc(a0);
        return a0;
    }
    expr const & e = reinterpret_cast<expr const &>(e0);
    expr r = instantiate(a, 1, &e);
    return r.steal();
}

struct instantiate_raw_policy {
    static constexpr bool only_atomic = true;
    size_t    m_n;
    object ** m_subst;
    bool should_return_self(expr const & m, unsigned offset) const {
        return offset >= get_loose_bvar_range(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        if (is_bvar(m)) {
            nat const & vidx = bvar_idx(m);
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= offset) {
                    size_t h = offset + m_n;
                    if (h < offset || idx < h) {
                        object * v = m_subst[idx - offset];
                        return lift_loose_bvars(TO_REF(expr, v), offset);
                    } else {
                        return mk_bvar(nat::of_size_t(idx - m_n));
                    }
                }
            } else if (vidx >= offset) {
                size_t h = offset + m_n;
                if (h < offset) {
                    object * v = m_subst[vidx.get_small_value() - offset];
                    return lift_loose_bvars(TO_REF(expr, v), offset);
                } else {
                    return mk_bvar(vidx - nat::of_size_t(m_n));
                }
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

static object * lean_expr_instantiate_core(b_obj_arg a0, size_t n, object** subst) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a) || n == 0) {
        lean_inc(a0);
        return a0;
    }
    expr r = replace_custom(a, instantiate_raw_policy{n, subst});
    return r.steal();
}

extern "C" LEAN_EXPORT object * lean_expr_instantiate(b_obj_arg a, b_obj_arg subst) {
    return lean_expr_instantiate_core(a, lean_array_size(subst), lean_array_cptr(subst));
}

extern "C" LEAN_EXPORT object * lean_expr_instantiate_range(b_obj_arg a, b_obj_arg begin, b_obj_arg end, b_obj_arg subst) {
    if (!lean_is_scalar(begin) || !lean_is_scalar(end)) {
        lean_internal_panic("invalid range for Expr.instantiateRange");
    } else {
        usize sz = lean_array_size(subst);
        usize b  = lean_unbox(begin);
        usize e  = lean_unbox(end);
        if (b > e || e > sz) {
            lean_internal_panic("invalid range for Expr.instantiateRange");
        }
        return lean_expr_instantiate_core(a, e - b, lean_array_cptr(subst) + b);
    }
}

struct instantiate_rev_policy {
    static constexpr bool only_atomic = true;
    unsigned     m_n;
    expr const * m_subst;
    bool should_return_self(expr const & m, unsigned offset) const {
        return offset >= get_loose_bvar_range(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        if (is_bvar(m)) {
            nat const & vidx = bvar_idx(m);
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= offset) {
                    size_t h = offset + m_n;
                    if (h < offset || idx < h) {
                        return lift_loose_bvars(m_subst[m_n - (idx - offset) - 1], offset);
                    } else {
                        return mk_bvar(nat::of_size_t(idx - m_n));
                    }
                }
            } else if (vidx >= offset) {
                size_t h = offset + m_n;
                if (h < offset) {
                    return lift_loose_bvars(m_subst[m_n - (vidx.get_small_value() - offset) - 1], offset);
                } else {
                    return mk_bvar(vidx - nat(m_n));
                }
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

expr instantiate_rev(expr const & a, unsigned n, expr const * subst) {
    if (!has_loose_bvars(a) || n == 0)
        return a;
    return replace_custom(a, instantiate_rev_policy{n, subst});
}

struct instantiate_rev_raw_policy {
    static constexpr bool only_atomic = true;
    size_t    m_n;
    object ** m_subst;
    bool should_return_self(expr const & m, unsigned offset) const {
        return offset >= get_loose_bvar_range(m);
    }
    expr visit_atomic(expr const & m, unsigned offset) const {
        if (is_bvar(m)) {
            nat const & vidx = bvar_idx(m);
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= offset) {
                    size_t h = offset + m_n;
                    if (h < offset || idx < h) {
                        object * v = m_subst[m_n - (idx - offset) - 1];
                        return lift_loose_bvars(TO_REF(expr, v), offset);
                    } else {
                        return mk_bvar(nat::of_size_t(idx - m_n));
                    }
                }
            } else if (vidx >= offset) {
                size_t h = offset + m_n;
                if (h < offset) {
                    object * v = m_subst[m_n - (vidx.get_small_value() - offset) - 1];
                    return lift_loose_bvars(TO_REF(expr, v), offset);
                } else {
                    return mk_bvar(vidx - nat::of_size_t(m_n));
                }
            }
        }
        return m;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

static object * lean_expr_instantiate_rev_core(object * a0, size_t n, object ** subst) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a) || n == 0) {
        lean_inc(a0);
        return a0;
    }
    expr r = replace_custom(a, instantiate_rev_raw_policy{n, subst});
    return r.steal();
}

extern "C" LEAN_EXPORT object * lean_expr_instantiate_rev(b_obj_arg a, b_obj_arg subst) {
    return lean_expr_instantiate_rev_core(a, lean_array_size(subst), lean_array_cptr(subst));
}

extern "C" LEAN_EXPORT object * lean_expr_instantiate_rev_range(b_obj_arg a, b_obj_arg begin, b_obj_arg end, b_obj_arg subst) {
    if (!lean_is_scalar(begin) || !lean_is_scalar(end)) {
        lean_internal_panic("invalid range for Expr.instantiateRevRange");
    } else {
        usize sz = lean_array_size(subst);
        usize b  = lean_unbox(begin);
        usize e  = lean_unbox(end);
        if (b > e || e > sz) {
            lean_internal_panic("invalid range for Expr.instantiateRevRange");
        }
        return lean_expr_instantiate_rev_core(a, e - b, lean_array_cptr(subst) + b);
    }
}

static expr apply_beta_rec(expr e, unsigned i, unsigned num_rev_args, expr const * rev_args, bool preserve_data, bool zeta) {
    if (is_lambda(e)) {
        if (i + 1 < num_rev_args) {
            return apply_beta_rec(binding_body(e), i+1, num_rev_args, rev_args, preserve_data, zeta);
        } else {
            return instantiate(binding_body(e), num_rev_args, rev_args);
        }
    } else if (is_let(e)) {
        if (zeta && i < num_rev_args) {
            return apply_beta_rec(instantiate(let_body(e), let_value(e)), i, num_rev_args, rev_args, preserve_data, zeta);
        } else {
            unsigned n = num_rev_args - i;
            return mk_rev_app(instantiate(e, i, rev_args + n), n, rev_args);
        }
    } else if (is_mdata(e)) {
        if (preserve_data) {
            unsigned n = num_rev_args - i;
            return mk_rev_app(instantiate(e, i, rev_args + n), n, rev_args);
        } else {
            return apply_beta_rec(mdata_expr(e), i, num_rev_args, rev_args, preserve_data, zeta);
        }
    } else {
        unsigned n = num_rev_args - i;
        return mk_rev_app(instantiate(e, i, rev_args + n), n, rev_args);
    }
}

expr apply_beta(expr f, unsigned num_rev_args, expr const * rev_args, bool preserve_data, bool zeta) {
    if (num_rev_args == 0) return f;
    return apply_beta_rec(f, 0, num_rev_args, rev_args, preserve_data, zeta);
}

expr cheap_beta_reduce(expr const & e) {
    if (!is_app(e)) return e;
    expr fn = get_app_fn(e);
    if (!is_lambda(fn)) return e;
    buffer<expr> args;
    get_app_args(e, args);
    unsigned i = 0;
    while (is_lambda(fn) && i < args.size()) {
        i++;
        fn = binding_body(fn);
    }
    if (!has_loose_bvars(fn)) {
        return mk_app(fn, args.size() - i, args.data() + i);
    } else if (is_bvar(fn)) {
        lean_assert(bvar_idx(fn) < i);
        return mk_app(args[i - bvar_idx(fn).get_small_value() - 1], args.size() - i, args.data() + i);
    } else {
        return e;
    }
}

struct instantiate_lparams_policy {
    static constexpr bool only_atomic = false;
    names const &  m_lps;
    levels const & m_ls;
    bool should_return_self(expr const & e, unsigned) const {
        return !has_param_univ(e);
    }
    expr visit_atomic(expr const & e, unsigned) const { return e; }
    optional<expr> visit(expr const & e, unsigned) const {
        if (is_constant(e)) {
            return some_expr(update_constant(e, map_reuse(const_levels(e), [&](level const & l) { return instantiate(l, m_lps, m_ls); })));
        } else if (is_sort(e)) {
            return some_expr(update_sort(e, instantiate(sort_level(e), m_lps, m_ls)));
        } else {
            return none_expr();
        }
    }
};

struct lparams_cache {
    static constexpr size_t CAPACITY = 16384;
    static constexpr size_t MASK = CAPACITY - 1;
    struct slot {
        lean_object * m_expr = nullptr;
        lean_object * m_lps  = nullptr;
        lean_object * m_ls   = nullptr;
        lean_object * m_res  = nullptr;
        ~slot() {
            if (m_expr) lean_dec(m_expr);
            if (m_lps)  lean_dec(m_lps);
            if (m_ls)   lean_dec(m_ls);
            if (m_res)  lean_dec(m_res);
        }
    };
    slot m_slots[CAPACITY];

    static unsigned hash_levels(levels const & ls) {
        unsigned h = 23;
        levels const * it = &ls;
        while (!is_nil(*it)) {
            h = hash(h, head(*it).hash());
            it = &tail(*it);
        }
        return h;
    }

    static bool eq_levels(lean_object * a_raw, levels const & b) {
        if (a_raw == b.raw()) return true;
        levels const & a = TO_REF(levels, a_raw);
        levels const * it1 = &a;
        levels const * it2 = &b;
        while (!is_nil(*it1) && !is_nil(*it2)) {
            if (!is_eqp(head(*it1), head(*it2)) && head(*it1) != head(*it2))
                return false;
            it1 = &tail(*it1);
            it2 = &tail(*it2);
        }
        return is_nil(*it1) && is_nil(*it2);
    }

    lean_object * find(expr const & e, names const & lps, levels const & ls, unsigned h) const {
        size_t idx = h & MASK;
        for (unsigned i = 0; i < 2; ++i) {
            slot const & s = m_slots[(idx + i) & MASK];
            if (s.m_expr == e.raw() && s.m_lps == lps.raw() && eq_levels(s.m_ls, ls)) {
                return s.m_res;
            }
        }
        return nullptr;
    }

    void insert(expr const & e, names const & lps, levels const & ls, expr const & res, unsigned h) {
        size_t idx = h & MASK;
        size_t target = (m_slots[idx].m_expr == nullptr) ? idx : ((idx + 1) & MASK);
        slot & s = m_slots[target];
        lean_inc(e.raw());
        lean_inc(lps.raw());
        lean_inc(ls.raw());
        lean_inc(res.raw());
        if (s.m_expr) lean_dec(s.m_expr);
        if (s.m_lps)  lean_dec(s.m_lps);
        if (s.m_ls)   lean_dec(s.m_ls);
        if (s.m_res)  lean_dec(s.m_res);
        s.m_expr = e.raw();
        s.m_lps  = lps.raw();
        s.m_ls   = ls.raw();
        s.m_res  = res.raw();
    }
};

static thread_local lparams_cache g_lparams_cache;

expr instantiate_lparams(expr const & e, names const & lps, levels const & ls) {
    if (!has_param_univ(e))
        return e;
    return replace_custom(e, instantiate_lparams_policy{lps, ls});
}

static expr instantiate_lparams_cached(expr const & e, names const & lps, levels const & ls) {
    unsigned h = hash(static_cast<unsigned>((uintptr_t)e.raw() >> 3), lparams_cache::hash_levels(ls));
    if (lean_object * cached = g_lparams_cache.find(e, lps, ls, h)) {
        return expr(cached, true);
    }
    kernel_arena_pause_scope pause;
    expr res = replace_custom(e, instantiate_lparams_policy{lps, ls});
    g_lparams_cache.insert(e, lps, ls, res, h);
    return res;
}

expr instantiate_type_lparams(constant_info const & info, levels const & ls) {
    if (info.get_num_lparams() != length(ls))
        lean_internal_panic("#universes mismatch at instantiateTypeLevelParams");
    if (is_nil(ls) || !has_param_univ(info.get_type()))
        return info.get_type();
    return instantiate_lparams_cached(info.get_type(), info.get_lparams(), ls);
}

expr instantiate_value_lparams(constant_info const & info, levels const & ls) {
    if (info.get_num_lparams() != length(ls))
        lean_internal_panic("#universes mismatch at instantiateValueLevelParams");
    if (!info.has_value())
        lean_internal_panic("definition/theorem expected at instantiateValueLevelParams");
    if (is_nil(ls) || !has_param_univ(info.get_value()))
        return info.get_value();
    return instantiate_lparams_cached(info.get_value(), info.get_lparams(), ls);
}

}
