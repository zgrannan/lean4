/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <cstring>
#include <memory>
#include <unordered_map>
#include <utility>
#include "runtime/memory.h"
#include "runtime/interrupt.h"
#include "runtime/flet.h"
#include "util/name_set.h"
#include "kernel/for_each_fn.h"

namespace lean {

struct for_each_cache {
    static constexpr size_t CAPACITY = 16384;
    static constexpr size_t MASK = CAPACITY - 1;
    struct slot {
        lean_object * key;
        uint32_t      offset;
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

    bool check_and_insert(lean_object * key, uint32_t offset, uint32_t my_epoch) {
        size_t idx = static_cast<size_t>(hash(static_cast<unsigned>((uintptr_t)key >> 3), offset)) & MASK;
        unsigned insert_pos = 3;
        for (unsigned i = 0; i < 4; ++i) {
            slot const & s = m_slots[(idx + i) & MASK];
            if (s.epoch == my_epoch) {
                if (s.key == key && s.offset == offset)
                    return true;
            } else {
                if (insert_pos == 3)
                    insert_pos = i;
                if (s.epoch < my_epoch)
                    break;
            }
        }
        slot & dst = m_slots[(idx + insert_pos) & MASK];
        dst.key    = key;
        dst.offset = offset;
        dst.epoch  = my_epoch;
        return false;
    }
};

static thread_local for_each_cache g_for_each_cache;

/*
If `partial_apps = true`, then given a term `g a b`, we also apply the function `m_f` to `g a`,
and not only to `g`, `a`, and `b`.
*/
template<bool partial_apps, typename F> class for_each_fn {
    uint32_t m_epoch = 0;
    bool     m_default_done = false;
    bool &   m_done;
    F        m_f;

    bool visited(expr const & e) {
        if (is_likely_unshared(e)) return false;
        if (m_epoch == 0) m_epoch = g_for_each_cache.enter();
        return g_for_each_cache.check_and_insert(e.raw(), 0, m_epoch);
    }

    void apply_fn(expr const & e) {
        if (LEAN_UNLIKELY(m_done)) return;
        if (is_app(e)) {
            apply_fn(app_fn(e));
            if (LEAN_UNLIKELY(m_done)) return;
            apply(app_arg(e));
        } else {
            apply(e);
        }
    }

    void apply(expr const & e) {
        if (LEAN_UNLIKELY(m_done)) return;
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e);
            return;
        default:
            break;
        }

        if (visited(e))
            return;

        if (!m_f(e))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e));
            return;
        case expr_kind::Proj:
            apply(proj_expr(e));
            return;
        case expr_kind::App:
            if (partial_apps)
                apply(app_fn(e));
            else
                apply_fn(app_fn(e));
            if (LEAN_UNLIKELY(m_done)) return;
            apply(app_arg(e));
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e));
            if (LEAN_UNLIKELY(m_done)) return;
            apply(binding_body(e));
            return;
        case expr_kind::Let:
            apply(let_type(e));
            if (LEAN_UNLIKELY(m_done)) return;
            apply(let_value(e));
            if (LEAN_UNLIKELY(m_done)) return;
            apply(let_body(e));
            return;
        }
    }

public:
    for_each_fn(F && f):m_done(m_default_done), m_f(std::forward<F>(f)) {}
    for_each_fn(F && f, bool & done):m_done(done), m_f(std::forward<F>(f)) {}
    ~for_each_fn() {
        if (m_epoch != 0) g_for_each_cache.leave();
    }
    void operator()(expr const & e) { apply(e); }
};

template<typename F> class for_each_offset_fn {
    uint32_t m_epoch = 0;
    F        m_f;

    bool visited(expr const & e, unsigned offset) {
        if (is_likely_unshared(e)) return false;
        if (m_epoch == 0) m_epoch = g_for_each_cache.enter();
        return g_for_each_cache.check_and_insert(e.raw(), offset, m_epoch);
    }

    void apply(expr const & e, unsigned offset) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e, offset);
            return;
        default:
            break;
        }

        if (visited(e, offset))
            return;

        if (!m_f(e, offset))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e), offset);
            return;
        case expr_kind::Proj:
            apply(proj_expr(e), offset);
            return;
        case expr_kind::App:
            apply(app_fn(e), offset);
            apply(app_arg(e), offset);
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e), offset);
            apply(binding_body(e), offset+1);
            return;
        case expr_kind::Let:
            apply(let_type(e), offset);
            apply(let_value(e), offset);
            apply(let_body(e), offset+1);
            return;
        }
    }

public:
    for_each_offset_fn(F && f):m_f(std::forward<F>(f)) {}
    ~for_each_offset_fn() {
        if (m_epoch != 0) g_for_each_cache.leave();
    }
    void operator()(expr const & e) { apply(e, 0); }
};

void for_each(expr const & e, std::function<bool(expr const &)> && f) { // NOLINT
    return for_each_fn<true, std::function<bool(expr const &)> &>(f)(e);
}

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    return for_each_offset_fn<std::function<bool(expr const &, unsigned)> &>(f)(e);
}

extern "C" LEAN_EXPORT obj_res lean_find_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    bool done = false;
    expr const & e = TO_REF(expr, e_);
    auto cb = [&](expr const & e) -> bool {
        if (done) return false;
        lean_inc(p);
        lean_inc(e.raw());
        if (lean_unbox(lean_apply_1(p, e.raw()))) {
            found = e.raw();
            done = true;
            return false;
        }
        return true;
    };
    for_each_fn<true, decltype(cb) &>(cb, done)(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

/*
Similar to `lean_find_expr`, but `p` returns
```
inductive FindStep where
  /-- Found desired subterm -/ | found
  /-- Search subterms -/ | visit
  /-- Do not search subterms -/ | done
```
*/
extern "C" LEAN_EXPORT obj_res lean_find_ext_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    bool done = false;
    expr const & e = TO_REF(expr, e_);
    // Recall that `findExt?` skips partial applications.
    auto cb = [&](expr const & e) -> bool {
        if (done) return false;
        lean_inc(p);
        lean_inc(e.raw());
        switch(lean_unbox(lean_apply_1(p, e.raw()))) {
        case 0: // found
            found = e.raw();
            done = true;
            return false;
        case 1: // visit
            return true;
        case 2: // done
            return false;
        default:
            lean_unreachable();
        }
    };
    for_each_fn<false, decltype(cb) &>(cb, done)(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

static name const & get_sorry_ax_name() {
    static name const * g_sorry_ax = []() {
        name * n = new name("sorryAx");
        mark_persistent(n->raw());
        return n;
    }();
    return *g_sorry_ax;
}

extern "C" LEAN_EXPORT uint8 lean_expr_has_sorry(b_obj_arg e_) {
    expr const & root = TO_REF(expr, e_);
    name const & sorry_name = get_sorry_ax_name();
    bool found = false;
    auto cb = [&](expr const & e) -> bool {
        if (is_constant(e)) {
            if (const_name(e) == sorry_name) {
                found = true;
            }
            return false;
        }
        return true;
    };
    for_each_fn<false, decltype(cb) &>(cb, found)(root);
    return found ? 1 : 0;
}

struct fold_consts_cache {
    static constexpr size_t EXPR_CAP = 8192;
    static constexpr size_t EXPR_MASK = EXPR_CAP - 1;
    static constexpr size_t NAME_CAP = 4096;
    static constexpr size_t NAME_MASK = NAME_CAP - 1;
    static constexpr size_t NAME_MAX_LOAD = 3072;

    struct expr_slot {
        lean_object * key;
        uint32_t      epoch;
    };
    struct name_slot {
        lean_object * name;
        uint64_t      hash;
        uint32_t      epoch;
    };

    expr_slot m_expr_slots[EXPR_CAP];
    name_slot m_name_slots[NAME_CAP];
    name_set  m_overflow_names;
    uint32_t  m_epoch = 0;
    uint32_t  m_name_count = 0;
    bool      m_has_overflow = false;
    bool      m_in_use = false;

    void enter() {
        if (LEAN_UNLIKELY(m_epoch > 0xFFFF0000u)) {
            std::memset(m_expr_slots, 0, sizeof(m_expr_slots));
            std::memset(m_name_slots, 0, sizeof(m_name_slots));
            m_epoch = 0;
        }
        ++m_epoch;
        m_name_count = 0;
        m_has_overflow = false;
        m_in_use = true;
    }

    void leave() {
        if (LEAN_UNLIKELY(m_has_overflow)) {
            m_overflow_names = name_set();
            m_has_overflow = false;
        }
        m_in_use = false;
    }

    bool check_and_insert_expr(lean_object * key) {
        size_t idx = static_cast<size_t>((uintptr_t)key >> 3) & EXPR_MASK;
        unsigned insert_pos = 3;
        uint32_t ep = m_epoch;
        for (unsigned i = 0; i < 4; ++i) {
            expr_slot const & s = m_expr_slots[(idx + i) & EXPR_MASK];
            if (s.epoch == ep) {
                if (s.key == key)
                    return true;
            } else {
                if (insert_pos == 3)
                    insert_pos = i;
                if (s.epoch < ep)
                    break;
            }
        }
        expr_slot & dst = m_expr_slots[(idx + insert_pos) & EXPR_MASK];
        dst.key   = key;
        dst.epoch = ep;
        return false;
    }

    bool mark_const_visited(lean_object * c) {
        uint64_t h = lean_name_hash(c);
        size_t idx = static_cast<size_t>(h) & NAME_MASK;
        uint32_t ep = m_epoch;
        for (unsigned probes = 0; probes < 64; ++probes) {
            name_slot & s = m_name_slots[idx];
            if (s.epoch != ep) {
                if (LEAN_UNLIKELY(m_has_overflow)) {
                    name n(c, true);
                    if (m_overflow_names.contains(n))
                        return false;
                }
                if (LEAN_LIKELY(m_name_count < NAME_MAX_LOAD)) {
                    s.name  = c;
                    s.hash  = h;
                    s.epoch = ep;
                    ++m_name_count;
                    return true;
                }
                break;
            }
            if (s.name == c || (s.hash == h && lean_name_eq(s.name, c))) {
                return false;
            }
            idx = (idx + 1) & NAME_MASK;
        }
        name n(c, true);
        if (m_has_overflow && m_overflow_names.contains(n)) {
            return false;
        }
        m_has_overflow = true;
        m_overflow_names.insert(n);
        return true;
    }
};

static thread_local fold_consts_cache g_fold_consts_cache;

class fold_consts_fn {
    fold_consts_cache *                m_cache;
    std::unique_ptr<fold_consts_cache> m_owned_cache;
    lean_object *                      m_acc;
    lean_object *                      m_f;

    void visit_const(lean_object * c) {
        if (m_cache->mark_const_visited(c)) {
            lean_inc(m_f);
            lean_inc(c);
            m_acc = lean_apply_2(m_f, c, m_acc);
        }
    }

    void visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::BVar:
        case expr_kind::FVar:
        case expr_kind::MVar:
        case expr_kind::Sort:
        case expr_kind::Lit:
            return;
        case expr_kind::Const:
            visit_const(const_name(e).raw());
            return;
        default:
            break;
        }
        if (!is_likely_unshared(e) && m_cache->check_and_insert_expr(e.raw()))
            return;
        switch (e.kind()) {
        case expr_kind::MData:
            visit(mdata_expr(e));
            return;
        case expr_kind::Proj:
            visit_const(proj_sname(e).raw());
            visit(proj_expr(e));
            return;
        case expr_kind::App:
            visit(app_fn(e));
            visit(app_arg(e));
            return;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            visit(binding_domain(e));
            visit(binding_body(e));
            return;
        case expr_kind::Let:
            visit(let_type(e));
            visit(let_value(e));
            visit(let_body(e));
            return;
        default:
            return;
        }
    }

public:
    fold_consts_fn(lean_object * init, lean_object * f) : m_acc(init), m_f(f) {
        if (LEAN_LIKELY(!g_fold_consts_cache.m_in_use)) {
            m_cache = &g_fold_consts_cache;
        } else {
            m_owned_cache = std::make_unique<fold_consts_cache>();
            std::memset(m_owned_cache->m_expr_slots, 0, sizeof(m_owned_cache->m_expr_slots));
            std::memset(m_owned_cache->m_name_slots, 0, sizeof(m_owned_cache->m_name_slots));
            m_cache = m_owned_cache.get();
        }
        m_cache->enter();
    }

    ~fold_consts_fn() {
        m_cache->leave();
    }

    lean_object * operator()(expr const & e) {
        visit(e);
        return m_acc;
    }
};

extern "C" LEAN_EXPORT obj_res lean_expr_fold_consts(obj_arg e_obj, obj_arg init, obj_arg f) {
    lean_object * res = fold_consts_fn(init, f)(TO_REF(expr, e_obj));
    lean_dec(e_obj);
    lean_dec(f);
    return res;
}
}
