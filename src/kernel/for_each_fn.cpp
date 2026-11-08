/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <cstring>
#include <unordered_map>
#include <utility>
#include "runtime/memory.h"
#include "runtime/interrupt.h"
#include "runtime/flet.h"
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
    uint32_t m_epoch = 1;
    uint32_t m_depth = 0;

    for_each_cache() {
        std::memset(m_slots, 0, sizeof(m_slots));
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
template<bool partial_apps> class for_each_fn {
    uint32_t m_epoch = 0;
    std::function<bool(expr const &)> m_f; // NOLINT

    bool visited(expr const & e) {
        if (is_likely_unshared(e)) return false;
        if (m_epoch == 0) m_epoch = g_for_each_cache.enter();
        return g_for_each_cache.check_and_insert(e.raw(), 0, m_epoch);
    }

    void apply_fn(expr const & e) {
        if (is_app(e)) {
            apply_fn(app_fn(e));
            apply(app_arg(e));
        } else {
            apply(e);
        }
    }

    void apply(expr const & e) {
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
            apply(app_arg(e));
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e));
            apply(binding_body(e));
            return;
        case expr_kind::Let:
            apply(let_type(e));
            apply(let_value(e));
            apply(let_body(e));
            return;
        }
    }

public:
    for_each_fn(std::function<bool(expr const &)> && f):m_f(f) {}        // NOLINT
    for_each_fn(std::function<bool(expr const &)> const & f):m_f(f) {}   // NOLINT
    ~for_each_fn() {
        if (m_epoch != 0) g_for_each_cache.leave();
    }
    void operator()(expr const & e) { apply(e); }
};

class for_each_offset_fn {
    uint32_t m_epoch = 0;
    std::function<bool(expr const &, unsigned)> m_f; // NOLINT

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
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> && f):m_f(f) {}        // NOLINT
    for_each_offset_fn(std::function<bool(expr const &, unsigned)> const & f):m_f(f) {}   // NOLINT
    ~for_each_offset_fn() {
        if (m_epoch != 0) g_for_each_cache.leave();
    }
    void operator()(expr const & e) { apply(e, 0); }
};

void for_each(expr const & e, std::function<bool(expr const &)> && f) { // NOLINT
    return for_each_fn<true>(f)(e);
}

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    return for_each_offset_fn(f)(e);
}

extern "C" LEAN_EXPORT obj_res lean_find_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    for_each_fn<true>([&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        if (lean_unbox(lean_apply_1(p, e.raw()))) {
            found = e.raw();
            return false;
        }
        return true;
    })(e);
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
    expr const & e = TO_REF(expr, e_);
    // Recall that `findExt?` skips partial applications.
    for_each_fn<false>([&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        switch(lean_unbox(lean_apply_1(p, e.raw()))) {
        case 0: // found
            found = e.raw();
            return false;
        case 1: // visit
            return true;
        case 2: // done
            return false;
        default:
            lean_unreachable();
        }
    })(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}
}
