/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <vector>
#include <cstring>
#include "util/alloc.h"
#include "kernel/expr.h"

namespace lean {
// Maps based on structural equality. That is, two keys are equal iff they are structurally equal
template<typename T>
using expr_map = typename lean::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;

struct expr_pair_slot {
    lean_object * first;
    lean_object * second;
};

struct flat_expr_table_pool {
    static constexpr unsigned NUM_CLASSES = 16; // class 0 = 128, class 15 = 4M
    std::vector<expr_pair_slot *>      m_free_slots[NUM_CLASSES];
    std::vector<std::vector<uint32_t>> m_free_used;

    ~flat_expr_table_pool() {
        for (unsigned c = 0; c < NUM_CLASSES; ++c) {
            for (expr_pair_slot * p : m_free_slots[c]) {
                delete[] p;
            }
        }
    }

    expr_pair_slot * alloc_slots(unsigned sz_class) {
        if (sz_class < NUM_CLASSES && !m_free_slots[sz_class].empty()) {
            expr_pair_slot * p = m_free_slots[sz_class].back();
            m_free_slots[sz_class].pop_back();
            return p;
        }
        size_t cap = static_cast<size_t>(128) << sz_class;
        expr_pair_slot * p = new expr_pair_slot[cap];
        std::memset(p, 0, cap * sizeof(expr_pair_slot));
        return p;
    }

    void free_slots(unsigned sz_class, expr_pair_slot * p) {
        if (sz_class < NUM_CLASSES && m_free_slots[sz_class].size() < 16) {
            m_free_slots[sz_class].push_back(p);
        } else {
            delete[] p;
        }
    }

    std::vector<uint32_t> alloc_used() {
        if (!m_free_used.empty()) {
            std::vector<uint32_t> v = std::move(m_free_used.back());
            m_free_used.pop_back();
            return v;
        }
        std::vector<uint32_t> v;
        v.reserve(64);
        return v;
    }

    void free_used(std::vector<uint32_t> && v) {
        v.clear();
        if (m_free_used.size() < 32) {
            m_free_used.push_back(std::move(v));
        }
    }
};

flat_expr_table_pool & get_thread_expr_table_pool();

class flat_expr_map {
    expr_pair_slot *      m_slots = nullptr;
    size_t                m_mask = 0;
    unsigned              m_size_class = 0;
    std::vector<uint32_t> m_used;

    void init_table() {
        auto & pool = get_thread_expr_table_pool();
        m_size_class = 0;
        m_mask = 127;
        m_slots = pool.alloc_slots(0);
        m_used = pool.alloc_used();
    }

    void grow() {
        auto & pool = get_thread_expr_table_pool();
        unsigned new_class = m_size_class + 1;
        size_t new_cap = static_cast<size_t>(128) << new_class;
        size_t new_mask = new_cap - 1;
        expr_pair_slot * new_slots = pool.alloc_slots(new_class);
        for (uint32_t & idx_ref : m_used) {
            uint32_t old_idx = idx_ref;
            lean_object * k = m_slots[old_idx].first;
            lean_object * v = m_slots[old_idx].second;
            m_slots[old_idx].first = nullptr;
            size_t pos = hash(TO_REF(expr, k)) & new_mask;
            while (new_slots[pos].first != nullptr) {
                pos = (pos + 1) & new_mask;
            }
            new_slots[pos].first  = k;
            new_slots[pos].second = v;
            idx_ref = static_cast<uint32_t>(pos);
        }
        pool.free_slots(m_size_class, m_slots);
        m_slots = new_slots;
        m_mask = new_mask;
        m_size_class = new_class;
    }

public:
    flat_expr_map() = default;
    flat_expr_map(flat_expr_map const &) = delete;
    flat_expr_map & operator=(flat_expr_map const &) = delete;
    ~flat_expr_map() {
        if (m_slots) {
            for (uint32_t idx : m_used) {
                lean_dec(m_slots[idx].first);
                lean_dec(m_slots[idx].second);
                m_slots[idx].first = nullptr;
            }
            auto & pool = get_thread_expr_table_pool();
            pool.free_slots(m_size_class, m_slots);
            pool.free_used(std::move(m_used));
        }
    }

    lean_object * find(expr const & k) const {
        if (!m_slots) return nullptr;
        unsigned h = hash(k);
        size_t idx = h & m_mask;
        while (true) {
            lean_object * fk = m_slots[idx].first;
            if (!fk) return nullptr;
            if (fk == k.raw() || (hash(TO_REF(expr, fk)) == h && is_equal(TO_REF(expr, fk), k))) {
                return m_slots[idx].second;
            }
            idx = (idx + 1) & m_mask;
        }
    }

    void insert(expr const & k, expr const & v) {
        if (!m_slots) {
            init_table();
        } else if (m_used.size() * 2 >= m_mask + 1) {
            grow();
        }
        unsigned h = hash(k);
        size_t idx = h & m_mask;
        while (true) {
            lean_object * fk = m_slots[idx].first;
            if (!fk) {
                lean_inc(k.raw());
                lean_inc(v.raw());
                m_slots[idx].first  = k.raw();
                m_slots[idx].second = v.raw();
                m_used.push_back(static_cast<uint32_t>(idx));
                return;
            }
            if (fk == k.raw() || (hash(TO_REF(expr, fk)) == h && is_equal(TO_REF(expr, fk), k))) {
                return;
            }
            idx = (idx + 1) & m_mask;
        }
    }
};

class flat_expr_pair_set {
    expr_pair_slot *      m_slots = nullptr;
    size_t                m_mask = 0;
    unsigned              m_size_class = 0;
    std::vector<uint32_t> m_used;

    void init_table() {
        auto & pool = get_thread_expr_table_pool();
        m_size_class = 0;
        m_mask = 127;
        m_slots = pool.alloc_slots(0);
        m_used = pool.alloc_used();
    }

    void grow() {
        auto & pool = get_thread_expr_table_pool();
        unsigned new_class = m_size_class + 1;
        size_t new_cap = static_cast<size_t>(128) << new_class;
        size_t new_mask = new_cap - 1;
        expr_pair_slot * new_slots = pool.alloc_slots(new_class);
        for (uint32_t & idx_ref : m_used) {
            uint32_t old_idx = idx_ref;
            lean_object * a = m_slots[old_idx].first;
            lean_object * b = m_slots[old_idx].second;
            m_slots[old_idx].first = nullptr;
            size_t pos = hash(hash(TO_REF(expr, a)), hash(TO_REF(expr, b))) & new_mask;
            while (new_slots[pos].first != nullptr) {
                pos = (pos + 1) & new_mask;
            }
            new_slots[pos].first  = a;
            new_slots[pos].second = b;
            idx_ref = static_cast<uint32_t>(pos);
        }
        pool.free_slots(m_size_class, m_slots);
        m_slots = new_slots;
        m_mask = new_mask;
        m_size_class = new_class;
    }

public:
    flat_expr_pair_set() = default;
    flat_expr_pair_set(flat_expr_pair_set const &) = delete;
    flat_expr_pair_set & operator=(flat_expr_pair_set const &) = delete;
    ~flat_expr_pair_set() {
        if (m_slots) {
            for (uint32_t idx : m_used) {
                lean_dec(m_slots[idx].first);
                lean_dec(m_slots[idx].second);
                m_slots[idx].first = nullptr;
            }
            auto & pool = get_thread_expr_table_pool();
            pool.free_slots(m_size_class, m_slots);
            pool.free_used(std::move(m_used));
        }
    }

    bool contains(expr const & a, expr const & b) const {
        if (!m_slots) return false;
        unsigned ha = hash(a);
        unsigned hb = hash(b);
        unsigned h  = hash(ha, hb);
        size_t idx  = h & m_mask;
        while (true) {
            lean_object * fa = m_slots[idx].first;
            if (!fa) return false;
            lean_object * fb = m_slots[idx].second;
            if ((fa == a.raw() || (hash(TO_REF(expr, fa)) == ha && is_equal(TO_REF(expr, fa), a))) &&
                (fb == b.raw() || (hash(TO_REF(expr, fb)) == hb && is_equal(TO_REF(expr, fb), b)))) {
                return true;
            }
            idx = (idx + 1) & m_mask;
        }
    }

    void insert(expr const & a, expr const & b) {
        if (!m_slots) {
            init_table();
        } else if (m_used.size() * 2 >= m_mask + 1) {
            grow();
        }
        unsigned ha = hash(a);
        unsigned hb = hash(b);
        unsigned h  = hash(ha, hb);
        size_t idx  = h & m_mask;
        while (true) {
            lean_object * fa = m_slots[idx].first;
            if (!fa) {
                lean_inc(a.raw());
                lean_inc(b.raw());
                m_slots[idx].first  = a.raw();
                m_slots[idx].second = b.raw();
                m_used.push_back(static_cast<uint32_t>(idx));
                return;
            }
            lean_object * fb = m_slots[idx].second;
            if ((fa == a.raw() || (hash(TO_REF(expr, fa)) == ha && is_equal(TO_REF(expr, fa), a))) &&
                (fb == b.raw() || (hash(TO_REF(expr, fb)) == hb && is_equal(TO_REF(expr, fb), b)))) {
                return;
            }
            idx = (idx + 1) & m_mask;
        }
    }
};
};
