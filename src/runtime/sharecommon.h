/*
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "runtime/object_ref.h"
#include "util/alloc.h"

namespace lean {
extern "C" LEAN_EXPORT uint8 lean_sharecommon_eq(b_obj_arg o1, b_obj_arg o2);
extern "C" LEAN_EXPORT uint64_t lean_sharecommon_hash(b_obj_arg o);

/*
A faster version of `sharecommon_fn` which only uses a local state.
It optimizes the number of RC operations, the strategy for caching results,
and uses C++ hashmap.
*/
class LEAN_EXPORT sharecommon_quick_fn {
public:
    struct flat_ptr_map {
        struct slot {
            lean_object * key;
            lean_object * val;
        };
        slot *   m_slots;
        size_t   m_cap;
        size_t   m_sz;
        uint32_t * m_used;
        size_t   m_used_cap;

        flat_ptr_map();
        ~flat_ptr_map();
        lean_object * find(lean_object * k) const;
        void insert(lean_object * k, lean_object * v);
        void grow();
    };

    struct flat_obj_set {
        struct slot {
            lean_object * obj;
            uint32_t      hash;
        };
        slot *   m_slots;
        size_t   m_cap;
        size_t   m_sz;
        uint32_t * m_used;
        size_t   m_used_cap;

        flat_obj_set();
        ~flat_obj_set();
        lean_object * find_with_hash(lean_object * o, uint32_t h) const;
        lean_object * find(lean_object * o) const;
        void insert_with_hash(lean_object * o, uint32_t h);
        void insert(lean_object * o);
        void grow();
    };

    /*
    We use `m_cache` to ensure we do **not** traverse a DAG as a tree.
    We use pointer equality for this collection.
    */
    flat_ptr_map m_cache;
    /* Set of maximally shared terms. AKA hash-consing table. */
    flat_obj_set m_set;
    /*
    If `true`, `check_cache` will also check `m_set`.
    This is useful when the input term may contain terms that have already
    been hashconsed.
    */
    bool m_check_set;

    lean_object * check_cache(lean_object * a);
    lean_object * save(lean_object * a, lean_object * new_a);
    lean_object * visit_terminal(lean_object * a);
    lean_object * visit_array(lean_object * a);
    lean_object * visit_ctor(lean_object * a);
    lean_object * visit(lean_object * a);
public:
    sharecommon_quick_fn(bool s = false):m_check_set(s) {}
    void set_check_set(bool f) { m_check_set = f; }
    lean_object * operator()(lean_object * a) {
        return visit(a);
    }
};

/*
Similar to `sharecommon_quick_fn`, but we save the entry points and result values to ensure
they are not deleted.
*/
class LEAN_EXPORT sharecommon_persistent_fn : private sharecommon_quick_fn {
    std::vector<object_ref> m_saved;
public:
    sharecommon_persistent_fn(bool s = false):sharecommon_quick_fn(s) {}
    void set_check_set(bool f) { m_check_set = f; }
    lean_object * operator()(lean_object * e);
};

};
