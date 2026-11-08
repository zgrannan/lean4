/*
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include "runtime/sharecommon.h"
#include "runtime/hash.h"

namespace lean {

extern "C" LEAN_EXPORT uint8 lean_sharecommon_eq(b_obj_arg o1, b_obj_arg o2) {
    lean_assert(!lean_is_scalar(o1));
    lean_assert(!lean_is_scalar(o2));
    size_t sz1 = lean_object_data_byte_size(o1);
    size_t sz2 = lean_object_data_byte_size(o2);
    if (sz1 != sz2) return false;
    // compare relevant parts of the header
    uint8_t tag = lean_ptr_tag(o1);
    if (tag != lean_ptr_tag(o2)) return false;
    if (lean_ptr_other(o1) != lean_ptr_other(o2)) return false;
    if (tag == LeanMPZ) {
        return mpz_value(o1) == mpz_value(o2);
    } else {
        size_t header_sz = sizeof(lean_object);
        lean_assert(sz1 >= header_sz);
        // compare objects' bodies
        return memcmp(reinterpret_cast<char*>(o1) + header_sz, reinterpret_cast<char*>(o2) + header_sz, sz1 - header_sz) == 0;
    }
}

extern "C" LEAN_EXPORT uint64_t lean_sharecommon_hash(b_obj_arg o) {
    lean_assert(!lean_is_scalar(o));
    size_t sz = lean_object_data_byte_size(o);
    size_t header_sz = sizeof(lean_object);
    uint8_t tag = lean_ptr_tag(o);
    if (tag == LeanMPZ) {
        return hash(tag, mpz_value(o).hash());
    } else {
        // hash relevant parts of the header
        unsigned init = hash(tag, lean_ptr_other(o));
        // hash body
        return hash_str(sz - header_sz, reinterpret_cast<unsigned char const *>(o) + header_sz, init);
    }
}

static obj_res mk_pair(obj_arg a, obj_arg b) {
    object * r = alloc_cnstr(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, b);
    // std::cout << "mk_pair " << a << " " << b << std::endl;
    return r;
}

class sharecommon_state {
protected:
    object * m_map_find;
    object * m_map_insert;
    object * m_set_find;
    object * m_set_insert;
    object * m_map;
    object * m_set;
public:
    sharecommon_state(b_obj_arg tc, obj_arg s) {
        m_map_find   = lean_ctor_get(tc, 1);
        m_map_insert = lean_ctor_get(tc, 2);
        m_set_find   = lean_ctor_get(tc, 3);
        m_set_insert = lean_ctor_get(tc, 4);
        m_map = lean_ctor_get(s, 0); lean_inc(m_map);
        m_set = lean_ctor_get(s, 1); lean_inc(m_set);
        // std::cout << "sharecommon_state " << m_map << " " << m_set << std::endl;
        lean_dec(s);
    }

    ~sharecommon_state() {
        lean_dec(m_map);
        lean_dec(m_set);
    }

    obj_res pack(obj_arg a) {
        obj_res r = mk_pair(a, mk_pair(m_map, m_set));
        m_map = lean_box(0);
        m_set = lean_box(0);
        return r;
    }

    obj_res map_find(b_obj_arg k) {
        lean_inc(m_map_find); lean_inc(m_map); lean_inc(k);
        return lean_apply_2(m_map_find, m_map, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        lean_inc(m_map_insert);
        m_map = lean_apply_3(m_map_insert, m_map, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc(m_set_find); lean_inc(m_set); lean_inc(o);
        return lean_apply_2(m_set_find, m_set, o);
    }

    void set_insert(obj_arg o) {
        lean_inc(m_set_insert);
        m_set = lean_apply_2(m_set_insert, m_set, o);
    }
};

class sharecommon_fn {
    sharecommon_state         m_state;
    std::vector<lean_object*> m_children;
    std::vector<lean_object*> m_todo;

    void clear_children() {
        m_children.clear();
    }

    bool push_child(b_obj_arg a) {
        if (lean_is_scalar(a)) {
            m_children.push_back(a);
            return true;
        }
        switch (lean_ptr_tag(a)) {
        case LeanReserved:
            lean_unreachable();
        // We do not maximize sharing for the following kinds of objects
        case LeanThunk:
        case LeanTask:     case LeanRef:
        case LeanExternal: case LeanClosure:
        case LeanPromise:
            m_children.push_back(a);
            return true;
        default:
            break;
        }

        // Check whether we have already maximized sharing for `a`
        obj_res o = m_state.map_find(a);
        if (o != lean_box(0)) {
            obj_res r = lean_ctor_get(o, 0);
            lean_dec(o);
            // The map still has a reference to `r`
            m_children.push_back(r);
            // std::cout << "cached maximized " << r << "\n";
            return true;
        }

        m_todo.push_back(a);
        return false;
    }

    void save(b_obj_arg a, obj_arg new_a) {
        lean_assert(m_todo.size() > 0);
        lean_assert(m_todo.back() == a);
        m_todo.pop_back();
        obj_res opt_new_r = m_state.set_find(new_a);
        if (opt_new_r != lean_box(0)) {
            lean_dec(new_a); // we already have a maximally shared term equivalent to `new_a`
            new_a = lean_ctor_get(opt_new_r, 0);
            lean_inc(new_a);
            lean_dec(opt_new_r);
            lean_inc(a);
            m_state.map_insert(a, new_a);
            // std::cout << "already maximized " << new_a << "\n";
        } else {
            lean_inc(a);
            lean_inc_n(new_a, 3);
            m_state.set_insert(new_a);        // `new_a` is a new maximally shared term
            m_state.map_insert(a, new_a);     // `new_a` is the maximally shared representation for `a`
            m_state.map_insert(new_a, new_a); // `new_a` is the maximally shared representation for itself
            // std::cout << "new maximized " << new_a << "\n";
        }
    }

    void visit_array(b_obj_arg a) {
        clear_children();
        bool missing_children = false;
        size_t sz = array_size(a);
        for (size_t i = 0; i < sz; i++) {
            if (!push_child(lean_array_get_core(a, i))) {
                missing_children = true;
            }
        }
        if (missing_children)
            return;
        lean_array_object * new_a = (lean_array_object*)lean_alloc_array(sz, sz);
        for (size_t i = 0; i < sz; i++) {
            lean_inc(m_children[i]);
            lean_array_set_core((lean_object*)new_a, i, m_children[i]);
        }
        save(a, (lean_object*)new_a);
    }

    void visit_sarray(b_obj_arg a) {
        size_t sz        = lean_sarray_size(a);
        unsigned elem_sz = lean_sarray_elem_size(a);
        lean_sarray_object * new_a = (lean_sarray_object*)lean_alloc_sarray(elem_sz, sz, sz);
        memcpy(new_a->m_data, lean_to_sarray(a)->m_data, elem_sz*sz);
        save(a, (lean_object*)new_a);
    }

    void visit_string(b_obj_arg a) {
        size_t sz     = lean_string_size(a);
        size_t len    = lean_string_len(a);
        lean_string_object * new_a = (lean_string_object*)lean_alloc_string(sz, sz, len);
        lean_set_st_header((lean_object*)new_a, LeanString, 0);
        new_a->m_size     = sz;
        new_a->m_capacity = sz;
        new_a->m_length   = len;
        memcpy(new_a->m_data, lean_to_string(a)->m_data, sz);
        save(a, (lean_object*)new_a);
    }

    void visit_mpz(b_obj_arg a) {
        object * new_a = alloc_mpz(mpz_value(a));
        save(a, new_a);
    }

    void visit_ctor(b_obj_arg a) {
        clear_children();
        unsigned num_objs  = lean_ctor_num_objs(a);
        bool missing_child = false;
        for (unsigned i = 0; i < num_objs; i++) {
            if (!push_child(lean_ctor_get(a, i))) {
                // std::cout << "missing_child " << a << " #" << i << " := " << lean_ctor_get(a, i) << std::endl;
                missing_child = true;
                lean_assert(m_todo.back() == lean_ctor_get(a, i));
            }
        }
        if (missing_child)
            return;
        unsigned tag           = lean_ptr_tag(a);
        unsigned sz            = lean_object_byte_size(a);
        unsigned scalar_offset = sizeof(lean_object) + num_objs*sizeof(void*);
        unsigned scalar_sz     = sz - scalar_offset;
        lean_object * new_a    = lean_alloc_ctor(tag, num_objs, scalar_sz);
        for (unsigned i = 0; i < num_objs; i++) {
            lean_inc(m_children[i]);
            lean_ctor_set(new_a, i, m_children[i]);
        }
        if (scalar_sz > 0) {
            memcpy(reinterpret_cast<char*>(new_a) + scalar_offset, reinterpret_cast<char*>(a) + scalar_offset, scalar_sz);
        }
        save(a, new_a);
    }

public:
    sharecommon_fn(b_obj_arg tc, obj_arg s):m_state(tc, s) {}

    obj_res operator()(obj_arg a) {
        if (push_child(a)) {
            object * r = m_children.back();
            lean_inc(r);
            lean_dec(a);
            return m_state.pack(r);
        }
        while (!m_todo.empty()) {
            b_obj_arg curr = m_todo.back();
            // std::cout << "visiting " << curr << " " << static_cast<unsigned>(lean_ptr_tag(curr)) << "\n";
            switch (lean_ptr_tag(curr)) {
            case LeanClosure:         lean_unreachable();
            case LeanArray:           visit_array(curr); break;
            case LeanScalarArray:     visit_sarray(curr); break;
            case LeanString:          visit_string(curr); break;
            case LeanMPZ:             visit_mpz(curr); break;
            case LeanThunk:           lean_unreachable();
            case LeanTask:            lean_unreachable();
            case LeanPromise:         lean_unreachable();
            case LeanRef:             lean_unreachable();
            case LeanExternal:        lean_unreachable();
            case LeanReserved:        lean_unreachable();
            default:                  visit_ctor(curr); break;
            }
        }

        obj_res o = m_state.map_find(a);
        lean_assert(o != lean_box(0));
        obj_res r = lean_ctor_get(o, 0);
        lean_inc(r);
        lean_dec(o);
        lean_dec(a);
        return m_state.pack(r);
    }
};

// def State.shareCommon {α} {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ
extern "C" LEAN_EXPORT obj_res lean_state_sharecommon(b_obj_arg tc, obj_arg s, obj_arg a) {
    return sharecommon_fn(tc, s)(a);
}


/*
  We do not increment reference counters when inserting Lean objects at `m_cache` and `m_set`.
  This is correct because
  - The domain of `m_cache` contains only sub-objects of `lean_sharecommon_quick` parameter,
    and we know the object referenced by this parameter will remain alive.
  - The range of `m_cache` contains only new objects that have been maxed shared, and these
    objects will be are sub-objects of the object returned by `lean_sharecommon_quick`.
  - `m_set` is like the range of `m_cache`.
*/

/*
  Takes a reference to an object in the range of `m_cache` or in `m_set`. These are single-threaded
  objects created here, so the sign test of `lean_inc_ref` is skipped. Overflowing the count panics
  instead of wrapping into the sticky range, since further increments here would walk the count back
  out of it.
*/
static inline void inc_st(lean_object * o) {
#if defined(__GNUC__) || defined(__clang__)
    int rc;
    bool overflow = __builtin_add_overflow(lean_internal_get_rc(o), 1, &rc);
    // Storing before the test lets the increment stay a single instruction on the count.
    lean_internal_set_rc(o, rc);
    if (LEAN_UNLIKELY(overflow))
        lean_internal_panic_rc_overflow();
#else
    int rc = lean_internal_get_rc(o);
    if (LEAN_UNLIKELY(rc == INT_MAX))
        lean_internal_panic_rc_overflow();
    lean_internal_set_rc(o, rc + 1);
#endif
}

struct sharecommon_table_pool {
    struct ptr_map_buf {
        sharecommon_quick_fn::flat_ptr_map::slot * slots;
        size_t cap;
        uint32_t * used;
        size_t used_cap;
    };
    struct obj_set_buf {
        sharecommon_quick_fn::flat_obj_set::slot * slots;
        size_t cap;
        uint32_t * used;
        size_t used_cap;
    };
    std::vector<ptr_map_buf> m_map_pool;
    std::vector<obj_set_buf> m_set_pool;

    ~sharecommon_table_pool() {
        for (auto & b : m_map_pool) {
            delete[] b.slots;
            delete[] b.used;
        }
        for (auto & b : m_set_pool) {
            delete[] b.slots;
            delete[] b.used;
        }
    }
};

static thread_local sharecommon_table_pool g_sharecommon_pool;

sharecommon_quick_fn::flat_ptr_map::flat_ptr_map() {
    if (!g_sharecommon_pool.m_map_pool.empty()) {
        auto b = g_sharecommon_pool.m_map_pool.back();
        g_sharecommon_pool.m_map_pool.pop_back();
        m_slots = b.slots;
        m_cap = b.cap;
        m_used = b.used;
        m_used_cap = b.used_cap;
    } else {
        m_cap = 2048;
        m_slots = new slot[m_cap]();
        m_used_cap = 1024;
        m_used = new uint32_t[m_used_cap];
    }
    m_sz = 0;
}

sharecommon_quick_fn::flat_ptr_map::~flat_ptr_map() {
    if (m_sz * 4 < m_cap) {
        for (size_t i = 0; i < m_sz; ++i) {
            m_slots[m_used[i]].key = nullptr;
        }
    } else {
        memset(m_slots, 0, m_cap * sizeof(slot));
    }
    if (m_cap <= 262144 && g_sharecommon_pool.m_map_pool.size() < 8) {
        g_sharecommon_pool.m_map_pool.push_back({m_slots, m_cap, m_used, m_used_cap});
    } else {
        delete[] m_slots;
        delete[] m_used;
    }
}

inline lean_object * sharecommon_quick_fn::flat_ptr_map::find(lean_object * k) const {
    size_t mask = m_cap - 1;
    size_t idx = (((uintptr_t)k >> 3) * 11400714819323198485ULL >> 32) & mask;
    while (true) {
        slot const & s = m_slots[idx];
        if (!s.key) return nullptr;
        if (s.key == k) return s.val;
        idx = (idx + 1) & mask;
    }
}

void sharecommon_quick_fn::flat_ptr_map::grow() {
    size_t new_cap = m_cap * 2;
    slot * new_slots = new slot[new_cap]();
    size_t new_used_cap = new_cap / 2;
    uint32_t * new_used = new uint32_t[new_used_cap];
    size_t mask = new_cap - 1;
    for (size_t i = 0; i < m_sz; ++i) {
        slot const & old_s = m_slots[m_used[i]];
        size_t idx = (((uintptr_t)old_s.key >> 3) * 11400714819323198485ULL >> 32) & mask;
        while (new_slots[idx].key) {
            idx = (idx + 1) & mask;
        }
        new_slots[idx] = old_s;
        new_used[i] = static_cast<uint32_t>(idx);
    }
    delete[] m_slots;
    delete[] m_used;
    m_slots = new_slots;
    m_cap = new_cap;
    m_used = new_used;
    m_used_cap = new_used_cap;
}

inline void sharecommon_quick_fn::flat_ptr_map::insert(lean_object * k, lean_object * v) {
    if (LEAN_UNLIKELY((m_sz + 1) * 2 >= m_cap)) {
        grow();
    }
    size_t mask = m_cap - 1;
    size_t idx = (((uintptr_t)k >> 3) * 11400714819323198485ULL >> 32) & mask;
    while (true) {
        slot & s = m_slots[idx];
        if (!s.key) {
            s.key = k;
            s.val = v;
            m_used[m_sz++] = static_cast<uint32_t>(idx);
            return;
        }
        if (s.key == k) {
            s.val = v;
            return;
        }
        idx = (idx + 1) & mask;
    }
}

sharecommon_quick_fn::flat_obj_set::flat_obj_set() {
    if (!g_sharecommon_pool.m_set_pool.empty()) {
        auto b = g_sharecommon_pool.m_set_pool.back();
        g_sharecommon_pool.m_set_pool.pop_back();
        m_slots = b.slots;
        m_cap = b.cap;
        m_used = b.used;
        m_used_cap = b.used_cap;
    } else {
        m_cap = 2048;
        m_slots = new slot[m_cap]();
        m_used_cap = 1024;
        m_used = new uint32_t[m_used_cap];
    }
    m_sz = 0;
}

sharecommon_quick_fn::flat_obj_set::~flat_obj_set() {
    if (m_sz * 4 < m_cap) {
        for (size_t i = 0; i < m_sz; ++i) {
            m_slots[m_used[i]].obj = nullptr;
        }
    } else {
        memset(m_slots, 0, m_cap * sizeof(slot));
    }
    if (m_cap <= 262144 && g_sharecommon_pool.m_set_pool.size() < 8) {
        g_sharecommon_pool.m_set_pool.push_back({m_slots, m_cap, m_used, m_used_cap});
    } else {
        delete[] m_slots;
        delete[] m_used;
    }
}

inline lean_object * sharecommon_quick_fn::flat_obj_set::find_with_hash(lean_object * o, uint32_t h) const {
    size_t mask = m_cap - 1;
    size_t idx = h & mask;
    while (true) {
        slot const & s = m_slots[idx];
        if (!s.obj) return nullptr;
        if (s.hash == h && (s.obj == o || lean_sharecommon_eq(s.obj, o))) {
            return s.obj;
        }
        idx = (idx + 1) & mask;
    }
}

inline lean_object * sharecommon_quick_fn::flat_obj_set::find(lean_object * o) const {
    return find_with_hash(o, static_cast<uint32_t>(lean_sharecommon_hash(o)));
}

void sharecommon_quick_fn::flat_obj_set::grow() {
    size_t new_cap = m_cap * 2;
    slot * new_slots = new slot[new_cap]();
    size_t new_used_cap = new_cap / 2;
    uint32_t * new_used = new uint32_t[new_used_cap];
    size_t mask = new_cap - 1;
    for (size_t i = 0; i < m_sz; ++i) {
        slot const & old_s = m_slots[m_used[i]];
        size_t idx = old_s.hash & mask;
        while (new_slots[idx].obj) {
            idx = (idx + 1) & mask;
        }
        new_slots[idx] = old_s;
        new_used[i] = static_cast<uint32_t>(idx);
    }
    delete[] m_slots;
    delete[] m_used;
    m_slots = new_slots;
    m_cap = new_cap;
    m_used = new_used;
    m_used_cap = new_used_cap;
}

inline void sharecommon_quick_fn::flat_obj_set::insert_with_hash(lean_object * o, uint32_t h) {
    if (LEAN_UNLIKELY((m_sz + 1) * 2 >= m_cap)) {
        grow();
    }
    size_t mask = m_cap - 1;
    size_t idx = h & mask;
    while (m_slots[idx].obj) {
        idx = (idx + 1) & mask;
    }
    m_slots[idx].obj = o;
    m_slots[idx].hash = h;
    m_used[m_sz++] = static_cast<uint32_t>(idx);
}

inline void sharecommon_quick_fn::flat_obj_set::insert(lean_object * o) {
    insert_with_hash(o, static_cast<uint32_t>(lean_sharecommon_hash(o)));
}

lean_object * sharecommon_quick_fn::check_cache(lean_object * a) {
    if (!lean_is_exclusive(a)) {
        // We only check the cache if `a` is a shared object
        if (lean_object * r = m_cache.find(a)) {
            // All objects stored in the range of `m_cache` are single threaded.
            lean_assert(lean_is_st(r));
            // We increment the reference counter because this object
            // will be returned by `lean_sharecommon_quick` or stored into a new object.
            inc_st(r);
            return r;
        }
        if (m_check_set) {
            if (lean_object * result = m_set.find(a)) {
                lean_assert(lean_is_st(result));
                inc_st(result);
                return result;
            }
        }
    }
    return nullptr;
}

/*
  `new_a` is a new object that is equal to `a`, but its subobjects are maximally shared.
*/
lean_object * sharecommon_quick_fn::save(lean_object * a, lean_object * new_a) {
    lean_assert(lean_is_st(new_a));
    lean_assert(lean_internal_get_rc(new_a) == 1);
    uint32_t h = static_cast<uint32_t>(lean_sharecommon_hash(new_a));
    lean_object * existing = m_set.find_with_hash(new_a, h);
    lean_object * result;
    if (existing == nullptr) {
        // `new_a` is a new object
        m_set.insert_with_hash(new_a, h);
        result = new_a;
    } else {
        // We already have a maximally shared object that is equal to `new_a`
        result = existing;
        DEBUG_CODE({
                if (lean_is_ctor(new_a)) {
                    lean_assert(lean_is_ctor(result));
                    unsigned num_objs = lean_ctor_num_objs(new_a);
                    lean_assert(lean_ctor_num_objs(result) == num_objs);
                    for (unsigned i = 0; i < num_objs; i++) {
                        lean_assert(lean_ctor_get(result, i) == lean_ctor_get(new_a, i));
                    }
                }
            });
        lean_dec_ref(new_a); // delete `new_a`
        // All objects in `m_set` are single threaded.
        lean_assert(lean_is_st(result));
        inc_st(result);
        lean_assert(lean_internal_get_rc(result) > 1);
    }
    if (!lean_is_exclusive(a)) {
        // We only cache the result if `a` is a shared object.
        m_cache.insert(a, result);
    }
    lean_assert(result == new_a || lean_internal_get_rc(result) > 1);
    lean_assert(result != new_a || lean_internal_get_rc(result) == 1);
    return result;
}

// `sarray` and `string`
lean_object * sharecommon_quick_fn::visit_terminal(lean_object * a) {
    uint32_t h = static_cast<uint32_t>(lean_sharecommon_hash(a));
    if (lean_object * existing = m_set.find_with_hash(a, h)) {
        a = existing;
    } else {
        m_set.insert_with_hash(a, h);
    }
    lean_inc_ref(a);
    return a;
}

lean_object * sharecommon_quick_fn::visit_array(lean_object * a) {
    lean_object * r = check_cache(a);
    if (r != nullptr) { lean_assert(lean_internal_get_rc(r) > 1); return r; }

    size_t sz = array_size(a);
    lean_array_object * new_a = (lean_array_object*)lean_alloc_array(sz, sz);
    for (size_t i = 0; i < sz; i++) {
        lean_array_set_core((lean_object*)new_a, i, visit(lean_array_get_core(a, i)));
    }
    return save(a, (lean_object*)new_a);
}

lean_object * sharecommon_quick_fn::visit_ctor(lean_object * a) {
    lean_object * r = check_cache(a);
    if (r != nullptr) { lean_assert(lean_internal_get_rc(r) > 1); return r; }
    unsigned num_objs      = lean_ctor_num_objs(a);
    unsigned tag           = lean_ptr_tag(a);
    unsigned sz            = lean_object_byte_size(a);
    unsigned scalar_offset = sizeof(lean_object) + num_objs*sizeof(void*);
    unsigned scalar_sz     = sz - scalar_offset;
    if (LEAN_LIKELY(sz <= 64)) {
        alignas(8) char tmp_buf[64];
        lean_object * tmp = reinterpret_cast<lean_object *>(tmp_buf);
        lean_set_non_heap_header(tmp, sz, tag, num_objs);
        for (unsigned i = 0; i < num_objs; i++) {
            lean_ctor_set(tmp, i, visit(lean_ctor_get(a, i)));
        }
        if (scalar_sz > 0) {
            memcpy(tmp_buf + scalar_offset, reinterpret_cast<char const *>(a) + scalar_offset, scalar_sz);
        }
        uint32_t h = static_cast<uint32_t>(lean_sharecommon_hash(tmp));
        if (lean_object * existing = m_set.find_with_hash(tmp, h)) {
            for (unsigned i = 0; i < num_objs; i++) {
                lean_dec(lean_ctor_get(tmp, i));
            }
            inc_st(existing);
            if (!lean_is_exclusive(a)) {
                m_cache.insert(a, existing);
            }
            return existing;
        }
        lean_object * new_a = lean_alloc_small_object(sz);
        lean_set_st_header(new_a, tag, num_objs);
        memcpy(reinterpret_cast<char *>(new_a) + sizeof(lean_object), tmp_buf + sizeof(lean_object), sz - sizeof(lean_object));
        m_set.insert_with_hash(new_a, h);
        if (!lean_is_exclusive(a)) {
            m_cache.insert(a, new_a);
        }
        return new_a;
    }
    lean_object * new_a    = lean_alloc_ctor(tag, num_objs, scalar_sz);
    for (unsigned i = 0; i < num_objs; i++) {
        lean_ctor_set(new_a, i, visit(lean_ctor_get(a, i)));
    }
    if (scalar_sz > 0) {
        memcpy(reinterpret_cast<char*>(new_a) + scalar_offset, reinterpret_cast<char*>(a) + scalar_offset, scalar_sz);
    }
    return save(a, new_a);
}

/*
**TODO:** We did not implement stack overflow detection.
We claim it is not needed in the current uses of `shareCommon'`.
If this becomes an issue, we can use the following approach to address the issue without
affecting the performance.
- Add an extra `depth` parameter.
- In `operator()`, estimate the maximum depth based on the remaining stack space. See `check_stack`.
- If the limit is reached, simply return `a`.
*/
lean_object * sharecommon_quick_fn::visit(lean_object * a) {
    if (lean_is_scalar(a)) {
        return a;
    }
    switch (lean_ptr_tag(a)) {
    /*
      Similarly to `sharecommon_fn`, we only maximally share arrays, scalar arrays, strings, and
      constructor objects.
    */
    case LeanClosure:         lean_inc_ref(a); return a;
    case LeanThunk:           lean_inc_ref(a); return a;
    case LeanTask:            lean_inc_ref(a); return a;
    case LeanPromise:         lean_inc_ref(a); return a;
    case LeanRef:             lean_inc_ref(a); return a;
    case LeanExternal:        lean_inc_ref(a); return a;
    case LeanReserved:        lean_inc_ref(a); return a;
    case LeanMPZ:             return visit_terminal(a);
    case LeanScalarArray:     return visit_terminal(a);
    case LeanString:          return visit_terminal(a);
    case LeanArray:           return visit_array(a);
    default:                  return visit_ctor(a);
    }
}

// def ShareCommon.shareCommon' (a : A) : A := a
extern "C" LEAN_EXPORT obj_res lean_sharecommon_quick(obj_arg a) {
    return sharecommon_quick_fn()(a);
}

lean_object * sharecommon_persistent_fn::operator()(lean_object * e) {
    lean_object * r = check_cache(e);
    if (r != nullptr)
        return r;
    m_saved.push_back(object_ref(e, true));
    r = visit(e);
    m_saved.push_back(object_ref(r, true));
    return r;
}
};
