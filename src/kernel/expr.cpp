/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include <string>
#include <algorithm>
#include <limits>
#include "runtime/hash.h"
#include "runtime/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/expr_sets.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"

namespace lean {
/* Expression literal values */
literal::literal(unsigned v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), mk_nat_obj(v))) {
}

literal::literal(nat const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(literal_kind::Nat), v)) {
}

bool operator==(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return false;
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() == b.get_string();
    case literal_kind::Nat:    return a.get_nat() == b.get_nat();
    }
    lean_unreachable();
}

bool operator<(literal const & a, literal const & b) {
    if (a.kind() != b.kind()) return static_cast<unsigned>(a.kind()) < static_cast<unsigned>(b.kind());
    switch (a.kind()) {
    case literal_kind::String: return a.get_string() < b.get_string();
    case literal_kind::Nat:    return a.get_nat() < b.get_nat();
    }
    lean_unreachable();
}

extern "C" uint8 lean_expr_binder_info(object * e);
binder_info binding_info_core(expr const & e) { return static_cast<binder_info>(lean_expr_binder_info(e.to_obj_arg())); }

extern "C" object * lean_lit_type(obj_arg e);
expr lit_type(literal const & lit) { return expr(lean_lit_type(lit.to_obj_arg())); }

extern "C" uint64_t lean_expr_hash(obj_arg e);
unsigned hash_core(expr const & e) {
    return lean_expr_hash(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_fvar(obj_arg e);
bool has_fvar_core(expr const & e) {
    return lean_expr_has_fvar(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_expr_mvar(obj_arg e);
bool has_expr_mvar_core(expr const & e) {
    return lean_expr_has_expr_mvar(e.to_obj_arg());
}

extern "C" uint8 lean_expr_has_level_mvar(obj_arg e);
bool has_univ_mvar_core(expr const & e) { return lean_expr_has_level_mvar(e.to_obj_arg()); }

extern "C" uint8 lean_expr_has_level_param(obj_arg e);
bool has_univ_param_core(expr const & e) { return lean_expr_has_level_param(e.to_obj_arg()); }

extern "C" unsigned lean_expr_loose_bvar_range(object * e);
unsigned get_loose_bvar_range_core(expr const & e) { return lean_expr_loose_bvar_range(e.to_obj_arg()); }

extern "C" LEAN_EXPORT uint64_t lean_expr_mk_data(uint64_t hash, object * bvarRange, uint32_t approxDepth, uint8_t hasFVar, uint8_t hasExprMVar, uint8_t hasLevelMVar, uint8_t hasLevelParam) {
    if (approxDepth > 255) approxDepth = 255;
    if (!is_scalar(bvarRange)) lean_internal_panic("too many bound variables");
    size_t range = unbox(bvarRange);
    if (range > 1048575) lean_internal_panic("too many bound variables");
    uint32_t r = range;
    uint32_t h = hash;
    return ((uint64_t) h) + (((uint64_t) approxDepth) << 32) + (((uint64_t) hasFVar) << 40)
    + (((uint64_t) hasExprMVar) << 41) + (((uint64_t) hasLevelMVar) << 42) + (((uint64_t) hasLevelParam) << 43)
    + (((uint64_t) r) << 44);
}

inline uint16_t get_approx_depth(uint64_t data) { return (data >> 32) & 255; }
inline uint32_t get_bvar_range(uint64_t data) { return data >> 44; }

extern "C" LEAN_EXPORT uint64_t lean_expr_mk_app_data(uint64_t fData, uint64_t aData) {
  uint16_t depth = std::max(get_approx_depth(fData), get_approx_depth(aData)) + 1;
  if (depth > 255) depth = 255;
  uint32_t range = std::max(get_bvar_range(fData), get_bvar_range(aData));
  uint32_t h = hash(fData, aData);
  return ((fData | aData) & (((uint64_t) 15) << 40)) | ((uint64_t) h) | (((uint64_t) depth) << 32) | (((uint64_t) range) << 44);
}

static inline uint64_t mk_binding_data(uint64_t tData, uint64_t eData) {
    uint32_t d_raw = std::max<uint32_t>(get_approx_depth(tData), get_approx_depth(eData)) + 1;
    uint32_t d = d_raw > 255 ? 255 : d_raw;
    uint32_t b_r = get_bvar_range(eData);
    uint32_t r = std::max<uint32_t>(get_bvar_range(tData), b_r > 0 ? b_r - 1 : 0u);
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(d_raw, lean_uint64_mix_hash(static_cast<uint32_t>(tData), static_cast<uint32_t>(eData))));
    return ((tData | eData) & (15ULL << 40)) | static_cast<uint64_t>(h) | (static_cast<uint64_t>(d) << 32) | (static_cast<uint64_t>(r) << 44);
}

static inline uint64_t mk_let_data(uint64_t tData, uint64_t vData, uint64_t bData) {
    uint32_t d_raw = std::max<uint32_t>({get_approx_depth(tData), get_approx_depth(vData), get_approx_depth(bData)}) + 1;
    uint32_t d = d_raw > 255 ? 255 : d_raw;
    uint32_t b_r = get_bvar_range(bData);
    uint32_t r = std::max<uint32_t>({get_bvar_range(tData), get_bvar_range(vData), b_r > 0 ? b_r - 1 : 0u});
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(d_raw, lean_uint64_mix_hash(static_cast<uint32_t>(tData), lean_uint64_mix_hash(static_cast<uint32_t>(vData), static_cast<uint32_t>(bData)))));
    return ((tData | vData | bData) & (15ULL << 40)) | static_cast<uint64_t>(h) | (static_cast<uint64_t>(d) << 32) | (static_cast<uint64_t>(r) << 44);
}

static inline uint64_t mk_fvar_data(name const & n) {
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(13ULL, n.hash()));
    return static_cast<uint64_t>(h) | (1ULL << 40);
}

static inline uint64_t mk_sort_data(level const & l) {
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(11ULL, l.hash()));
    uint64_t hasLevelMVar = has_mvar(l) ? 1ULL : 0ULL;
    uint64_t hasLevelParam = has_param(l) ? 1ULL : 0ULL;
    return static_cast<uint64_t>(h) | (hasLevelMVar << 42) | (hasLevelParam << 43);
}

static inline uint64_t mk_const_data(name const & n, levels const & ls) {
    uint64_t lh = 7ULL;
    uint64_t hasLevelMVar = 0;
    uint64_t hasLevelParam = 0;
    for (object * it = ls.raw(); !lean_is_scalar(it); it = lean_ctor_get(it, 1)) {
        level const & head = static_cast<level const &>(cnstr_get_ref(it, 0));
        lh = lean_uint64_mix_hash(lh, head.hash());
        if (has_mvar(head)) hasLevelMVar = 1;
        if (has_param(head)) hasLevelParam = 1;
    }
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(5ULL, lean_uint64_mix_hash(n.hash(), lh)));
    return static_cast<uint64_t>(h) | (hasLevelMVar << 42) | (hasLevelParam << 43);
}

static inline uint64_t mk_mdata_data(uint64_t eData) {
    uint32_t d_raw = static_cast<uint32_t>(get_approx_depth(eData)) + 1;
    uint32_t d = d_raw > 255 ? 255 : d_raw;
    uint32_t r = get_bvar_range(eData);
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(d_raw, static_cast<uint32_t>(eData)));
    return (eData & (15ULL << 40)) | static_cast<uint64_t>(h) | (static_cast<uint64_t>(d) << 32) | (static_cast<uint64_t>(r) << 44);
}

static inline uint64_t mk_proj_data(name const & s, nat const & idx, uint64_t eData) {
    uint32_t d_raw = static_cast<uint32_t>(get_approx_depth(eData)) + 1;
    uint32_t d = d_raw > 255 ? 255 : d_raw;
    uint32_t r = get_bvar_range(eData);
    uint64_t idx_u64 = idx.is_small() ? static_cast<uint64_t>(idx.get_small_value()) : lean_uint64_of_nat(idx.raw());
    uint32_t h = static_cast<uint32_t>(lean_uint64_mix_hash(d_raw, lean_uint64_mix_hash(s.hash(), lean_uint64_mix_hash(idx_u64, static_cast<uint32_t>(eData)))));
    return (eData & (15ULL << 40)) | static_cast<uint64_t>(h) | (static_cast<uint64_t>(d) << 32) | (static_cast<uint64_t>(r) << 44);
}

// =======================================
// Kernel Scoped Bump Arena
// =======================================

struct kernel_arena {
    static constexpr size_t SLAB_SIZE = 1u << 20;       // 1 MB per slab
    static constexpr size_t MAX_ARENA_BYTES = 64u << 20; // 64 MB cap per declaration
    static constexpr size_t TRACKED_MASK = 1023;

    struct tracked_entry {
        object * m_ptr = nullptr;
        uint32_t m_epoch = 0;
    };

    std::vector<char *> m_slabs;
    size_t m_curr_slab = 0;
    size_t m_offset = 0;
    size_t m_used_bytes = 0;
    size_t m_peak_bytes = 0;
    size_t m_total_alloc_bytes = 0;
    size_t m_total_scopes = 0;
    unsigned m_depth = 0;
    bool m_active = false;
    bool m_retain_on_exit = false;
    uint32_t m_epoch = 0;
    tracked_entry m_tracked[TRACKED_MASK + 1];
    std::vector<object *> m_heap_refs;
    std::vector<char *> m_retained_slabs;
    std::vector<object *> m_retained_heap_refs;

    ~kernel_arena() {
        if (getenv("LEAN_PRINT_ARENA_STATS") && m_total_scopes > 0) {
            fprintf(stderr, "[kernel_arena] scopes=%zu peak_bytes=%zu (%.2f KB) total_alloc_bytes=%zu (%.2f MB)\n",
                    m_total_scopes, m_peak_bytes, m_peak_bytes / 1024.0,
                    m_total_alloc_bytes, m_total_alloc_bytes / (1024.0 * 1024.0));
        }
        for (object * o : m_heap_refs) lean_dec_ref(o);
        for (object * o : m_retained_heap_refs) lean_dec_ref(o);
        for (char * s : m_slabs) delete[] s;
        for (char * s : m_retained_slabs) delete[] s;
    }

    inline void next_epoch() {
        ++m_epoch;
        if (LEAN_UNLIKELY(m_epoch == 0)) {
            for (size_t i = 0; i <= TRACKED_MASK; ++i) {
                m_tracked[i].m_epoch = 0;
            }
            m_epoch = 1;
        }
    }

    inline object * alloc_ctor(unsigned tag, unsigned num_objs, size_t total_sz) {
        if (LEAN_UNLIKELY(m_used_bytes + total_sz > MAX_ARENA_BYTES)) {
            return nullptr;
        }
        if (LEAN_UNLIKELY(m_slabs.empty())) {
            m_slabs.push_back(new char[SLAB_SIZE]);
            m_curr_slab = 0;
            m_offset = 0;
        }
        if (LEAN_UNLIKELY(m_offset + total_sz > SLAB_SIZE)) {
            ++m_curr_slab;
            if (m_curr_slab >= m_slabs.size()) {
                m_slabs.push_back(new char[SLAB_SIZE]);
            }
            m_offset = 0;
        }
        object * o = reinterpret_cast<object *>(m_slabs[m_curr_slab] + m_offset);
        m_offset += total_sz;
        m_used_bytes += total_sz;
        lean_set_non_heap_header(o, total_sz, tag, num_objs);
        return o;
    }

    inline void track_child(object * c) {
        if (!lean_is_scalar(c) && lean_has_rc(c)) {
            size_t idx = (reinterpret_cast<uintptr_t>(c) >> 3) & TRACKED_MASK;
            if (m_tracked[idx].m_ptr == c && m_tracked[idx].m_epoch == m_epoch && lean_internal_get_rc(c) != 1) {
                return;
            }
            m_tracked[idx].m_ptr = c;
            m_tracked[idx].m_epoch = m_epoch;
            lean_inc_ref(c);
            m_heap_refs.push_back(c);
        }
    }

    bool in_current_slabs(object * o) const {
        if (lean_is_scalar(o) || m_slabs.empty() || m_used_bytes == 0) return false;
        uintptr_t p = reinterpret_cast<uintptr_t>(o);
        for (size_t i = 0; i <= m_curr_slab && i < m_slabs.size(); ++i) {
            uintptr_t base = reinterpret_cast<uintptr_t>(m_slabs[i]);
            if (p >= base && p < base + SLAB_SIZE) return true;
        }
        return false;
    }

    void reset() {
        if (m_used_bytes > m_peak_bytes) {
            m_peak_bytes = m_used_bytes;
        }
        m_total_alloc_bytes += m_used_bytes;
        ++m_total_scopes;
        if (LEAN_UNLIKELY(m_retain_on_exit)) {
            for (size_t i = 0; i <= m_curr_slab && i < m_slabs.size(); ++i) {
                m_retained_slabs.push_back(m_slabs[i]);
            }
            m_slabs.erase(m_slabs.begin(), m_slabs.begin() + std::min(m_curr_slab + 1, m_slabs.size()));
            m_retained_heap_refs.insert(m_retained_heap_refs.end(), m_heap_refs.begin(), m_heap_refs.end());
            m_heap_refs.clear();
            m_retain_on_exit = false;
        } else {
            for (object * o : m_heap_refs) {
                lean_dec_ref(o);
            }
            m_heap_refs.clear();
        }
        m_curr_slab = 0;
        m_offset = 0;
        m_used_bytes = 0;
    }
};

static thread_local kernel_arena g_kernel_arena;

kernel_arena_scope::kernel_arena_scope() {
    m_outermost = (g_kernel_arena.m_depth == 0);
    ++g_kernel_arena.m_depth;
    if (m_outermost) {
        g_kernel_arena.next_epoch();
        g_kernel_arena.m_active = true;
    }
}

kernel_arena_scope::~kernel_arena_scope() {
    --g_kernel_arena.m_depth;
    if (m_outermost) {
        g_kernel_arena.m_active = false;
        g_kernel_arena.reset();
    }
}

kernel_arena_pause_scope::kernel_arena_pause_scope() {
    m_prev_active = g_kernel_arena.m_active;
    g_kernel_arena.m_active = false;
}

kernel_arena_pause_scope::~kernel_arena_pause_scope() {
    g_kernel_arena.m_active = m_prev_active;
}

void kernel_arena_retain_on_exception() {
    if (g_kernel_arena.m_depth > 0 && g_kernel_arena.m_used_bytes > 0) {
        g_kernel_arena.m_retain_on_exit = true;
    }
}

static expr promote_rec(expr const & e) {
    if (!g_kernel_arena.in_current_slabs(e.raw())) {
        return e;
    }
    switch (e.kind()) {
    case expr_kind::BVar:   return mk_bvar(bvar_idx(e));
    case expr_kind::FVar:   return mk_fvar(fvar_name(e));
    case expr_kind::MVar:   return e;
    case expr_kind::Sort:   return mk_sort(sort_level(e));
    case expr_kind::Const:  return mk_const(const_name(e), const_levels(e));
    case expr_kind::App:    return mk_app(promote_rec(app_fn(e)), promote_rec(app_arg(e)));
    case expr_kind::Lambda: return mk_lambda(binding_name(e), promote_rec(binding_domain(e)), promote_rec(binding_body(e)), binding_info(e));
    case expr_kind::Pi:     return mk_pi(binding_name(e), promote_rec(binding_domain(e)), promote_rec(binding_body(e)), binding_info(e));
    case expr_kind::Let:    return mk_let(let_name(e), promote_rec(let_type(e)), promote_rec(let_value(e)), promote_rec(let_body(e)), let_nondep(e));
    case expr_kind::Lit:    return mk_lit(lit_value(e));
    case expr_kind::MData:  return mk_mdata(mdata_data(e), promote_rec(mdata_expr(e)));
    case expr_kind::Proj:   return mk_proj(proj_sname(e), proj_idx(e), promote_rec(proj_expr(e)));
    }
    lean_unreachable();
}

expr kernel_arena_promote(expr const & e) {
    kernel_arena_retain_on_exception();
    if (g_kernel_arena.m_used_bytes == 0) return e;
    kernel_arena_pause_scope pause;
    return promote_rec(e);
}

kernel_arena_stats get_kernel_arena_stats() {
    return kernel_arena_stats{
        g_kernel_arena.m_peak_bytes,
        g_kernel_arena.m_total_alloc_bytes,
        g_kernel_arena.m_total_scopes
    };
}

// =======================================
// Constructors

static constexpr size_t NUM_STATIC_BVARS = 1024;
static object * g_bvars[NUM_STATIC_BVARS] = {nullptr};

static expr * g_dummy = nullptr;

static expr const & get_dummy() {
    if (!g_dummy) {
        g_dummy = new expr(mk_constant("__expr_for_default_constructor__"));
        mark_persistent(g_dummy->raw());
    }
    return *g_dummy;
}

expr::expr():expr(get_dummy()) {}

extern "C" object * lean_expr_mk_lit(obj_arg l);
expr mk_lit(literal const & l) { return expr(lean_expr_mk_lit(l.to_obj_arg())); }

extern "C" object * lean_expr_mk_mdata(obj_arg m, obj_arg e);
expr mk_mdata(kvmap const & m, expr const & e) {
    uint64_t data = mk_mdata_data(get_data(e));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(10, 2, 32)) {
            g_kernel_arena.track_child(m.raw());
            g_kernel_arena.track_child(e.raw());
            lean_ctor_set(o, 0, m.raw());
            lean_ctor_set(o, 1, e.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*2, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(10, 2, 8);
    lean_ctor_set(o, 0, m.to_obj_arg());
    lean_ctor_set(o, 1, e.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*2, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_proj(obj_arg s, obj_arg idx, obj_arg e);
expr mk_proj(name const & s, nat const & idx, expr const & e) {
    uint64_t data = mk_proj_data(s, idx, get_data(e));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(11, 3, 40)) {
            g_kernel_arena.track_child(s.raw());
            g_kernel_arena.track_child(idx.raw());
            g_kernel_arena.track_child(e.raw());
            lean_ctor_set(o, 0, s.raw());
            lean_ctor_set(o, 1, idx.raw());
            lean_ctor_set(o, 2, e.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*3, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(11, 3, 8);
    lean_ctor_set(o, 0, s.to_obj_arg());
    lean_ctor_set(o, 1, idx.to_obj_arg());
    lean_ctor_set(o, 2, e.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*3, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_bvar(obj_arg idx);
expr mk_bvar(nat const & idx) {
    if (LEAN_LIKELY(idx.is_small())) {
        size_t v = idx.get_small_value();
        if (LEAN_LIKELY(v < NUM_STATIC_BVARS && g_bvars[v] != nullptr)) {
            return expr(g_bvars[v]);
        }
    }
    return expr(lean_expr_mk_bvar(idx.to_obj_arg()));
}

extern "C" object * lean_expr_mk_fvar(obj_arg n);
expr mk_fvar(name const & n) {
    uint64_t data = mk_fvar_data(n);
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(1, 1, 24)) {
            g_kernel_arena.track_child(n.raw());
            lean_ctor_set(o, 0, n.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*1, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(1, 1, 8);
    lean_ctor_set(o, 0, n.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*1, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_const(obj_arg n, obj_arg ls);
expr mk_const(name const & n, levels const & ls) {
    uint64_t data = mk_const_data(n, ls);
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(4, 2, 32)) {
            g_kernel_arena.track_child(n.raw());
            g_kernel_arena.track_child(ls.raw());
            lean_ctor_set(o, 0, n.raw());
            lean_ctor_set(o, 1, ls.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*2, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(4, 2, 8);
    lean_ctor_set(o, 0, n.to_obj_arg());
    lean_ctor_set(o, 1, ls.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*2, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_app(obj_arg f, obj_arg a);
expr mk_app(expr const & f, expr const & a) {
    uint64_t data = lean_expr_mk_app_data(get_data(f), get_data(a));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(5, 2, 32)) {
            g_kernel_arena.track_child(f.raw());
            g_kernel_arena.track_child(a.raw());
            lean_ctor_set(o, 0, f.raw());
            lean_ctor_set(o, 1, a.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*2, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(5, 2, 8);
    lean_ctor_set(o, 0, f.to_obj_arg());
    lean_ctor_set(o, 1, a.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*2, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_sort(obj_arg l);
expr mk_sort(level const & l) {
    uint64_t data = mk_sort_data(l);
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(3, 1, 24)) {
            g_kernel_arena.track_child(l.raw());
            lean_ctor_set(o, 0, l.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*1, data);
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(3, 1, 8);
    lean_ctor_set(o, 0, l.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*1, data);
    return expr(o);
}

extern "C" object * lean_expr_mk_lambda(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
expr mk_lambda(name const & n, expr const & t, expr const & e, binder_info bi) {
    uint64_t data = mk_binding_data(get_data(t), get_data(e));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(6, 3, 48)) {
            g_kernel_arena.track_child(n.raw());
            g_kernel_arena.track_child(t.raw());
            g_kernel_arena.track_child(e.raw());
            lean_ctor_set(o, 0, n.raw());
            lean_ctor_set(o, 1, t.raw());
            lean_ctor_set(o, 2, e.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*3, data);
            lean_ctor_set_uint8(o, sizeof(void*)*3 + 8, static_cast<uint8>(bi));
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(6, 3, 9);
    lean_ctor_set(o, 0, n.to_obj_arg());
    lean_ctor_set(o, 1, t.to_obj_arg());
    lean_ctor_set(o, 2, e.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*3, data);
    lean_ctor_set_uint8(o, sizeof(void*)*3 + 8, static_cast<uint8>(bi));
    return expr(o);
}

extern "C" object * lean_expr_mk_forall(obj_arg n, obj_arg t, obj_arg e, uint8 bi);
expr mk_pi(name const & n, expr const & t, expr const & e, binder_info bi) {
    uint64_t data = mk_binding_data(get_data(t), get_data(e));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(7, 3, 48)) {
            g_kernel_arena.track_child(n.raw());
            g_kernel_arena.track_child(t.raw());
            g_kernel_arena.track_child(e.raw());
            lean_ctor_set(o, 0, n.raw());
            lean_ctor_set(o, 1, t.raw());
            lean_ctor_set(o, 2, e.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*3, data);
            lean_ctor_set_uint8(o, sizeof(void*)*3 + 8, static_cast<uint8>(bi));
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(7, 3, 9);
    lean_ctor_set(o, 0, n.to_obj_arg());
    lean_ctor_set(o, 1, t.to_obj_arg());
    lean_ctor_set(o, 2, e.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*3, data);
    lean_ctor_set_uint8(o, sizeof(void*)*3 + 8, static_cast<uint8>(bi));
    return expr(o);
}

static name * g_default_name = nullptr;
expr mk_arrow(expr const & t, expr const & e) {
    return mk_pi(*g_default_name, t, e, mk_binder_info());
}

extern "C" object * lean_expr_mk_let(object * n, object * t, object * v, object * b, uint8 nondep);
expr mk_let(name const & n, expr const & t, expr const & v, expr const & b, bool nondep) {
    uint64_t data = mk_let_data(get_data(t), get_data(v), get_data(b));
    if (g_kernel_arena.m_active) {
        if (object * o = g_kernel_arena.alloc_ctor(8, 4, 56)) {
            g_kernel_arena.track_child(n.raw());
            g_kernel_arena.track_child(t.raw());
            g_kernel_arena.track_child(v.raw());
            g_kernel_arena.track_child(b.raw());
            lean_ctor_set(o, 0, n.raw());
            lean_ctor_set(o, 1, t.raw());
            lean_ctor_set(o, 2, v.raw());
            lean_ctor_set(o, 3, b.raw());
            lean_ctor_set_uint64(o, sizeof(void*)*4, data);
            lean_ctor_set_uint8(o, sizeof(void*)*4 + 8, static_cast<uint8>(nondep));
            return expr(o);
        }
    }
    object * o = lean_alloc_ctor(8, 4, 9);
    lean_ctor_set(o, 0, n.to_obj_arg());
    lean_ctor_set(o, 1, t.to_obj_arg());
    lean_ctor_set(o, 2, v.to_obj_arg());
    lean_ctor_set(o, 3, b.to_obj_arg());
    lean_ctor_set_uint64(o, sizeof(void*)*4, data);
    lean_ctor_set_uint8(o, sizeof(void*)*4 + 8, static_cast<uint8>(nondep));
    return expr(o);
}

static expr * g_Prop  = nullptr;
expr mk_Prop() { return *g_Prop; }

// =======================================
// Auxiliary constructors and accessors

expr mk_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    for (unsigned i = 0; i < num_args; i++)
        r = mk_app(r, args[i]);
    return r;
}

expr mk_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_app(mk_app(args[0], args[1]), num_args - 2, args+2);
}

expr mk_rev_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mk_app(r, args[i]);
    }
    return r;
}

expr const & get_app_args(expr const & e, buffer<expr> & args) {
    unsigned sz = args.size();
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    std::reverse(args.begin() + sz, args.end());
    return *it;
}

expr const & get_app_rev_args(expr const & e, buffer<expr> & args) {
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    return *it;
}

expr const & get_app_fn(expr const & e) {
    expr const * it = &e;
    while (is_app(*it)) {
        it = &(app_fn(*it));
    }
    return *it;
}

unsigned get_app_num_args(expr const & e) {
    expr const * it = &e;
    unsigned n = 0;
    while (is_app(*it)) {
        it = &(app_fn(*it));
        n++;
    }
    return n;
}

bool is_arrow(expr const & t) {
    if (!is_pi(t)) return false;
    if (has_loose_bvars(t)) {
        return !has_loose_bvar(binding_body(t), 0);
    } else {
        lean_assert(has_loose_bvars(binding_body(t)) == has_loose_bvar(binding_body(t), 0));
        return !has_loose_bvars(binding_body(t));
    }
}

extern "C" uint8 lean_expr_is_have(object * e);
bool let_nondep_core(expr const & e) {
    lean_assert(is_let(e));
    return lean_expr_is_have(e.to_obj_arg());
}

// =======================================
// Update

expr update_mdata(expr const & e, expr const & t) {
    if (!is_eqp(mdata_expr(e), t))
        return mk_mdata(mdata_data(e), t);
    else
        return e;
}

expr update_proj(expr const & e, expr const & t) {
    if (!is_eqp(proj_expr(e), t))
        return mk_proj(proj_sname(e), proj_idx(e), t);
    else
        return e;
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return mk_app(new_fn, new_arg);
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e));
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info bi) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body) || bi != binding_info(e))
        return mk_binding(e.kind(), binding_name(e), new_domain, new_body, bi);
    else
        return e;
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return mk_sort(new_level);
    else
        return e;
}

expr update_const(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return mk_const(const_name(e), new_levels);
    else
        return e;
}

expr update_let(expr const & e, expr const & new_type, expr const & new_value, expr const & new_body) {
    if (!is_eqp(let_type(e), new_type) || !is_eqp(let_value(e), new_value) || !is_eqp(let_body(e), new_body))
        return mk_let(let_name(e), new_type, new_value, new_body, let_nondep(e));
    else
        return e;
}

extern "C" object * lean_expr_consume_type_annotations(obj_arg e);

expr consume_type_annotations(expr const & e) { return expr(lean_expr_consume_type_annotations(e.to_obj_arg())); }

// =======================================
// Loose bound variable management

static bool has_loose_bvars_in_domain(expr const & b, unsigned vidx, bool strict) {
    if (is_pi(b)) {
        if (has_loose_bvar(binding_domain(b), vidx)) {
            if (is_explicit(binding_info(b))) {
                return true;
            } else if (has_loose_bvars_in_domain(binding_body(b), 0, strict)) {
                // "Transitivity": vidx occurs in current implicit argument, so we search for current argument in the body.
                return true;
            }
        }
        // finally we search for vidx in the body
        return has_loose_bvars_in_domain(binding_body(b), vidx+1, strict);
    } else if (!strict) {
        return has_loose_bvar(b, vidx);
    } else {
        return false;
    }
}

bool has_loose_bvar(expr const & e, unsigned i) {
    if (!has_loose_bvars(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned offset) {
            if (found)
                return false; // already found
            unsigned n_i = i + offset;
            if (n_i < i)
                return false; // overflow, vidx can't be >= max unsigned
            if (n_i >= get_loose_bvar_range(e))
                return false; // expression e does not contain bound variables with idx >= n_i
            if (is_var(e)) {
                nat const & vidx = bvar_idx(e);
                if (vidx == n_i)
                    found = true;
            }
            return true; // continue search
        });
    return found;
}

extern "C" LEAN_EXPORT uint8 lean_expr_has_loose_bvar(b_obj_arg e, b_obj_arg i) {
    if (!lean_is_scalar(i))
        return false;
    return has_loose_bvar(TO_REF(expr, e), lean_unbox(i));
}

struct lower_loose_bvars_policy {
    static constexpr bool only_atomic = true;
    unsigned m_s;
    unsigned m_d;
    bool should_return_self(expr const & e, unsigned offset) const {
        unsigned s1 = m_s + offset;
        return s1 < m_s || s1 >= get_loose_bvar_range(e);
    }
    expr visit_atomic(expr const & e, unsigned offset) const {
        if (is_bvar(e)) {
            nat const & vidx = bvar_idx(e);
            unsigned s1 = m_s + offset;
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= s1) {
                    lean_assert(idx >= offset + m_d);
                    return mk_bvar(nat::of_size_t(idx - m_d));
                }
            } else if (vidx >= s1) {
                return mk_bvar(vidx - nat(m_d));
            }
        }
        return e;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

expr lower_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    lean_assert(s >= d);
    return replace_custom(e, lower_loose_bvars_policy{s, d});
}

expr lower_loose_bvars(expr const & e, unsigned d) {
    return lower_loose_bvars(e, d, d);
}

extern "C" LEAN_EXPORT object * lean_expr_lower_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d) || lean_unbox(s) < lean_unbox(d)) {
        lean_inc(e);
        return e;
    }
    return lower_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
}

struct lift_loose_bvars_policy {
    static constexpr bool only_atomic = true;
    unsigned m_s;
    unsigned m_d;
    bool should_return_self(expr const & e, unsigned offset) const {
        unsigned s1 = m_s + offset;
        return s1 < m_s || s1 >= get_loose_bvar_range(e);
    }
    expr visit_atomic(expr const & e, unsigned offset) const {
        if (is_bvar(e)) {
            nat const & vidx = bvar_idx(e);
            unsigned s1 = m_s + offset;
            if (vidx.is_small()) {
                size_t idx = vidx.get_small_value();
                if (idx >= s1) {
                    return mk_bvar(nat::of_size_t(idx + m_d));
                }
            } else if (vidx >= s1) {
                return mk_bvar(vidx + nat(m_d));
            }
        }
        return e;
    }
    optional<expr> visit(expr const &, unsigned) const { return none_expr(); }
};

expr lift_loose_bvars(expr const & e, unsigned s, unsigned d) {
    if (d == 0 || s >= get_loose_bvar_range(e))
        return e;
    return replace_custom(e, lift_loose_bvars_policy{s, d});
}

expr lift_loose_bvars(expr const & e, unsigned d) {
    return lift_loose_bvars(e, 0, d);
}

extern "C" LEAN_EXPORT object * lean_expr_lift_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
    if (!lean_is_scalar(s) || !lean_is_scalar(d)) {
        lean_inc(e);
        return e;
    }
    return lift_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
}

extern "C" LEAN_EXPORT uint8 lean_expr_is_app_of_arity(b_obj_arg e, b_obj_arg n, b_obj_arg a_obj) {
    if (!lean_is_scalar(a_obj)) return 0;
    size_t a = lean_unbox(a_obj);
    while (a > 0) {
        if (expr_kind_core(e) != expr_kind::App) return 0;
        e = lean_ctor_get(e, 0);
        --a;
    }
    if (expr_kind_core(e) != expr_kind::Const) return 0;
    return lean_name_eq(lean_ctor_get(e, 0), n);
}

extern "C" LEAN_EXPORT uint8 lean_expr_is_app_of_arity_prime(b_obj_arg e, b_obj_arg n, b_obj_arg a_obj) {
    if (!lean_is_scalar(a_obj)) return 0;
    size_t a = lean_unbox(a_obj);
    while (true) {
        expr_kind k = expr_kind_core(e);
        if (k == expr_kind::MData) {
            e = lean_ctor_get(e, 1);
        } else if (a > 0) {
            if (k != expr_kind::App) return 0;
            e = lean_ctor_get(e, 0);
            --a;
        } else {
            if (k != expr_kind::Const) return 0;
            return lean_name_eq(lean_ctor_get(e, 0), n);
        }
    }
}

// =======================================
// Implicit argument inference

expr infer_implicit(expr const & t, unsigned num_params, bool strict) {
    if (num_params == 0) {
        return t;
    } else if (is_pi(t)) {
        expr new_body = infer_implicit(binding_body(t), num_params-1, strict);
        if (!is_explicit(binding_info(t))) {
            // argument is already marked as implicit
            return update_binding(t, binding_domain(t), new_body);
        } else if (has_loose_bvars_in_domain(new_body, 0, strict)) {
            return update_binding(t, binding_domain(t), new_body, mk_implicit_binder_info());
        } else {
            return update_binding(t, binding_domain(t), new_body);
        }
    } else {
        return t;
    }
}

expr infer_implicit(expr const & t, bool strict) {
    return infer_implicit(t, std::numeric_limits<unsigned>::max(), strict);
}

// =======================================
// Initialization & Finalization

void initialize_expr() {
    for (size_t i = 0; i < NUM_STATIC_BVARS; ++i) {
        g_bvars[i] = lean_expr_mk_bvar(lean_box(i));
        mark_persistent(g_bvars[i]);
    }
    get_dummy();
    g_default_name = new name("a");
    mark_persistent(g_default_name->raw());
    g_Prop         = new expr(mk_sort(mk_level_zero()));
    mark_persistent(g_Prop->raw());
    /* TODO(Leo): add support for builtin constants in the kernel.
       Something similar to what we have in the library directory. */
}

void finalize_expr() {
    delete g_Prop;
    delete g_dummy;
    delete g_default_name;
}
}
