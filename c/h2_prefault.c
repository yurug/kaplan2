/* ktdeque_dequeptr.c — packets-and-chains C implementation with FLAT
 * packet allocation and DIFF-link encoding.  Each Rocq `Packet A` value
 * (a yellow run of k nested levels) maps to one FULL chain link allocation
 * containing 2*k contiguous `kt_buf`s.  Cascade through a yellow run is
 * in-place buffer manipulation on a stack-local packet copy, with at most
 * 2 mallocs committed per operation (one new top link plus, when the
 * cascade extends past the packet, one new tail link).
 *
 * Phase P (diff-link, K=1):  Most ops modify exactly one of {outer pre,
 * outer suf} and leave inner bufs / deeper levels untouched.  We model
 * this with a smaller "DIFF" link variant that stores only the changed
 * buffer + a back-reference to a FULL "base" link, plus a separate
 * effective-tail pointer.  The K=1 invariant says: a DIFF's `base` is
 * always a FULL link.  Writes over a DIFF either re-base (when the new
 * op modifies the same outer side as the existing override — drop the
 * old override, install the new one over the same base) or materialize
 * a fresh FULL (when the op modifies the opposite side, since one DIFF
 * can hold only a single override).  This keeps reads O(1) (at most one
 * indirection through DIFF→base).
 *
 *   chain ::= NULL                            -- empty deque
 *           | kt_chain_link                   -- non-empty (FULL or DIFF)
 *
 *   FULL link  =  16-byte header + bufs[2*depth*40]   (96 B for depth=1)
 *   DIFF link  =  16-byte header + base ptr + override (64 B)
 *
 * Convention: a FULL link with depth=1, bufs=[b, B0], tail=NULL is the
 * pure "Ending(b)" form.  Pure endings are always FULL (DIFFs require a
 * non-NULL base, hence non-NULL tail-or-base, so they are never pure
 * endings).
 *
 * The cascade dynamics mirror Viennot's `green_of_red`:
 *   - depth=1, tail=NULL    -> make_small (1-2 chain link allocs)
 *   - depth=1, tail!=NULL   -> green_of_red Case 2 (1 alloc, merges
 *                              top's outer with tail's outer level)
 *   - depth>=2              -> green_of_red Case 3 (2 allocs, splits
 *                              top's yellow run at the outer level)
 */

#include "ktdeque.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#ifdef KT_DIFF_DEBUG
#include <stdio.h>
#endif

#define MAX_BUF 5
#define MAX_PACKET_DEPTH 64

/* ====================================================================== */
/* Bump-pointer arena for chain links and pairs.                          */
/*                                                                         */
/* glibc malloc costs ~30-50 ns/call due to locking and bookkeeping.      */
/* We replace it with a thread-local bump allocator that takes 4 MB       */
/* chunks from malloc.  This LEAKS memory across the bench (chunks are    */
/* never freed), but the bench is O(n) cumulative allocation regardless.  */
/* Cache locality is much better since fresh allocations are contiguous.  */
/* ====================================================================== */

#define ARENA_CHUNK_SIZE (4 * 1024 * 1024)  /* 4 MB chunks */

typedef struct kt_arena_chunk {
    struct kt_arena_chunk* prev;
    char* bump;
    char* end;
    char data[];
} kt_arena_chunk;

static __thread kt_arena_chunk* g_arena = NULL;

static void arena_grow(size_t need) {
    size_t chunk_payload = ARENA_CHUNK_SIZE;
    if (need > chunk_payload) chunk_payload = need;
    kt_arena_chunk* c = (kt_arena_chunk*)malloc(sizeof(*c) + chunk_payload);
    c->prev = g_arena;
    c->bump = c->data;
    c->end  = c->data + chunk_payload;
    /* H2 prefault variant: touch every page once to skip demand-paging
       cost on first access during operations.  Real cost: warmup; benefit:
       page faults amortize into a tight init loop instead of slowing
       individual ops. */
    for (volatile char* p = c->data; p < c->end; p += 4096) *p = 0;
    g_arena = c;
}

/* arena_alloc: O(1) bump allocation, 16-byte aligned for safety. */
static inline void* arena_alloc(size_t sz) {
    /* Round up to 16 bytes for alignment (kt_buf has 8-byte members,
       kt_chain_link has pointers; 16 covers both). */
    sz = (sz + 15u) & ~(size_t)15u;
    if (__builtin_expect(g_arena == NULL || g_arena->bump + sz > g_arena->end, 0)) {
        arena_grow(sz);
    }
    void* p = g_arena->bump;
    g_arena->bump += sz;
    return p;
}

/* ====================================================================== */
/* Buffer (Buf5)                                                          */
/*                                                                         */
/* Stage-1 packed layout: 40 bytes.  We exploit the fact that all element */
/* pointers (kt_pair* from arena_alloc, base elements supplied by users)  */
/* are at least 8-byte aligned, hence the low 3 bits are always zero.  We */
/* steal those 3 bits in slot 0 to encode the buffer size (0..5).         */
/*                                                                         */
/*   empty (size=0):  e[0] = NULL                                          */
/*   non-empty:       e[0] = (real_ptr | size)                            */
/*                                                                         */
/* Two ALU operations recover the real pointer / size; in exchange we     */
/* drop 8 bytes of padding per buffer (was: 1 size byte + 7 padding + 5   */
/* pointers = 48 bytes).  Per chain link this saves 16 bytes (depth=1) or */
/* more for deeper packets, which translates to fewer cache lines copied  */
/* on each rebuild.                                                        */
/*                                                                         */
/* CRITICAL ALIGNMENT GUARANTEE: every kt_elem stored in slot 0 must have */
/* its low 3 bits equal to zero.  arena_alloc returns 16-byte aligned     */
/* memory.  Users pass &storage[i] for some 8-byte type (e.g. long), also */
/* satisfying the constraint.                                              */
/* ====================================================================== */

#define BUF_TAG_MASK ((uintptr_t)0x7)

typedef struct {
    kt_elem e[MAX_BUF];   /* 40 bytes; e[0] low 3 bits encode size */
} kt_buf;

/* Decode size from a buf: the low 3 bits of e[0] (0 when e[0]==NULL). */
static inline uint8_t buf_size(const kt_buf* b) {
    return (uint8_t)((uintptr_t)b->e[0] & BUF_TAG_MASK);
}

/* Decode the actual pointer in slot 0 (mask off the size bits). */
static inline kt_elem buf_at0(const kt_buf* b) {
    return (kt_elem)((uintptr_t)b->e[0] & ~BUF_TAG_MASK);
}

/* Read element at index i; only slot 0 needs masking. */
static inline kt_elem buf_at(const kt_buf* b, int i) {
    if (i == 0) return buf_at0(b);
    return b->e[i];
}

/* Tag a pointer p with size in the low 3 bits. */
static inline kt_elem buf_tag(kt_elem p, uint8_t size) {
    return (kt_elem)((uintptr_t)p | (uintptr_t)size);
}

/* buf_empty: encoded as e[0] = NULL (size=0). */
static inline kt_buf buf_empty(void) {
    kt_buf b;
    b.e[0] = NULL; b.e[1] = NULL; b.e[2] = NULL; b.e[3] = NULL; b.e[4] = NULL;
    return b;
}

static inline kt_buf buf_singleton(kt_elem x) {
    kt_buf b;
    b.e[0] = buf_tag(x, 1);
    b.e[1] = NULL; b.e[2] = NULL; b.e[3] = NULL; b.e[4] = NULL;
    return b;
}

static inline kt_buf buf_pair_2(kt_elem a, kt_elem b) {
    kt_buf r;
    r.e[0] = buf_tag(a, 2); r.e[1] = b;
    r.e[2] = NULL; r.e[3] = NULL; r.e[4] = NULL;
    return r;
}

static inline kt_buf buf_pair_3(kt_elem a, kt_elem b, kt_elem c) {
    kt_buf r;
    r.e[0] = buf_tag(a, 3); r.e[1] = b; r.e[2] = c;
    r.e[3] = NULL; r.e[4] = NULL;
    return r;
}

/* buf5_push : prepend x to b.  Returns 1 on success, 0 if b is B5.
 * On failure *out is initialized to empty so callers don't trip
 * maybe-uninitialized warnings.  Hot-path: copies whole array contents
 * (constant size, branch-free). */
static inline int buf_push(kt_elem x, const kt_buf* b, kt_buf* out) {
    int s = (int)buf_size(b);
    if (__builtin_expect(s >= MAX_BUF, 0)) {
        *out = buf_empty();
        return 0;
    }
    /* Copy all 5 slots regardless — constant-size copies vectorize well.
       Slot 0 of new buf is x tagged with size (s+1); slots 1..4 are the
       previous slots 0..3 with slot-0 unmasked. */
    out->e[0] = buf_tag(x, (uint8_t)(s + 1));
    out->e[1] = buf_at0(b);
    out->e[2] = b->e[1];
    out->e[3] = b->e[2];
    out->e[4] = b->e[3];
    return 1;
}

/* buf5_inject : append x to b.  Returns 1 on success, 0 if b is B5.
 * For empty input (size=0), x becomes the new slot 0. */
static inline int buf_inject(const kt_buf* b, kt_elem x, kt_buf* out) {
    int s = (int)buf_size(b);
    if (__builtin_expect(s >= MAX_BUF, 0)) {
        *out = buf_empty();
        return 0;
    }
    /* Build by copying then writing x at slot s.  We must:
        - propagate the existing tagged slot 0 as-is, then update its tag
          to the new size (s+1) — but if s==0 then x goes to slot 0 with
          tag (s+1)=1 instead.
       Simplest correct form: copy unmasked slots, then either override
       slot 0 with buf_tag(x,1) when s==0, or override slot s with x and
       re-tag slot 0. */
    if (s == 0) {
        out->e[0] = buf_tag(x, 1);
        out->e[1] = NULL; out->e[2] = NULL; out->e[3] = NULL; out->e[4] = NULL;
        return 1;
    }
    out->e[0] = buf_tag(buf_at0(b), (uint8_t)(s + 1));
    out->e[1] = b->e[1];
    out->e[2] = b->e[2];
    out->e[3] = b->e[3];
    out->e[4] = b->e[4];
    out->e[s] = x;
    return 1;
}

/* buf5_pop : remove front. Returns 1 on success, 0 if b is B0.
 * On failure, *out_rest is initialized to empty and *out_x = NULL so callers
 * don't trip maybe-uninitialized warnings. */
static inline int buf_pop(const kt_buf* b, kt_elem* out_x, kt_buf* out_rest) {
    int s = (int)buf_size(b);
    if (__builtin_expect(s == 0, 0)) {
        *out_x = NULL;
        *out_rest = buf_empty();
        return 0;
    }
    *out_x = buf_at0(b);
    /* Shift left by 1; new slot 0 is old slot 1 (untagged), tagged with size s-1. */
    if (s == 1) {
        out_rest->e[0] = NULL;
    } else {
        out_rest->e[0] = buf_tag(b->e[1], (uint8_t)(s - 1));
    }
    out_rest->e[1] = b->e[2];
    out_rest->e[2] = b->e[3];
    out_rest->e[3] = b->e[4];
    out_rest->e[4] = NULL;
    return 1;
}

/* buf5_eject : remove back. Returns 1 on success, 0 if b is B0. */
static inline int buf_eject(const kt_buf* b, kt_buf* out_rest, kt_elem* out_x) {
    int s = (int)buf_size(b);
    if (__builtin_expect(s == 0, 0)) {
        *out_x = NULL;
        *out_rest = buf_empty();
        return 0;
    }
    *out_x = buf_at(b, s - 1);
    if (s == 1) {
        /* Result is empty. */
        out_rest->e[0] = NULL; out_rest->e[1] = NULL; out_rest->e[2] = NULL;
        out_rest->e[3] = NULL; out_rest->e[4] = NULL;
        return 1;
    }
    out_rest->e[0] = buf_tag(buf_at0(b), (uint8_t)(s - 1));
    out_rest->e[1] = b->e[1];
    out_rest->e[2] = b->e[2];
    out_rest->e[3] = b->e[3];
    out_rest->e[4] = NULL;
    /* Clear the slot we just removed (was at index s-1; for s>=2 that is */
    /* an index in 1..4, so untagged). */
    out_rest->e[s - 1] = NULL;
    return 1;
}

/* ====================================================================== */
/* Chain link / packet (flat layout)                                      */
/* ====================================================================== */

/* Color tag (Viennot regularity).  Required because the structural color
 * (derived from buffer sizes) does not always coincide with the tag —
 * green_of_red Case 3 produces a "tagged R" successor whose buffers may
 * be sized as G/Y, but it must still be treated as R for chain
 * regularity (i.e., needs ensure_green before its parent transitions
 * to Y/R). */
typedef enum {
    COL_G = 0,
    COL_Y = 1,
    COL_R = 2
} kt_color;

/* Diff-link encoding (Phase P):
 *
 * Most operations modify exactly one of {outer_pre, outer_suf} and leave
 * inner bufs, tail, and tag-modulo-recompute alone.  A FULL link is
 * 16 + 2*depth*40 bytes; a DIFF link is 16 + 40 = 56 bytes (40 % smaller
 * for depth=1).
 *
 * INVARIANT (K=1): a DIFF's `base` always points to a FULL link, never to
 * another DIFF.  When a write would create a DIFF over a DIFF, we
 * materialize: walk through the existing DIFF to its base FULL, compose
 * the new override + the existing override into a fresh FULL.  This keeps
 * reads O(1) (one indirection at most).
 *
 * Layout: kind, depth, tag, which fit in the first 4 bytes.  FULL stores
 * the tail pointer + bufs[2*depth].  DIFF stores the base pointer + a
 * single `override` buffer (and the unmodified buf can be read from
 * base->bufs[]).  Both share the bufs[] flexible array but interpret it
 * differently — the kind discriminant must be checked first.
 */
typedef enum {
    LINK_FULL = 0,
    LINK_DIFF = 1
} kt_link_kind;

typedef struct kt_chain_link {
    uint8_t depth;                  /* FULL: 1..MAX_PACKET_DEPTH; DIFF: ignored */
    uint8_t tag;                    /* kt_color (effective tag) */
    uint8_t kind;                   /* LINK_FULL or LINK_DIFF */
    uint8_t which;                  /* DIFF only: 0=pre overridden, 1=suf */
    uint8_t chain_pos;              /* Position in chain: head=0, tail=head+head.depth, etc.
                                       Determines the "level" of elements in this link's
                                       outer bufs.  bufs[2*i], bufs[2*i+1] hold elements at
                                       level chain_pos + i. */
    uint8_t _pad0, _pad1, _pad2;    /* 3 bytes padding to align tail on 8-byte boundary */
    struct kt_chain_link* tail;     /* Effective deeper chain pointer (NULL =
                                       Ending) — same semantics for FULL
                                       and DIFF. */
    /* From here, FULL and DIFF diverge:
         FULL: bufs[2*depth] (pre_0, suf_0, pre_1, suf_1, ...).
         DIFF: { kt_chain_link* base; kt_buf override; }
       Cast to kt_chain_link_diff to access the DIFF tail. */
    kt_buf  bufs[];                 /* FULL only; for DIFF, see below. */
} kt_chain_link;

/* DIFF link layout: shares first 16 bytes (header + tail) with FULL.  Used
 * when only one outer buffer changed and we want a smaller allocation. */
typedef struct {
    uint8_t depth, tag, kind, which, chain_pos, _pad0, _pad1, _pad2;
    struct kt_chain_link* tail;     /* Effective tail (may differ from base->tail). */
    struct kt_chain_link* base;     /* FULL link supplying unchanged outer/inner bufs.
                                       Never NULL, never DIFF (K=1 invariant). */
    kt_buf  override;
} kt_chain_link_diff;

#define PRE(L,i)  ((L)->bufs[2*(i)])
#define SUF(L,i)  ((L)->bufs[2*(i)+1])

/* ----- Diff-link accessors ----- */

/* link_outer_pre(L): returns a pointer to the effective outer pre buffer.
 * O(1) — at most one indirection through DIFF's base. */
static inline const kt_buf* link_outer_pre(const kt_chain_link* L) {
    if (__builtin_expect(L->kind == LINK_FULL, 1)) return &L->bufs[0];
    const kt_chain_link_diff* D = (const kt_chain_link_diff*)L;
    if (D->which == 0) return &D->override;
    return &D->base->bufs[0];
}

static inline const kt_buf* link_outer_suf(const kt_chain_link* L) {
    if (__builtin_expect(L->kind == LINK_FULL, 1)) return &L->bufs[1];
    const kt_chain_link_diff* D = (const kt_chain_link_diff*)L;
    if (D->which == 1) return &D->override;
    return &D->base->bufs[1];
}

/* link_tail(L): effective tail pointer (same field for FULL and DIFF). */
static inline struct kt_chain_link* link_tail(const kt_chain_link* L) {
    return L->tail;
}

/* link_depth(L): effective depth.  For DIFF, this is base->depth. */
static inline uint8_t link_depth(const kt_chain_link* L) {
    if (__builtin_expect(L->kind == LINK_FULL, 1)) return L->depth;
    const kt_chain_link_diff* D = (const kt_chain_link_diff*)L;
    return D->base->depth;
}

/* link_buf_at(L, i): effective i-th buffer (0..2*depth-1). */
static inline const kt_buf* link_buf_at(const kt_chain_link* L, int i) {
    if (__builtin_expect(L->kind == LINK_FULL, 1)) return &L->bufs[i];
    const kt_chain_link_diff* D = (const kt_chain_link_diff*)L;
    if (i == D->which) return &D->override;
    return &D->base->bufs[i];
}

/* link_as_full(L): if L is FULL, return L.  If L is DIFF, return its base.
 * Useful when a code path needs the underlying full link's bufs[2..]
 * directly (deeper inner levels). */
static inline const kt_chain_link* link_as_full(const kt_chain_link* L) {
    if (__builtin_expect(L->kind == LINK_FULL, 1)) return L;
    const kt_chain_link_diff* D = (const kt_chain_link_diff*)L;
    return D->base;
}

/* ----- alloc counters for wc_test ----- */
#ifdef KT_PROFILE
static size_t g_alloc_links = 0;
static size_t g_alloc_pairs = 0;
size_t kt_alloc_packets(void) { return g_alloc_links; }
size_t kt_alloc_chains(void)  { return 0; }
size_t kt_alloc_pairs(void)   { return g_alloc_pairs; }
size_t kt_alloc_bufs(void)    { return 0; }
void   kt_reset_alloc_counters(void) { g_alloc_links = 0; g_alloc_pairs = 0; }
#else
size_t kt_alloc_packets(void) { return 0; }
size_t kt_alloc_chains(void)  { return 0; }
size_t kt_alloc_pairs(void)   { return 0; }
size_t kt_alloc_bufs(void)    { return 0; }
void   kt_reset_alloc_counters(void) {}
#endif

#ifdef KT_DIFF_TRACE
static size_t g_diff_count = 0;
static size_t g_full_count = 0;
size_t kt_diff_count(void) { return g_diff_count; }
size_t kt_full_count(void) { return g_full_count; }
#endif

#ifdef KT_PATH_TRACE
size_t kt_path_pop_pure_ending = 0;
size_t kt_path_pop_diff_simple = 0;
size_t kt_path_pop_full_simple = 0;
size_t kt_path_pop_redtrigger  = 0;
size_t kt_path_pop_psize_zero  = 0;
size_t kt_path_pop_calls       = 0;
size_t kt_path_gor_case1 = 0;
size_t kt_path_gor_case2 = 0;
size_t kt_path_gor_case3 = 0;
size_t kt_path_make_small_calls = 0;
size_t kt_path_pop_p1size[6] = {0,0,0,0,0,0};
#endif

/* alloc_link: arena-allocate a fresh chain link with the given depth,
 * tag, buffers, and tail.  Allocates exactly enough room for 2*depth
 * buffers.  cp = chain_pos (level offset). */
static kt_chain_link* alloc_link_t(uint8_t cp, uint8_t depth, kt_color tag,
                                    const kt_buf* bufs,
                                    kt_chain_link* tail) {
    size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
    kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
    L->depth = depth;
    L->tag = (uint8_t)tag;
    L->kind = LINK_FULL;
    L->which = 0;
    L->chain_pos = cp;
    memcpy(L->bufs, bufs, 2 * (size_t)depth * sizeof(kt_buf));
    L->tail = tail;
#ifdef KT_PROFILE
    g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
    g_full_count++;
#endif
    return L;
}

/* alloc_link_uninit: arena-allocate a fresh chain link with the given
 * depth, tag, and tail; bufs[] is left uninitialized for the caller to
 * populate directly.  Saves a redundant buffer copy in green_of_red
 * Cases 2 & 3. */
static inline kt_chain_link* alloc_link_uninit(uint8_t cp, uint8_t depth, kt_color tag,
                                                kt_chain_link* tail) {
    size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
    kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
    L->depth = depth;
    L->tag = (uint8_t)tag;
    L->kind = LINK_FULL;
    L->which = 0;
    L->chain_pos = cp;
    L->tail = tail;
#ifdef KT_PROFILE
    g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
    g_full_count++;
#endif
    return L;
}

/* alloc_diff_uninit: arena-allocate a fresh DIFF link with separate
 * effective tail and base.  base must be a FULL link (K=1 invariant).
 * The override field is left uninitialized.  Size is 64 bytes (vs 96 for
 * FULL depth=1, vs 96+ for FULL depth>=2). */
static inline kt_chain_link_diff* alloc_diff_uninit(uint8_t which, kt_color tag,
                                                    kt_chain_link* eff_tail,
                                                    kt_chain_link* base) {
    kt_chain_link_diff* D = (kt_chain_link_diff*)arena_alloc(sizeof(kt_chain_link_diff));
    D->depth = 0;  /* unused */
    D->tag = (uint8_t)tag;
    D->kind = LINK_DIFF;
    D->which = which;
    D->chain_pos = base->chain_pos;
    D->tail = eff_tail;
    D->base = base;
#ifdef KT_PROFILE
    g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
    g_diff_count++;
#endif
    return D;
}

/* derive the structural color of a link's outer based on buffer sizes.
 * Used for tagging fresh links from non-Case-3 paths. */
static inline kt_color color_from_bufs(const kt_buf* pre, const kt_buf* suf) {
    int ps = (int)buf_size(pre), ss = (int)buf_size(suf);
    /* G: both pre and suf in {B2, B3}.
       R: at least one is B0 or B5.
       Y: anything else (at least one is B1 or B4 but neither is B0/B5). */
    if (ps == 0 || ps == 5 || ss == 0 || ss == 5) return COL_R;
    if ((ps == 2 || ps == 3) && (ss == 2 || ss == 3)) return COL_G;
    return COL_Y;
}

/* alloc_link: same but auto-derives color from outer bufs. */
static kt_chain_link* alloc_link(uint8_t cp, uint8_t depth, const kt_buf* bufs,
                                  kt_chain_link* tail) {
    kt_color c = color_from_bufs(&bufs[0], &bufs[1]);
    return alloc_link_t(cp, depth, c, bufs, tail);
}

/* alloc_link_2: shorthand for the common depth-1 case (pre, suf, tail). */
static inline kt_chain_link* alloc_link_2(uint8_t cp, kt_buf pre, kt_buf suf,
                                          kt_chain_link* tail) {
    kt_buf bb[2];
    bb[0] = pre; bb[1] = suf;
    return alloc_link(cp, 1, bb, tail);
}

/* alloc_ending: depth-1 link with bufs=[b, B0], tail=NULL.  Models
 * Ending(b) in the Viennot chain.  Tag is always G (Endings are green). */
static inline kt_chain_link* alloc_ending(uint8_t cp, kt_buf b) {
    kt_buf bb[2];
    bb[0] = b; bb[1] = buf_empty();
    return alloc_link_t(cp, 1, COL_G, bb, NULL);
}

/* ====================================================================== */
/* Pair / unpair                                                          */
/*                                                                         */
/* Pair-tree flattening (K=2):                                             */
/*   level 0:    kt_elem is a base value pointer.                          */
/*   level 1:    kt_elem is a ptr to a 2-block of level-0 ptrs (16 bytes). */
/*   level 2:    kt_elem is a ptr to a 4-block of level-0 ptrs (32 bytes). */
/*   level >= 3: kt_elem is a ptr to a kt_pair whose left/right are        */
/*               level-(d-1) elements (legacy scheme).                     */
/*                                                                         */
/* pair_make_at(level, x, y):  combine two level-(level-1) elements into   */
/*   one level-`level` element.                                            */
/* pair_split_at(level, e, x, y):  split a level-`level` element into two  */
/*   level-(level-1) elements.                                             */
/*                                                                         */
/* Persistence preserved: split at level <= K (1 or 2) returns offsets     */
/* INTO the original block.  Since the arena never frees, those offsets    */
/* remain valid for the lifetime of the program.                           */
/* ====================================================================== */

/* Legacy heterogeneous pair (used at level >= 3). */
static inline kt_elem kt_pair_make_inline(kt_elem x, kt_elem y) {
    kt_pair* p = (kt_pair*)arena_alloc(sizeof(kt_pair));
    p->left  = x;
    p->right = y;
#ifdef KT_PROFILE
    g_alloc_pairs++;
#endif
    return (kt_elem)p;
}

static inline void kt_pair_split_inline(kt_elem e, kt_elem* x, kt_elem* y) {
    kt_pair* p = (kt_pair*)e;
    *x = p->left;
    *y = p->right;
}

/* pair_make_at: build a level-`level` pair element from two level-(level-1)
 * elements.  At level=1, the result is a flat 2-block (16B).  At level=2,
 * it is a flat 4-block (32B), copied 16B-at-a-time from x and y.  At
 * level>=3, falls back to a kt_pair (16B). */
static inline kt_elem pair_make_at(int level, kt_elem x, kt_elem y) {
    if (__builtin_expect(level == 1, 1)) {
        kt_elem* block = (kt_elem*)arena_alloc(2 * sizeof(kt_elem));
        block[0] = x; block[1] = y;
#ifdef KT_PROFILE
        g_alloc_pairs++;
#endif
        return (kt_elem)block;
    }
    if (level == 2) {
        kt_elem* block = (kt_elem*)arena_alloc(4 * sizeof(kt_elem));
        /* x is a level-1 2-block; copy 16 bytes (2 ptrs).  Same for y. */
        memcpy(block,     x, 2 * sizeof(kt_elem));
        memcpy(block + 2, y, 2 * sizeof(kt_elem));
#ifdef KT_PROFILE
        g_alloc_pairs++;
#endif
        return (kt_elem)block;
    }
    return kt_pair_make_inline(x, y);
}

/* pair_split_at: split a level-`level` element into two level-(level-1)
 * elements.  At level<=K, no allocation: the two outputs alias offsets
 * into the original block.  Persistence preserved (arena never frees). */
static inline void pair_split_at(int level, kt_elem e, kt_elem* x, kt_elem* y) {
    if (__builtin_expect(level == 1, 1)) {
        kt_elem* b = (kt_elem*)e;
        *x = b[0];
        *y = b[1];
        return;
    }
    if (level == 2) {
        /* Both halves point INTO the 32B block.  No allocation. */
        kt_elem* b = (kt_elem*)e;
        *x = (kt_elem)b;        /* first 2 ptrs (level-1 2-block) */
        *y = (kt_elem)(b + 2);  /* last 2 ptrs (level-1 2-block) */
        return;
    }
    kt_pair_split_inline(e, x, y);
}

/* Public-API pair ops: kept for ABI compatibility.  These default to
 * level=3 (kt_pair indirection) since callers don't communicate level. */
kt_elem kt_pair_make(kt_elem x, kt_elem y) {
    return kt_pair_make_inline(x, y);
}

void kt_pair_split(kt_elem e, kt_elem* x, kt_elem* y) {
    kt_pair_split_inline(e, x, y);
}

/* ====================================================================== */
/* Public API: empty                                                      */
/* ====================================================================== */

kt_deque kt_empty(void) { return NULL; }

/* ====================================================================== */
/* Push / Inject                                                          */
/* ====================================================================== */
/* These mirror Viennot's push/make_red/green_of_red, specialized to a
 * flat packet layout.  The cascade INSIDE a packet is in-place on a
 * stack-local kt_buf array (`work`); only when we commit to a final
 * structure do we malloc.
 */

/* Helper: extract the "overflow pair" from a B5 prefix buffer — i.e.,
 * the back two elements — leaving a B3 prefix.  Returns the pair.
 *
 * Layout for a B5 pre [a,b,c,d,e]: Overflow(B3(a,b,c), (d,e)).
 *
 * Currently unused (kept for reference / future use). */
__attribute__((unused))
static inline kt_elem prefix_overflow_pair(kt_buf* b) {
    assert(buf_size(b) == 5);
    kt_elem d = b->e[3], e = b->e[4];
    kt_elem pair = kt_pair_make_inline(d, e);
    /* Re-tag slot 0 with new size 3. */
    b->e[0] = buf_tag(buf_at0(b), 3);
    b->e[3] = NULL; b->e[4] = NULL;
    return pair;
}

/* Helper: extract the "overflow pair" from a B5 suffix buffer — i.e.,
 * the front two elements — leaving a B3 suffix.
 *
 * Layout for a B5 suf [a,b,c,d,e]: Overflow(B3(c,d,e), (a,b)).
 *
 * Currently unused (kept for reference / future use). */
__attribute__((unused))
static inline kt_elem suffix_overflow_pair(kt_buf* b) {
    assert(buf_size(b) == 5);
    kt_elem a = buf_at0(b), bb = b->e[1];
    kt_elem pair = kt_pair_make_inline(a, bb);
    /* Shift left by 2 — keep last 3 elements; new slot 0 is old slot 2 with size tag 3. */
    b->e[0] = buf_tag(b->e[2], 3);
    b->e[1] = b->e[3];
    b->e[2] = b->e[4];
    b->e[3] = NULL; b->e[4] = NULL;
    return pair;
}

/* prefix_decompose category (Viennot): tells the make_small / concat
 * functions whether a buffer is underflowed, ok, or overflowed. */
typedef enum { D_UNDERFLOW, D_OK, D_OVERFLOW } decomp_kind;

/* Construct a green prefix B2/B3 from an optional element + a pair. */
static inline kt_buf prefix23(int has_opt, kt_elem opt, kt_elem b, kt_elem c) {
    if (has_opt) return buf_pair_3(opt, b, c);
    return buf_pair_2(b, c);
}

/* Construct a green suffix B2/B3 from a pair + an optional element. */
static inline kt_buf suffix23(kt_elem a, kt_elem b, int has_opt, kt_elem opt) {
    if (has_opt) return buf_pair_3(a, b, opt);
    return buf_pair_2(a, b);
}

/* prefix_decompose: classify a buffer and extract its info.  Returns
 * the decomp kind; sets *out_green to the green portion (for OK and
 * OVERFLOW) or empty (for UNDERFLOW); sets *out_pair_a, *out_pair_b
 * to the overflow pair (for OVERFLOW); for UNDERFLOW, *out_has_opt
 * indicates whether the buffer has 1 element. */
static decomp_kind prefix_decompose(const kt_buf* b, kt_buf* out_green,
                                     int* out_has_opt, kt_elem* out_opt,
                                     kt_elem* out_pa, kt_elem* out_pb) {
    kt_elem e0 = buf_at0(b);
    switch (buf_size(b)) {
    case 0: *out_has_opt = 0; return D_UNDERFLOW;
    case 1: *out_has_opt = 1; *out_opt = e0; return D_UNDERFLOW;
    case 2: case 3:
        *out_green = *b;
        return D_OK;
    case 4:
        /* B4(a,b,c,d) -> Overflow(B2(a,b), (c,d)) */
        *out_green = buf_pair_2(e0, b->e[1]);
        *out_pa = b->e[2]; *out_pb = b->e[3];
        return D_OVERFLOW;
    case 5:
        /* B5(a,b,c,d,e) -> Overflow(B3(a,b,c), (d,e)) */
        *out_green = buf_pair_3(e0, b->e[1], b->e[2]);
        *out_pa = b->e[3]; *out_pb = b->e[4];
        return D_OVERFLOW;
    }
    /* unreachable */
    return D_UNDERFLOW;
}

/* suffix_decompose: same but for suffixes.  Overflow on B4/B5 takes
 * the FRONT pair as the overflow, leaving the back as green. */
static decomp_kind suffix_decompose(const kt_buf* b, kt_buf* out_green,
                                     int* out_has_opt, kt_elem* out_opt,
                                     kt_elem* out_pa, kt_elem* out_pb) {
    kt_elem e0 = buf_at0(b);
    switch (buf_size(b)) {
    case 0: *out_has_opt = 0; return D_UNDERFLOW;
    case 1: *out_has_opt = 1; *out_opt = e0; return D_UNDERFLOW;
    case 2: case 3:
        *out_green = *b;
        return D_OK;
    case 4:
        /* B4(a,b,c,d) -> Overflow(B2(c,d), (a,b)) */
        *out_green = buf_pair_2(b->e[2], b->e[3]);
        *out_pa = e0; *out_pb = b->e[1];
        return D_OVERFLOW;
    case 5:
        /* B5(a,b,c,d,e) -> Overflow(B3(c,d,e), (a,b)) */
        *out_green = buf_pair_3(b->e[2], b->e[3], b->e[4]);
        *out_pa = e0; *out_pb = b->e[1];
        return D_OVERFLOW;
    }
    return D_UNDERFLOW;
}

/* buffer_unsandwich: split B(2..5) into (first, middle, last); B0/B1
 * becomes "Alone" with optional element. */
typedef struct {
    int kind;          /* 0 = Alone(opt), 1 = Sandwich(a, mid, b) */
    int has_opt;
    kt_elem opt;
    kt_elem first, last;
    kt_buf  mid;
} sandwich_t;

static sandwich_t buffer_unsandwich(const kt_buf* b) {
    sandwich_t s;
    s.mid = buf_empty();
    kt_elem e0 = buf_at0(b);
    switch (buf_size(b)) {
    case 0: s.kind = 0; s.has_opt = 0; return s;
    case 1: s.kind = 0; s.has_opt = 1; s.opt = e0; return s;
    case 2:
        s.kind = 1; s.first = e0; s.last = b->e[1];
        s.mid = buf_empty();
        return s;
    case 3:
        s.kind = 1; s.first = e0; s.last = b->e[2];
        s.mid = buf_singleton(b->e[1]);
        return s;
    case 4:
        s.kind = 1; s.first = e0; s.last = b->e[3];
        s.mid = buf_pair_2(b->e[1], b->e[2]);
        return s;
    case 5:
        s.kind = 1; s.first = e0; s.last = b->e[4];
        s.mid = buf_pair_3(b->e[1], b->e[2], b->e[3]);
        return s;
    }
    return s;
}

/* buffer_halve: convert a buffer of level-(out_level-1) singletons into a
 * buffer of level-out_level pairs.  If odd # of elements, returns the
 * leftover first element separately. */
static void buffer_halve(int out_level, const kt_buf* b,
                          int* has_opt, kt_elem* opt, kt_buf* out_pairs) {
    *out_pairs = buf_empty();
    *has_opt = 0;
    kt_elem e0 = buf_at0(b);
    switch (buf_size(b)) {
    case 0: break;
    case 1: *has_opt = 1; *opt = e0; break;
    case 2:
        *out_pairs = buf_singleton(pair_make_at(out_level, e0, b->e[1]));
        break;
    case 3:
        *has_opt = 1; *opt = e0;
        *out_pairs = buf_singleton(pair_make_at(out_level, b->e[1], b->e[2]));
        break;
    case 4: {
        kt_elem p1 = pair_make_at(out_level, e0, b->e[1]);
        kt_elem p2 = pair_make_at(out_level, b->e[2], b->e[3]);
        *out_pairs = buf_pair_2(p1, p2);
        break;
    }
    case 5: {
        *has_opt = 1; *opt = e0;
        kt_elem p1 = pair_make_at(out_level, b->e[1], b->e[2]);
        kt_elem p2 = pair_make_at(out_level, b->e[3], b->e[4]);
        *out_pairs = buf_pair_2(p1, p2);
        break;
    }
    }
}

/* yellow_push: prepend x to a yellow buffer (B1..B4); result is red on
 * B5.  We just use buf_push since we know the prefix size <= 4. */

/* prefix_rot: prefix_rot x B(...) = (B(... with x prepended (size unchanged), last element).
 * I.e., push x to front, eject from back, return both. */
static void prefix_rot(kt_elem x, const kt_buf* b, kt_buf* out_b, kt_elem* out_back) {
    *out_b = buf_empty();
    int s = (int)buf_size(b);
    if (s == 0) {
        *out_back = x;
        return;
    }
    /* New buf has size s, slot 0 is x; slot i+1 (1<=i<s-1, i.e. 1..s-1) is old slot i.
       Old slot 0 needs unmasking. */
    kt_elem old_e0 = buf_at0(b);
    out_b->e[0] = buf_tag(x, (uint8_t)s);
    out_b->e[1] = old_e0;
    for (int i = 1; i < s - 1; i++) out_b->e[i+1] = b->e[i];
    *out_back = (s == 1) ? old_e0 : b->e[s - 1];
}

/* suffix_rot: inject x to back, pop front, return both. */
static void suffix_rot(const kt_buf* b, kt_elem x, kt_elem* out_front, kt_buf* out_b) {
    *out_b = buf_empty();
    int s = (int)buf_size(b);
    if (s == 0) {
        *out_front = x;
        return;
    }
    /* Shift left: pop front (slot 0), inject x at slot s-1.
       New buf has the same size s; slot 0 is the old slot 1 (untagged) tagged. */
    *out_front = buf_at0(b);
    if (s == 1) {
        out_b->e[0] = buf_tag(x, 1);
        return;
    }
    out_b->e[0] = buf_tag(b->e[1], (uint8_t)s);
    for (int i = 1; i < s - 1; i++) out_b->e[i] = b->e[i+1];
    out_b->e[s - 1] = x;
}

/* ====================================================================== */
/* make_small: handle the depth=1, tail=NULL case of green_of_red.        */
/* See Viennot's `make_small p1 b2 s1`: produces a fresh green chain     */
/* given a 1-level packet's pre/suf and the deeper buffer (which is B0  */
/* in our case since tail=NULL is "Ending B0" implicit).                  */
/* ====================================================================== */

/* make_small builds a fresh chain from (p1, b2, s1).  In our usage
 * b2 = B0 (since tail==NULL means the implicit deeper buffer is empty).
 * cp is the chain_pos of the link being replaced; p1 and s1 hold elements
 * at level cp, b2 holds elements at level cp+1.  Pairs made/split between
 * outer (cp) and b2 (cp+1) are at level cp+1; pairs made by buffer_halve
 * (consuming b2's level-(cp+1) singletons) are at level cp+2.
 * Returns the head of the new chain (also at chain_pos cp). */
static kt_chain_link* make_small(uint8_t cp, kt_buf p1, kt_buf b2, kt_buf s1) {
    int lvl1 = (int)cp + 1;  /* boundary level for pairs between p1/s1 and b2 */
    kt_buf p1g, s1g; /* green parts */
    int p1_has_opt = 0, s1_has_opt = 0;
    kt_elem p1_opt = NULL, s1_opt = NULL;
    kt_elem p1_pa = NULL, p1_pb = NULL;
    kt_elem s1_pa = NULL, s1_pb = NULL;

    decomp_kind dp = prefix_decompose(&p1, &p1g, &p1_has_opt, &p1_opt,
                                       &p1_pa, &p1_pb);
    decomp_kind ds = suffix_decompose(&s1, &s1g, &s1_has_opt, &s1_opt,
                                       &s1_pa, &s1_pb);

    /* 9 cases, mirroring Viennot's match. */
    if (dp == D_UNDERFLOW && ds == D_UNDERFLOW) {
        /* Both underflow.  Use buffer_unsandwich on b2. */
        sandwich_t sw = buffer_unsandwich(&b2);
        if (sw.kind == 0) {
            /* Alone(opt): construct an Ending(small) directly. */
            int p = p1_has_opt, m = sw.has_opt, s = s1_has_opt;
            kt_buf out;
            if (!p && !m && !s) {
                /* Empty deque. */
                return NULL;
            }
            if (p && !m && !s) out = buf_singleton(p1_opt);
            else if (!p && !m && s) out = buf_singleton(s1_opt);
            else if (p && !m && s) out = buf_pair_2(p1_opt, s1_opt);
            else if (!p && m && !s) {
                /* Some(a,b): unpack the pair. */
                kt_elem a, b; pair_split_at(lvl1, sw.opt, &a, &b);
                out = buf_pair_2(a, b);
            }
            else if (p && m && !s) {
                kt_elem a, b; pair_split_at(lvl1, sw.opt, &a, &b);
                out = buf_pair_3(p1_opt, a, b);
            }
            else if (!p && m && s) {
                kt_elem a, b; pair_split_at(lvl1, sw.opt, &a, &b);
                out = buf_pair_3(a, b, s1_opt);
            }
            else { /* p && m && s */
                kt_elem a, b; pair_split_at(lvl1, sw.opt, &a, &b);
                out = buf_empty();
                /* B4(p1_opt, a, b, s1_opt). */
                out.e[0] = buf_tag(p1_opt, 4);
                out.e[1] = a; out.e[2] = b; out.e[3] = s1_opt;
            }
            return alloc_ending(cp, out);
        } else {
            /* Sandwich(ab, rest, cd): pair-unpack. */
            kt_elem la, lb;
            pair_split_at(lvl1, sw.first, &la, &lb);
            kt_elem ra, rb;
            pair_split_at(lvl1, sw.last, &ra, &rb);
            kt_buf new_pre = prefix23(p1_has_opt, p1_opt, la, lb);
            kt_buf new_suf = suffix23(ra, rb, s1_has_opt, s1_opt);
            /* Result: Chain(G, Packet(new_pre, Hole, new_suf), Ending(rest)). */
            return alloc_link_2(cp, new_pre, new_suf,
                                 alloc_ending((uint8_t)(cp + 1), sw.mid));
        }
    }

    if (dp == D_UNDERFLOW && ds == D_OK) {
        /* p1 underflow, s1 ok.  Use buffer_pop on b2. */
        if (buf_size(&b2) == 0) {
            if (!p1_has_opt) {
                /* Just s1g as Ending. */
                return alloc_ending(cp, s1g);
            } else {
                /* buffer_push p1_opt s1g. */
                kt_buf res;
                if (!buf_push(p1_opt, &s1g, &res)) return NULL;
                /* res may be B5 (push to B4 yields B5).  Per Viennot's
                   buffer_push, push to B4 stays as Ending(B5).  Only push
                   to B5 (size 6 logically) splits into a chain.  Since
                   our res.size <= 5, we just stay as Ending(res). */
                return alloc_ending(cp, res);
            }
        } else {
            /* buffer_pop b2: extract first pair (cd) from b2. */
            kt_buf b2_rest;
            kt_elem cd_pair;
            buf_pop(&b2, &cd_pair, &b2_rest);
            kt_elem c, d;
            pair_split_at(lvl1, cd_pair, &c, &d);
            kt_buf new_pre = prefix23(p1_has_opt, p1_opt, c, d);
            return alloc_link_2(cp, new_pre, s1g,
                                 alloc_ending((uint8_t)(cp + 1), b2_rest));
        }
    }

    if (dp == D_UNDERFLOW && ds == D_OVERFLOW) {
        /* p1 underflow, s1 overflow.  s1's overflow pair is at the front
         * (s1_pa, s1_pb).  suffix_rot(b2, ab) -> (front, center). */
        kt_elem ab = pair_make_at(lvl1, s1_pa, s1_pb);
        kt_elem cd_front;
        kt_buf  center;
        suffix_rot(&b2, ab, &cd_front, &center);
        kt_elem c, d; pair_split_at(lvl1, cd_front, &c, &d);
        kt_buf new_pre = prefix23(p1_has_opt, p1_opt, c, d);
        return alloc_link_2(cp, new_pre, s1g,
                             alloc_ending((uint8_t)(cp + 1), center));
    }

    if (dp == D_OK && ds == D_UNDERFLOW) {
        if (buf_size(&b2) == 0) {
            if (!s1_has_opt) {
                return alloc_ending(cp, p1g);
            } else {
                /* buffer_inject p1g s1_opt. */
                kt_buf res;
                if (!buf_inject(&p1g, s1_opt, &res)) return NULL;
                return alloc_ending(cp, res);
            }
        } else {
            /* buffer_eject b2: extract last pair (ab). */
            kt_buf b2_rest;
            kt_elem ab_pair;
            buf_eject(&b2, &b2_rest, &ab_pair);
            kt_elem a, b; pair_split_at(lvl1, ab_pair, &a, &b);
            kt_buf new_suf = suffix23(a, b, s1_has_opt, s1_opt);
            return alloc_link_2(cp, p1g, new_suf,
                                 alloc_ending((uint8_t)(cp + 1), b2_rest));
        }
    }

    if (dp == D_OK && ds == D_OK) {
        /* Both green.  Result: Chain(G, Packet(p1g, Hole, s1g), Ending b2). */
        return alloc_link_2(cp, p1g, s1g,
                             alloc_ending((uint8_t)(cp + 1), b2));
    }

    if (dp == D_OK && ds == D_OVERFLOW) {
        /* s1 overflow: inject pair into b2. */
        kt_elem ab = pair_make_at(lvl1, s1_pa, s1_pb);
        if (buf_size(&b2) <= 4) {
            kt_buf b2_new;
            buf_inject(&b2, ab, &b2_new);
            return alloc_link_2(cp, p1g, s1g,
                                 alloc_ending((uint8_t)(cp + 1), b2_new));
        }
        /* b2 already B5: buffer_inject B5(a,b,c,d,e) ab = Chain(G, Packet(B3(a,b,c), Hole, B3(d,e,ab)), Ending B0). */
        kt_buf np2 = buf_pair_3(buf_at0(&b2), b2.e[1], b2.e[2]);
        kt_buf ns2 = buf_pair_3(b2.e[3], b2.e[4], ab);
        kt_chain_link* deeper =
            alloc_link_2((uint8_t)(cp + 1), np2, ns2,
                          alloc_ending((uint8_t)(cp + 2), buf_empty()));
        return alloc_link_2(cp, p1g, s1g, deeper);
    }

    if (dp == D_OVERFLOW && ds == D_UNDERFLOW) {
        /* p1 overflow (pair cd at back), s1 underflow.  prefix_rot cd b2. */
        kt_elem cd = pair_make_at(lvl1, p1_pa, p1_pb);
        kt_buf  center;
        kt_elem ab;
        prefix_rot(cd, &b2, &center, &ab);
        kt_elem a, b; pair_split_at(lvl1, ab, &a, &b);
        kt_buf new_suf = suffix23(a, b, s1_has_opt, s1_opt);
        return alloc_link_2(cp, p1g, new_suf,
                             alloc_ending((uint8_t)(cp + 1), center));
    }

    if (dp == D_OVERFLOW && ds == D_OK) {
        /* p1 overflow: push pair onto b2 (front). */
        kt_elem cd = pair_make_at(lvl1, p1_pa, p1_pb);
        if (buf_size(&b2) <= 4) {
            kt_buf b2_new;
            buf_push(cd, &b2, &b2_new);
            return alloc_link_2(cp, p1g, s1g,
                                 alloc_ending((uint8_t)(cp + 1), b2_new));
        }
        /* b2 is B5: buffer_push cd B5(a,b,c,d,e) = Chain(G, Packet(B3(cd,a,b), Hole, B3(c,d,e)), Ending B0). */
        kt_buf np = buf_pair_3(cd, buf_at0(&b2), b2.e[1]);
        kt_buf ns = buf_pair_3(b2.e[2], b2.e[3], b2.e[4]);
        kt_chain_link* deeper =
            alloc_link_2((uint8_t)(cp + 1), np, ns,
                          alloc_ending((uint8_t)(cp + 2), buf_empty()));
        return alloc_link_2(cp, p1g, s1g, deeper);
    }

    /* dp == D_OVERFLOW && ds == D_OVERFLOW. */
    {
        kt_elem cd = pair_make_at(lvl1, p1_pa, p1_pb);
        kt_elem ab = pair_make_at(lvl1, s1_pa, s1_pb);
        int has_x = 0; kt_elem x = NULL; kt_buf rest;
        /* buffer_halve consumes b2 (level cp+1) and outputs pairs at level cp+2. */
        buffer_halve(lvl1 + 1, &b2, &has_x, &x, &rest);
        kt_buf p2;
        if (has_x) p2 = buf_pair_2(cd, x);
        else       p2 = buf_singleton(cd);
        kt_buf s2 = buf_singleton(ab);
        /* Chain(G, Packet(p1g, Packet(p2, Hole, s2), s1g), Ending rest):
           one chain link with depth=2, bufs=[p1g, s1g, p2, s2], tail=Ending(rest). */
        kt_buf bb[4];
        bb[0] = p1g; bb[1] = s1g; bb[2] = p2; bb[3] = s2;
        return alloc_link(cp, 2, bb,
                           alloc_ending((uint8_t)(cp + 2), rest));
    }
}

/* ====================================================================== */
/* green_prefix_concat / green_suffix_concat / prefix_concat / suffix_concat */
/* ====================================================================== */

/* These are the Viennot helpers used in green_of_red Cases 2 & 3.  They
 * adjust two adjacent buffers (one outer, one yellow) so the outer
 * becomes green and the yellow stays yellow.
 *
 * green_prefix_concat b1 b2: b1 any color, b2 green pair-buf.  Returns
 * (b1' green, b2' yellow).
 *
 * prefix_concat: same but b2 is yellow not green; result allows red b2'. */

/* green_pop / green_eject / yellow_pop / yellow_eject: thin wrappers over
   buf_pop / buf_eject.  The original specialized versions were size-class
   specific to enable tighter codegen, but with the packed encoding the
   tag-bit handling is centralized in buf_pop / buf_eject and re-doing it
   here would just duplicate the masking logic. */
static inline void green_pop(const kt_buf* b, kt_elem* out_x, kt_buf* out_rest) {
    buf_pop(b, out_x, out_rest);
}
static inline void green_eject(const kt_buf* b, kt_buf* out_rest, kt_elem* out_x) {
    buf_eject(b, out_rest, out_x);
}
static inline void yellow_pop(const kt_buf* b, kt_elem* out_x, kt_buf* out_rest) {
    buf_pop(b, out_x, out_rest);
}
static inline void yellow_eject(const kt_buf* b, kt_buf* out_rest, kt_elem* out_x) {
    buf_eject(b, out_rest, out_x);
}

/* green_push x b: b is green B2/B3, prepend x — result is B3/B4 yellow. */
static inline kt_buf green_push(kt_elem x, const kt_buf* b) {
    kt_buf out; buf_push(x, b, &out); return out;
}

/* green_inject b x: b is green B2/B3, append x — result is B3/B4 yellow. */
static inline kt_buf green_inject(const kt_buf* b, kt_elem x) {
    kt_buf out; buf_inject(b, x, &out); return out;
}

/* yellow_push x b: b is yellow B1..B4, prepend x — result is B2..B5. */
static inline kt_buf yellow_push(kt_elem x, const kt_buf* b) {
    kt_buf out; buf_push(x, b, &out); return out;
}

/* yellow_inject b x. */
static inline kt_buf yellow_inject(const kt_buf* b, kt_elem x) {
    kt_buf out; buf_inject(b, x, &out); return out;
}

/* green_prefix_concat b1 b2: b1 any color (the OUTER buffer of the red top,
 * elements at level (level-1)), b2 green pair buffer (the OUTER buffer of
 * the green successor, elements at level `level`).  The pair traffic
 * between them is at level `level`. */
static inline void green_prefix_concat(int level,
                                        const kt_buf* restrict b1,
                                        const kt_buf* restrict b2,
                                        kt_buf* restrict out_b1,
                                        kt_buf* restrict out_b2) {
    kt_buf b1g; int has_opt = 0; kt_elem opt = NULL;
    kt_elem pa = NULL, pb = NULL;
    decomp_kind d = prefix_decompose(b1, &b1g, &has_opt, &opt, &pa, &pb);
    switch (d) {
    case D_UNDERFLOW: {
        kt_elem ab; kt_buf b2_rest;
        green_pop(b2, &ab, &b2_rest);
        kt_elem a, b; pair_split_at(level, ab, &a, &b);
        *out_b1 = prefix23(has_opt, opt, a, b);
        *out_b2 = b2_rest;
        return;
    }
    case D_OK:
        *out_b1 = b1g;
        *out_b2 = *b2;  /* to_yellow is identity at the C level. */
        return;
    case D_OVERFLOW: {
        kt_elem ab = pair_make_at(level, pa, pb);
        *out_b1 = b1g;
        *out_b2 = green_push(ab, b2);
        return;
    }
    }
}

/* green_suffix_concat b1 b2: b1 green pair buf (OUTER of green successor),
 * b2 any color (OUTER suf of red top).  level = pair-traffic level. */
static inline void green_suffix_concat(int level,
                                        const kt_buf* restrict b1,
                                        const kt_buf* restrict b2,
                                        kt_buf* restrict out_b1,
                                        kt_buf* restrict out_b2) {
    kt_buf b2g; int has_opt = 0; kt_elem opt = NULL;
    kt_elem pa = NULL, pb = NULL;
    decomp_kind d = suffix_decompose(b2, &b2g, &has_opt, &opt, &pa, &pb);
    switch (d) {
    case D_UNDERFLOW: {
        kt_buf b1_rest; kt_elem ab;
        green_eject(b1, &b1_rest, &ab);
        kt_elem a, b; pair_split_at(level, ab, &a, &b);
        *out_b1 = b1_rest;
        *out_b2 = suffix23(a, b, has_opt, opt);
        return;
    }
    case D_OK:
        *out_b1 = *b1;
        *out_b2 = b2g;
        return;
    case D_OVERFLOW: {
        kt_elem ab = pair_make_at(level, pa, pb);
        *out_b1 = green_inject(b1, ab);
        *out_b2 = b2g;
        return;
    }
    }
}

/* prefix_concat b1 b2: b1 any color (outer red top pre), b2 yellow pair buf
 * (next-yellow level pre).  level = pair-traffic level. */
static inline void prefix_concat(int level,
                                  const kt_buf* restrict b1,
                                  const kt_buf* restrict b2,
                                  kt_buf* restrict out_b1,
                                  kt_buf* restrict out_b2) {
    kt_buf b1g; int has_opt = 0; kt_elem opt = NULL;
    kt_elem pa = NULL, pb = NULL;
    decomp_kind d = prefix_decompose(b1, &b1g, &has_opt, &opt, &pa, &pb);
    switch (d) {
    case D_UNDERFLOW: {
        kt_elem ab; kt_buf b2_rest;
        yellow_pop(b2, &ab, &b2_rest);
        kt_elem a, b; pair_split_at(level, ab, &a, &b);
        *out_b1 = prefix23(has_opt, opt, a, b);
        *out_b2 = b2_rest;
        return;
    }
    case D_OK:
        *out_b1 = b1g;
        *out_b2 = *b2;  /* to_red = identity at C level. */
        return;
    case D_OVERFLOW: {
        kt_elem ab = pair_make_at(level, pa, pb);
        *out_b1 = b1g;
        *out_b2 = yellow_push(ab, b2);
        return;
    }
    }
}

/* suffix_concat b1 b2: b1 yellow pair buf, b2 any color outer suf. */
static inline void suffix_concat(int level,
                                  const kt_buf* restrict b1,
                                  const kt_buf* restrict b2,
                                  kt_buf* restrict out_b1,
                                  kt_buf* restrict out_b2) {
    kt_buf b2g; int has_opt = 0; kt_elem opt = NULL;
    kt_elem pa = NULL, pb = NULL;
    decomp_kind d = suffix_decompose(b2, &b2g, &has_opt, &opt, &pa, &pb);
    switch (d) {
    case D_UNDERFLOW: {
        kt_buf b1_rest; kt_elem ab;
        yellow_eject(b1, &b1_rest, &ab);
        kt_elem a, b; pair_split_at(level, ab, &a, &b);
        *out_b1 = b1_rest;
        *out_b2 = suffix23(a, b, has_opt, opt);
        return;
    }
    case D_OK:
        *out_b1 = *b1;
        *out_b2 = b2g;
        return;
    case D_OVERFLOW: {
        kt_elem ab = pair_make_at(level, pa, pb);
        *out_b1 = yellow_inject(b1, ab);
        *out_b2 = b2g;
        return;
    }
    }
}

/* ====================================================================== */
/* green_of_red: the central rebalancing primitive.                        */
/* ====================================================================== */

/* Apply green_of_red to a chain whose head is `top` and whose top
 * packet is RED (outer pre or outer suf is overflow/underflow, depending
 * on which op triggered it).  Returns the head of the fixed chain.
 *
 * The 3 cases mirror Viennot directly. */
static kt_chain_link* green_of_red(kt_chain_link* top) {
    /* Inputs: top->depth, top->bufs, top->tail.
       cp = top's chain_pos (level offset of top's outer bufs).
       Pair traffic at the top↔inner level boundary is at level cp+1. */
    uint8_t cp = top->chain_pos;
    int lvl1 = (int)cp + 1;
    if (top->depth == 1 && top->tail == NULL) {
#ifdef KT_PATH_TRACE
        kt_path_gor_case1++; kt_path_make_small_calls++;
#endif
        /* Case 1: depth=1, tail=NULL -> make_small with b2=B0. */
        return make_small(cp, PRE(top, 0), buf_empty(), SUF(top, 0));
    }
    if (top->depth == 1) {
#ifdef KT_PATH_TRACE
        kt_path_gor_case2++;
#endif
        /* Case 2: depth=1, tail!=NULL.
           Tail is GREEN by regularity.  We merge top's outer with tail's
           outer.  tl may be a DIFF (G/Y); use helpers to read effective
           depth, tail, and bufs. */
        kt_chain_link* tl = top->tail;
        /* Regularity invariant (KT99): if top is RED, its tail is GREEN.
           If this assert ever fires, regularity preservation is broken
           somewhere upstream — DO NOT add a recursive fallback; fix the
           upstream op. */
        assert(tl->tag == COL_G && "Case 2: tail must be GREEN by regularity");
        uint8_t tl_depth = link_depth(tl);
        const kt_buf* tl_pre = link_outer_pre(tl);
        const kt_buf* tl_suf = link_outer_suf(tl);
        kt_chain_link* tl_tail = link_tail(tl);
        if (tl_depth == 1 && tl_tail == NULL && buf_size(tl_suf) == 0) {
            /* Tail is a PURE Ending(buf): bufs[0] is the only buffer.
                 Chain(R, Packet(p1, Hole, s1), Ending buf) -> make_small p1 buf s1.
               */
            return make_small(cp, PRE(top, 0), *tl_pre, SUF(top, 0));
        }
        /* Tail is a ChainCons: tl has depth>=1 (not pure Ending) OR depth=1
           with non-NULL tail.  Apply green_prefix_concat / green_suffix_concat. */
        uint8_t new_depth = (uint8_t)(1 + tl_depth);
        if (__builtin_expect(new_depth > MAX_PACKET_DEPTH, 0)) return NULL;
        /* Allocate uninit link, fill its bufs[] in place.
           green_prefix_concat / green_suffix_concat always return green
           (B2/B3) outers, so the result tag is always COL_G. */
        kt_chain_link* L = alloc_link_uninit(cp, new_depth, COL_G, tl_tail);
        green_prefix_concat(lvl1, &top->bufs[0], tl_pre, &L->bufs[0], &L->bufs[2]);
        green_suffix_concat(lvl1, tl_suf, &top->bufs[1], &L->bufs[3], &L->bufs[1]);
        if (__builtin_expect(tl_depth > 1, 0)) {
            /* Deeper bufs come from tl's underlying FULL.  For DIFF, that's
               tl->tail (which == base FULL).  For FULL, it's just tl. */
            const kt_chain_link* tl_full = link_as_full(tl);
            memcpy(&L->bufs[4], &tl_full->bufs[2],
                   (size_t)(tl_depth - 1) * 2 * sizeof(kt_buf));
        }
        return L;
    }
#ifdef KT_PATH_TRACE
    kt_path_gor_case3++;
#endif
    /* Case 3: depth >= 2.  Peel the outer level off and re-thread inner level
       as a new red chain link. */
    /* Original packet: Packet(p1, Packet(p2, child, s2), s1) where p2 = PRE(top,1),
       s2 = SUF(top,1), child = packet-of-deeper-levels (Hole or non-Hole). */
    /* Regularity invariant: if top is RED with depth>=2, its tail (if any)
       must be GREEN.  The new R link inherits this tail; chain invariant
       (Y/R -> G) requires its tail to be G.  If this fires, fix upstream. */
    assert((top->tail == NULL || top->tail->tag == COL_G) &&
           "Case 3: original tail must be GREEN — new R link inherits it");
    kt_buf new_p1, new_p2, new_s1, new_s2;
    prefix_concat(lvl1, &top->bufs[0], &top->bufs[2], &new_p1, &new_p2);
    suffix_concat(lvl1, &top->bufs[3], &top->bufs[1], &new_s2, &new_s1);
    /* Result: Chain(G, Packet(new_p1, Hole, new_s1),
                     Chain(R, Packet(new_p2, child=top_inner, new_s2), top_tail)).
       In flat form:
         new_top: depth=1, bufs=[new_p1, new_s1], tail = new_red_link.
         new_red_link: depth = top.depth - 1, bufs = [new_p2, new_s2, top.bufs[4..]], tail = top.tail.
       new_top has chain_pos cp; new_red_link has chain_pos cp+1 (since new_top has depth=1). */
    uint8_t new_red_depth = (uint8_t)(top->depth - 1);
    /* Tag the inner link as R per Viennot's Case 3 result.
       Direct-write into the malloc'd link to skip the kt_buf bb[] copy. */
    kt_chain_link* new_red_link =
        alloc_link_uninit((uint8_t)(cp + 1), new_red_depth, COL_R, top->tail);
    new_red_link->bufs[0] = new_p2;
    new_red_link->bufs[1] = new_s2;
    if (new_red_depth > 1) {
        memcpy(&new_red_link->bufs[2], &top->bufs[4],
               (size_t)(new_red_depth - 1) * 2 * sizeof(kt_buf));
    }
    /* The new red link could itself be "red" structurally (its outer pre
       is potentially B5 after prefix_concat).  Per Viennot, this is OK:
       the chain invariant Y/R -> G is maintained because top->tail (the
       new red link's tail) is green by the original invariant. */

    kt_color new_top_tag = color_from_bufs(&new_p1, &new_s1);
    kt_chain_link* new_top = alloc_link_uninit(cp, 1, new_top_tag, new_red_link);
    new_top->bufs[0] = new_p1;
    new_top->bufs[1] = new_s1;
    return new_top;
}

/* ====================================================================== */
/* ensure_green: if the link's tag is R, run green_of_red.  Otherwise     */
/* (G or Y), return as-is.  Per Viennot, ensure_green's input is restricted */
/* to noyellow (G or R), but the typing happens at our caller.             */
/*                                                                         */
/* NOTE: Currently unused — the call sites in kt_push/inject/pop/eject     */
/* inline the cheap (top->tail == NULL || top->tail->tag != COL_R) check   */
/* and call green_of_red directly when needed, saving a function call in   */
/* the hot path.  Kept for reference / future use.                         */
/* ====================================================================== */
__attribute__((unused))
static kt_chain_link* ensure_green(kt_chain_link* L) {
    if (L != NULL && L->tag == COL_R) return green_of_red(L);
    return L;
}

/* ====================================================================== */
/* push                                                                    */
/* ====================================================================== */

kt_deque kt_push(kt_elem x, kt_deque d) {
    kt_chain_link* top = (kt_chain_link*)d;
    if (top == NULL) {
        return (kt_deque)alloc_ending(0, buf_singleton(x));
    }
    /* Check if top is the pure Ending(buf) form: depth=1, tail=NULL,
       bufs[1] empty.  Then push to bufs[0] with possibly B5 split. */
    if (top->depth == 1 && top->tail == NULL && buf_size(&SUF(top, 0)) == 0) {
        kt_buf old = PRE(top, 0);
        if (buf_size(&old) <= 4) {
            kt_buf newb;
            buf_push(x, &old, &newb);
            return (kt_deque)alloc_ending(top->chain_pos, newb);
        }
        /* old is B5: buffer_push x B5 = Chain(G, Packet(B3(x,a,b), Hole, B3(c,d,e)), Ending B0).
           cp(head)=top->chain_pos, cp(ending)=top->chain_pos+1. */
        kt_elem o0 = buf_at0(&old);
        kt_buf np = buf_pair_3(x, o0, old.e[1]);
        kt_buf ns = buf_pair_3(old.e[2], old.e[3], old.e[4]);
        return (kt_deque)alloc_link_2(top->chain_pos, np, ns,
                                        alloc_ending((uint8_t)(top->chain_pos + 1),
                                                       buf_empty()));
    }

    /* Top is a chain link with depth>=1.  Push x onto effective outer pre.
       If outer pre size was <=3: result <=4, no red trigger — rebuild.
       If outer pre size was 4: result is B5 (red) — trigger green_of_red.
       (Size 5 should never occur as we maintain the invariant.) */
    const kt_buf* p1 = link_outer_pre(top);
    int p1_sz = (int)buf_size(p1);
    if (__builtin_expect(p1_sz >= 5, 0)) return NULL;
    if (__builtin_expect(p1_sz <= 3, 1)) {
        /* Simple rebuild: result has size p1_sz+1 in {1..4}, never red. */
        kt_chain_link* eff_tail = link_tail(top);
        kt_chain_link* fixed_tail =
            (eff_tail == NULL || eff_tail->tag != COL_R)
                ? eff_tail
                : green_of_red(eff_tail);
        uint8_t depth = link_depth(top);
        /* Diff-link encoding: allocate a DIFF when possible.  Cases:
           - top is FULL: DIFF over top, which=PRE, override=new_pre.
           - top is DIFF with which=PRE: re-base — DIFF over top->base
             with which=PRE, override=new_pre.  The old override is
             dropped; the new one is the *current* effective pre after the
             push.  Suf and deeper come from base (same as before).
           - top is DIFF with which=SUF: cannot re-base without losing
             the suf override.  Must materialize to FULL. */
        int top_is_diff = (top->kind == LINK_DIFF);
        int top_which_is_pre = top_is_diff
            ? (((const kt_chain_link_diff*)top)->which == 0)
            : 0;
        if (__builtin_expect(!top_is_diff || top_which_is_pre, 1)) {
            const kt_chain_link* base = link_as_full(top);
            const kt_buf* suf_in_base = &base->bufs[1];
            kt_color tag;
            int new_p_sz = p1_sz + 1;
            int ss = (int)buf_size(suf_in_base);
            if (new_p_sz == 5 || ss == 0 || ss == 5) tag = COL_R;
            else if ((new_p_sz == 2 || new_p_sz == 3) && (ss == 2 || ss == 3)) tag = COL_G;
            else tag = COL_Y;
            kt_chain_link_diff* D = alloc_diff_uninit(0, tag, fixed_tail,
                                                      (kt_chain_link*)base);
            D->override.e[0] = buf_tag(x, (uint8_t)new_p_sz);
            D->override.e[1] = buf_at0(p1);
            D->override.e[2] = p1->e[1];
            D->override.e[3] = p1->e[2];
            D->override.e[4] = p1->e[3];
            return (kt_deque)D;
        }
        /* Top is DIFF with which=SUF; new op modifies pre.  Materialize a
           FULL with the new pre AND the existing suf override. */
        size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
        kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
        L->depth = depth;
        L->kind = LINK_FULL;
        L->which = 0;
        L->chain_pos = top->chain_pos;
        L->tail = fixed_tail;
        L->bufs[0].e[0] = buf_tag(x, (uint8_t)(p1_sz + 1));
        L->bufs[0].e[1] = buf_at0(p1);
        L->bufs[0].e[2] = p1->e[1];
        L->bufs[0].e[3] = p1->e[2];
        L->bufs[0].e[4] = p1->e[3];
        /* Suf is the override of the old DIFF (link_outer_suf reads it). */
        L->bufs[1] = *link_outer_suf(top);
        if (__builtin_expect(depth > 1, 0)) {
            const kt_chain_link* base = link_as_full(top);
            memcpy(&L->bufs[2], &base->bufs[2],
                   (size_t)(depth - 1) * 2 * sizeof(kt_buf));
        }
        L->tag = (uint8_t)color_from_bufs(&L->bufs[0], &L->bufs[1]);
#ifdef KT_PROFILE
        g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
        g_full_count++;
#endif
        return (kt_deque)L;
    }
    /* p1_sz == 4: pushing yields B5, red trigger.  Build a virtual top on
       the stack and run green_of_red.  depth>=2 is exceptional. */
    kt_buf p1_new;
    buf_push(x, p1, &p1_new);
    char vbuf[sizeof(kt_chain_link) + 2 * MAX_PACKET_DEPTH * sizeof(kt_buf)];
    kt_chain_link* virt = (kt_chain_link*)vbuf;
    uint8_t v_depth = link_depth(top);
    virt->depth = v_depth;
    virt->tag = top->tag;
    virt->kind = LINK_FULL;
    virt->which = 0;
    virt->chain_pos = top->chain_pos;
    virt->tail = link_tail(top);
    if (__builtin_expect(top->kind == LINK_FULL && v_depth == 1, 1)) {
        virt->bufs[0] = p1_new;
        virt->bufs[1] = top->bufs[1];
    } else if (top->kind == LINK_FULL) {
        memcpy(virt->bufs, top->bufs, (size_t)(2 * v_depth) * sizeof(kt_buf));
        virt->bufs[0] = p1_new;
    } else {
        /* DIFF top: outer pre is now p1_new; outer suf from helper; deeper from base. */
        virt->bufs[0] = p1_new;
        virt->bufs[1] = *link_outer_suf(top);
        if (__builtin_expect(v_depth > 1, 0)) {
            const kt_chain_link* _base = link_as_full(top);
            memcpy(&virt->bufs[2], &_base->bufs[2],
                   (size_t)(v_depth - 1) * 2 * sizeof(kt_buf));
        }
    }
    return (kt_deque)green_of_red(virt);
}

/* ====================================================================== */
/* inject                                                                  */
/* ====================================================================== */

kt_deque kt_inject(kt_deque d, kt_elem x) {
    kt_chain_link* top = (kt_chain_link*)d;
    if (top == NULL) {
        return (kt_deque)alloc_ending(0, buf_singleton(x));
    }
    /* Pure Ending(b) form: inject into bufs[0]. */
    if (top->depth == 1 && top->tail == NULL && buf_size(&SUF(top, 0)) == 0) {
        kt_buf old = PRE(top, 0);
        if (buf_size(&old) <= 4) {
            kt_buf newb;
            buf_inject(&old, x, &newb);
            return (kt_deque)alloc_ending(top->chain_pos, newb);
        }
        /* old is B5: buffer_inject B5 x = Chain(G, Packet(B3(a,b,c), Hole, B3(d,e,x)), Ending B0). */
        kt_buf np = buf_pair_3(buf_at0(&old), old.e[1], old.e[2]);
        kt_buf ns = buf_pair_3(old.e[3], old.e[4], x);
        return (kt_deque)alloc_link_2(top->chain_pos, np, ns,
                                        alloc_ending((uint8_t)(top->chain_pos + 1),
                                                       buf_empty()));
    }
    /* Inject into outer suf. */
    const kt_buf* s1 = link_outer_suf(top);
    int s1_sz = (int)buf_size(s1);
    if (__builtin_expect(s1_sz >= 5, 0)) return NULL;
    if (__builtin_expect(s1_sz <= 3, 1)) {
        /* Result has size s1_sz+1 in {1..4}, never red. */
        kt_chain_link* eff_tail = link_tail(top);
        kt_chain_link* fixed_tail =
            (eff_tail == NULL || eff_tail->tag != COL_R)
                ? eff_tail
                : green_of_red(eff_tail);
        uint8_t depth = link_depth(top);
        int top_is_diff = (top->kind == LINK_DIFF);
        int top_which_is_suf = top_is_diff
            ? (((const kt_chain_link_diff*)top)->which == 1)
            : 0;
        if (__builtin_expect(!top_is_diff || top_which_is_suf, 1)) {
            /* Re-base or fresh DIFF over FULL. */
            const kt_chain_link* base = link_as_full(top);
            const kt_buf* pre_in_base = &base->bufs[0];
            int new_s_sz = s1_sz + 1;
            int ps = (int)buf_size(pre_in_base);
            kt_color tag;
            if (ps == 0 || ps == 5 || new_s_sz == 5) tag = COL_R;
            else if ((ps == 2 || ps == 3) && (new_s_sz == 2 || new_s_sz == 3)) tag = COL_G;
            else tag = COL_Y;
            kt_chain_link_diff* D = alloc_diff_uninit(1, tag, fixed_tail,
                                                      (kt_chain_link*)base);
            if (s1_sz == 0) {
                D->override = buf_singleton(x);
            } else {
                D->override.e[0] = buf_tag(buf_at0(s1), (uint8_t)new_s_sz);
                D->override.e[1] = s1->e[1];
                D->override.e[2] = s1->e[2];
                D->override.e[3] = s1->e[3];
                D->override.e[4] = s1->e[4];
                ((kt_elem*)&D->override)[s1_sz] = x;
            }
            return (kt_deque)D;
        }
        /* Top is DIFF with which=PRE; new op modifies suf.  Materialize FULL. */
        size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
        kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
        L->depth = depth;
        L->kind = LINK_FULL;
        L->which = 0;
        L->chain_pos = top->chain_pos;
        L->tail = fixed_tail;
        L->bufs[0] = *link_outer_pre(top);
        if (s1_sz == 0) {
            L->bufs[1] = buf_singleton(x);
        } else {
            L->bufs[1].e[0] = buf_tag(buf_at0(s1), (uint8_t)(s1_sz + 1));
            L->bufs[1].e[1] = s1->e[1];
            L->bufs[1].e[2] = s1->e[2];
            L->bufs[1].e[3] = s1->e[3];
            L->bufs[1].e[4] = s1->e[4];
            ((kt_elem*)&L->bufs[1])[s1_sz] = x;
        }
        if (__builtin_expect(depth > 1, 0)) {
            const kt_chain_link* base = link_as_full(top);
            memcpy(&L->bufs[2], &base->bufs[2],
                   (size_t)(2 * depth - 2) * sizeof(kt_buf));
        }
        L->tag = (uint8_t)color_from_bufs(&L->bufs[0], &L->bufs[1]);
#ifdef KT_PROFILE
        g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
        g_full_count++;
#endif
        return (kt_deque)L;
    }
    /* s1_sz == 4: result is B5, red trigger.  Run green_of_red. */
    kt_buf s1_new;
    buf_inject(s1, x, &s1_new);
    char vbuf[sizeof(kt_chain_link) + 2 * MAX_PACKET_DEPTH * sizeof(kt_buf)];
    kt_chain_link* virt = (kt_chain_link*)vbuf;
    uint8_t v_depth = link_depth(top);
    virt->depth = v_depth;
    virt->tag = top->tag;
    virt->kind = LINK_FULL;
    virt->which = 0;
    virt->chain_pos = top->chain_pos;
    virt->tail = link_tail(top);
    if (__builtin_expect(top->kind == LINK_FULL && v_depth == 1, 1)) {
        virt->bufs[0] = top->bufs[0];
        virt->bufs[1] = s1_new;
    } else if (top->kind == LINK_FULL) {
        memcpy(virt->bufs, top->bufs, (size_t)(2 * v_depth) * sizeof(kt_buf));
        virt->bufs[1] = s1_new;
    } else {
        virt->bufs[0] = *link_outer_pre(top);
        virt->bufs[1] = s1_new;
        if (__builtin_expect(v_depth > 1, 0)) {
            const kt_chain_link* _base = link_as_full(top);
            memcpy(&virt->bufs[2], &_base->bufs[2],
                   (size_t)(v_depth - 1) * 2 * sizeof(kt_buf));
        }
    }
    return (kt_deque)green_of_red(virt);
}

/* ====================================================================== */
/* pop                                                                     */
/* ====================================================================== */

/* Pop on a yellow buffer (B1..B4): return front + rest (size 0..3). */
/* (uses yellow_pop above) */

kt_deque kt_pop(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    kt_chain_link* top = (kt_chain_link*)d;
#ifdef KT_PATH_TRACE
    kt_path_pop_calls++;
#endif
    if (top == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    /* Pure Ending(b) form. */
    if (top->depth == 1 && top->tail == NULL && buf_size(&SUF(top, 0)) == 0) {
#ifdef KT_PATH_TRACE
        kt_path_pop_pure_ending++;
#endif
        kt_buf old = PRE(top, 0);
        if (buf_size(&old) == 0) {
            if (out_was_nonempty) *out_was_nonempty = 0;
            return NULL;
        }
        kt_elem x; kt_buf rest;
        buf_pop(&old, &x, &rest);
        if (out) *out = x;
        if (out_was_nonempty) *out_was_nonempty = 1;
        if (buf_size(&rest) == 0) return NULL;
        return (kt_deque)alloc_ending(top->chain_pos, rest);
    }
    /* Pop outer pre. */
    const kt_buf* p1 = link_outer_pre(top);
    int p1_sz = (int)buf_size(p1);
#ifdef KT_PATH_TRACE
    if (p1_sz >= 0 && p1_sz <= 5) kt_path_pop_p1size[p1_sz]++;
#endif
    if (p1_sz == 0) {
#ifdef KT_PATH_TRACE
        kt_path_pop_psize_zero++;
#endif
        /* Outer pre empty.  Fallback: try pop suf. */
        const kt_buf* s_eff = link_outer_suf(top);
        if (buf_size(s_eff) > 0) {
            kt_elem x; kt_buf rest;
            buf_pop(s_eff, &x, &rest);
            if (out) *out = x;
            if (out_was_nonempty) *out_was_nonempty = 1;
            uint8_t depth = link_depth(top);
            kt_buf bb[2 * MAX_PACKET_DEPTH];
            for (int i = 0; i < 2 * depth; i++) bb[i] = *link_buf_at(top, i);
            bb[1] = rest;
            return (kt_deque)alloc_link(top->chain_pos, depth, bb, link_tail(top));
        }
        if (out_was_nonempty) *out_was_nonempty = 0;
        return d;
    }
    if (out) *out = buf_at0(p1);
    if (out_was_nonempty) *out_was_nonempty = 1;
    /* If p1 was green (B2/B3) -> p1_new yellow (B1/B2): no trigger.
       If p1 was yellow (B1..B4) -> p1_new (B0..B3): if size 0 (B1->B0) red trigger. */
    if (__builtin_expect(p1_sz >= 2, 1)) {
        kt_chain_link* eff_tail = link_tail(top);
        kt_chain_link* fixed_tail =
            (eff_tail == NULL || eff_tail->tag != COL_R)
                ? eff_tail
                : green_of_red(eff_tail);
        uint8_t depth = link_depth(top);
        int top_is_diff = (top->kind == LINK_DIFF);
        int top_which_is_pre = top_is_diff
            ? (((const kt_chain_link_diff*)top)->which == 0)
            : 0;
        if (__builtin_expect(!top_is_diff || top_which_is_pre, 1)) {
#ifdef KT_PATH_TRACE
            kt_path_pop_diff_simple++;
#endif
            const kt_chain_link* base = link_as_full(top);
            const kt_buf* suf_in_base = &base->bufs[1];
            int new_p_sz = p1_sz - 1;
            int ss = (int)buf_size(suf_in_base);
            kt_color tag;
            if (new_p_sz == 0 || ss == 0 || ss == 5) tag = COL_R;
            else if ((new_p_sz == 2 || new_p_sz == 3) && (ss == 2 || ss == 3)) tag = COL_G;
            else tag = COL_Y;
            kt_chain_link_diff* D = alloc_diff_uninit(0, tag, fixed_tail,
                                                      (kt_chain_link*)base);
            D->override.e[0] = (new_p_sz == 0) ? NULL
                                : buf_tag(p1->e[1], (uint8_t)new_p_sz);
            D->override.e[1] = p1->e[2];
            D->override.e[2] = p1->e[3];
            D->override.e[3] = p1->e[4];
            D->override.e[4] = NULL;
            return (kt_deque)D;
        }
        /* Top is DIFF with which=SUF; new op modifies pre.  Materialize FULL. */
#ifdef KT_PATH_TRACE
        kt_path_pop_full_simple++;
#endif
        size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
        kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
        L->depth = depth;
        L->kind = LINK_FULL;
        L->which = 0;
        L->chain_pos = top->chain_pos;
        L->tail = fixed_tail;
        L->bufs[0].e[0] = buf_tag(p1->e[1], (uint8_t)(p1_sz - 1));
        L->bufs[0].e[1] = p1->e[2];
        L->bufs[0].e[2] = p1->e[3];
        L->bufs[0].e[3] = p1->e[4];
        L->bufs[0].e[4] = NULL;
        L->bufs[1] = *link_outer_suf(top);
        if (__builtin_expect(depth > 1, 0)) {
            const kt_chain_link* base = link_as_full(top);
            memcpy(&L->bufs[2], &base->bufs[2],
                   (size_t)(depth - 1) * 2 * sizeof(kt_buf));
        }
        L->tag = (uint8_t)color_from_bufs(&L->bufs[0], &L->bufs[1]);
#ifdef KT_PROFILE
        g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
        g_full_count++;
#endif
        return (kt_deque)L;
    }
    /* p1_sz == 1, popping yields B0: red trigger. */
#ifdef KT_PATH_TRACE
    kt_path_pop_redtrigger++;
#endif
    kt_buf p1_new = buf_empty();
    char vbuf[sizeof(kt_chain_link) + 2 * MAX_PACKET_DEPTH * sizeof(kt_buf)];
    kt_chain_link* virt = (kt_chain_link*)vbuf;
    uint8_t v_depth = link_depth(top);
    virt->depth = v_depth;
    virt->tag = top->tag;
    virt->kind = LINK_FULL;
    virt->which = 0;
    virt->chain_pos = top->chain_pos;
    virt->tail = link_tail(top);
    if (__builtin_expect(top->kind == LINK_FULL && v_depth == 1, 1)) {
        virt->bufs[0] = p1_new;
        virt->bufs[1] = top->bufs[1];
    } else if (top->kind == LINK_FULL) {
        memcpy(virt->bufs, top->bufs, (size_t)(2 * v_depth) * sizeof(kt_buf));
        virt->bufs[0] = p1_new;
    } else {
        virt->bufs[0] = p1_new;
        virt->bufs[1] = *link_outer_suf(top);
        if (__builtin_expect(v_depth > 1, 0)) {
            const kt_chain_link* _base = link_as_full(top);
            memcpy(&virt->bufs[2], &_base->bufs[2],
                   (size_t)(v_depth - 1) * 2 * sizeof(kt_buf));
        }
    }
    return (kt_deque)green_of_red(virt);
}

/* ====================================================================== */
/* eject                                                                   */
/* ====================================================================== */

kt_deque kt_eject(kt_deque d, kt_elem* out, int* out_was_nonempty) {
    kt_chain_link* top = (kt_chain_link*)d;
    if (top == NULL) {
        if (out_was_nonempty) *out_was_nonempty = 0;
        return NULL;
    }
    /* Pure Ending(b) form. */
    if (top->depth == 1 && top->tail == NULL && buf_size(&SUF(top, 0)) == 0) {
        kt_buf old = PRE(top, 0);
        if (buf_size(&old) == 0) {
            if (out_was_nonempty) *out_was_nonempty = 0;
            return NULL;
        }
        kt_buf rest; kt_elem x;
        buf_eject(&old, &rest, &x);
        if (out) *out = x;
        if (out_was_nonempty) *out_was_nonempty = 1;
        if (buf_size(&rest) == 0) return NULL;
        return (kt_deque)alloc_ending(top->chain_pos, rest);
    }
    /* Eject from outer suf. */
    const kt_buf* s1 = link_outer_suf(top);
    int s1_sz = (int)buf_size(s1);
    if (s1_sz == 0) {
        /* Outer suf empty.  Fallback: try eject pre. */
        const kt_buf* p_eff = link_outer_pre(top);
        if (buf_size(p_eff) > 0) {
            kt_buf rest; kt_elem x;
            buf_eject(p_eff, &rest, &x);
            if (out) *out = x;
            if (out_was_nonempty) *out_was_nonempty = 1;
            uint8_t depth = link_depth(top);
            kt_buf bb[2 * MAX_PACKET_DEPTH];
            for (int i = 0; i < 2 * depth; i++) bb[i] = *link_buf_at(top, i);
            bb[0] = rest;
            return (kt_deque)alloc_link(top->chain_pos, depth, bb, link_tail(top));
        }
        if (out_was_nonempty) *out_was_nonempty = 0;
        return d;
    }
    /* Read tail element directly (no temp). */
    if (out) *out = (s1_sz == 1) ? buf_at0(s1) : s1->e[s1_sz - 1];
    if (out_was_nonempty) *out_was_nonempty = 1;
    if (__builtin_expect(s1_sz >= 2, 1)) {
        /* Result has size s1_sz-1 >= 1, never red. */
        kt_chain_link* eff_tail = link_tail(top);
        kt_chain_link* fixed_tail =
            (eff_tail == NULL || eff_tail->tag != COL_R)
                ? eff_tail
                : green_of_red(eff_tail);
        uint8_t depth = link_depth(top);
        int top_is_diff = (top->kind == LINK_DIFF);
        int top_which_is_suf = top_is_diff
            ? (((const kt_chain_link_diff*)top)->which == 1)
            : 0;
        if (__builtin_expect(!top_is_diff || top_which_is_suf, 1)) {
            const kt_chain_link* base = link_as_full(top);
            const kt_buf* pre_in_base = &base->bufs[0];
            int new_s_sz = s1_sz - 1;
            int ps = (int)buf_size(pre_in_base);
            kt_color tag;
            if (ps == 0 || ps == 5 || new_s_sz == 0) tag = COL_R;
            else if ((ps == 2 || ps == 3) && (new_s_sz == 2 || new_s_sz == 3)) tag = COL_G;
            else tag = COL_Y;
            kt_chain_link_diff* D = alloc_diff_uninit(1, tag, fixed_tail,
                                                      (kt_chain_link*)base);
            D->override.e[0] = buf_tag(buf_at0(s1), (uint8_t)new_s_sz);
            D->override.e[1] = s1->e[1];
            D->override.e[2] = s1->e[2];
            D->override.e[3] = s1->e[3];
            D->override.e[4] = NULL;
            D->override.e[s1_sz - 1] = NULL;
            return (kt_deque)D;
        }
        /* Top is DIFF with which=PRE; new op modifies suf.  Materialize FULL. */
        size_t sz = sizeof(kt_chain_link) + 2 * (size_t)depth * sizeof(kt_buf);
        kt_chain_link* L = (kt_chain_link*)arena_alloc(sz);
        L->depth = depth;
        L->kind = LINK_FULL;
        L->which = 0;
        L->chain_pos = top->chain_pos;
        L->tail = fixed_tail;
        L->bufs[0] = *link_outer_pre(top);
        L->bufs[1].e[0] = buf_tag(buf_at0(s1), (uint8_t)(s1_sz - 1));
        L->bufs[1].e[1] = s1->e[1];
        L->bufs[1].e[2] = s1->e[2];
        L->bufs[1].e[3] = s1->e[3];
        L->bufs[1].e[4] = NULL;
        L->bufs[1].e[s1_sz - 1] = NULL;
        if (__builtin_expect(depth > 1, 0)) {
            const kt_chain_link* base = link_as_full(top);
            memcpy(&L->bufs[2], &base->bufs[2],
                   (size_t)(2 * depth - 2) * sizeof(kt_buf));
        }
        L->tag = (uint8_t)color_from_bufs(&L->bufs[0], &L->bufs[1]);
#ifdef KT_PROFILE
        g_alloc_links++;
#endif
#ifdef KT_DIFF_TRACE
        g_full_count++;
#endif
        return (kt_deque)L;
    }
    /* s1_sz == 1: ejecting yields B0, red trigger. */
    kt_buf s1_new = buf_empty();
    char vbuf[sizeof(kt_chain_link) + 2 * MAX_PACKET_DEPTH * sizeof(kt_buf)];
    kt_chain_link* virt = (kt_chain_link*)vbuf;
    uint8_t v_depth = link_depth(top);
    virt->depth = v_depth;
    virt->tag = top->tag;
    virt->kind = LINK_FULL;
    virt->which = 0;
    virt->chain_pos = top->chain_pos;
    virt->tail = link_tail(top);
    if (__builtin_expect(top->kind == LINK_FULL && v_depth == 1, 1)) {
        virt->bufs[0] = top->bufs[0];
        virt->bufs[1] = s1_new;
    } else if (top->kind == LINK_FULL) {
        memcpy(virt->bufs, top->bufs, (size_t)(2 * v_depth) * sizeof(kt_buf));
        virt->bufs[1] = s1_new;
    } else {
        virt->bufs[0] = *link_outer_pre(top);
        virt->bufs[1] = s1_new;
        if (__builtin_expect(v_depth > 1, 0)) {
            const kt_chain_link* _base = link_as_full(top);
            memcpy(&virt->bufs[2], &_base->bufs[2],
                   (size_t)(v_depth - 1) * 2 * sizeof(kt_buf));
        }
    }
    return (kt_deque)green_of_red(virt);
}

/* ====================================================================== */
/* Length, regularity, walk                                               */
/* ====================================================================== */

static size_t buf_count_at(const kt_buf* b, int level) {
    return (size_t)buf_size(b) << level;
}

size_t kt_length(kt_deque d) {
    const kt_chain_link* L = (const kt_chain_link*)d;
    size_t total = 0;
    int level = 0;
    while (L) {
        uint8_t depth = link_depth(L);
        for (int i = 0; i < depth; i++) {
            total += buf_count_at(link_buf_at(L, 2*i),     level + i);
            total += buf_count_at(link_buf_at(L, 2*i + 1), level + i);
        }
        level += depth;
        L = link_tail(L);
    }
    return total;
}

int kt_check_regular(kt_deque d) {
    const kt_chain_link* L = (const kt_chain_link*)d;
    while (L) {
        uint8_t depth = link_depth(L);
        if (depth < 1 || depth > MAX_PACKET_DEPTH) return -1;
        for (int i = 0; i < depth; i++) {
            if (buf_size(link_buf_at(L, 2*i)) > 5) return -2;
            if (buf_size(link_buf_at(L, 2*i + 1)) > 5) return -3;
        }
        L = link_tail(L);
    }
    return 0;
}

static void walk_buf_at(const kt_buf* b, int level, kt_walk_cb cb, void* ctx) {
    uint8_t s = buf_size(b);
    if (level == 0) {
        for (uint8_t i = 0; i < s; i++) cb(buf_at(b, i), ctx);
    } else {
        for (uint8_t i = 0; i < s; i++) {
            kt_elem xa, ya;
            /* buf_at(b, i) is a level-`level` element; split via the
               level-aware helper (handles K=2 flat blocks). */
            pair_split_at(level, buf_at(b, i), &xa, &ya);
            kt_buf inner = buf_pair_2(xa, ya);
            walk_buf_at(&inner, level - 1, cb, ctx);
        }
    }
}

void kt_walk(kt_deque d, kt_walk_cb cb, void* ctx) {
    const kt_chain_link* L = (const kt_chain_link*)d;
    /* Front-to-back order:
         For each chain link in order:
           For each level i = 0..depth-1: emit PRE(L, i) at level (offset+i).
         Then recurse on L->tail with offset += L->depth.
         Then for each chain link in REVERSE (deepest-first):
           For each level i = depth-1..0: emit SUF(L, i) at level (offset+i).

       The recursive structure: walk_chain emits all pres in front-to-back
       packet/level order, then the tail's chain, then all sufs in
       back-to-front order.

       But chains are nested: walk_packet for top emits top.pres in level
       order, then walk_chain(tail), then top.sufs in reverse level order.
    */
    /* Iterative implementation using a stack of links and base levels. */
    if (L == NULL) return;
    /* Walk down: collect chain into an array of (link, base_level). */
    const kt_chain_link* stack[256];
    int bases[256];
    int sp = 0;
    int level = 0;
    while (L) {
        stack[sp] = L;
        bases[sp] = level;
        level += link_depth(L);
        sp++;
        L = link_tail(L);
    }
    /* Forward pass: emit PRE in level order. */
    for (int s = 0; s < sp; s++) {
        const kt_chain_link* M = stack[s];
        int base = bases[s];
        uint8_t d = link_depth(M);
        for (int i = 0; i < d; i++) {
            walk_buf_at(link_buf_at(M, 2*i), base + i, cb, ctx);
        }
    }
    /* Backward pass: emit SUF in reverse level order. */
    for (int s = sp - 1; s >= 0; s--) {
        const kt_chain_link* M = stack[s];
        int base = bases[s];
        uint8_t d = link_depth(M);
        for (int i = d - 1; i >= 0; i--) {
            walk_buf_at(link_buf_at(M, 2*i + 1), base + i, cb, ctx);
        }
    }
}
