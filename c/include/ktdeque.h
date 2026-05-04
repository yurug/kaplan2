/* ktdeque.h — Section-4 deque with worst-case O(1) per op (packets-and-chains).
 *
 * Algorithmic structure: KT99 §4.1 stack-of-substacks / VWGP packets-and-chains.
 * Each operation modifies at most the top packet plus (in the green_of_red
 * cascade) the topmost-G chain link.
 *
 * See COMPARISON.md for benchmark numbers, STATUS.md for design rationale.
 */

#ifndef KT_DEQUE_H
#define KT_DEQUE_H

#include <stddef.h>
#include <stdint.h>

typedef void* kt_elem;

typedef struct kt_pair {
    kt_elem left;
    kt_elem right;
} kt_pair;

#define kt_base(x) ((kt_elem)(x))

kt_elem kt_pair_make(kt_elem x, kt_elem y);
void    kt_pair_split(kt_elem e, kt_elem* x, kt_elem* y);

typedef void* kt_deque;

kt_deque kt_empty(void);
kt_deque kt_push   (kt_elem x, kt_deque d);
kt_deque kt_inject (kt_deque d, kt_elem x);
kt_deque kt_pop    (kt_deque d, kt_elem* out, int* out_was_nonempty);
kt_deque kt_eject  (kt_deque d, kt_elem* out, int* out_was_nonempty);

size_t kt_length(kt_deque d);

/* Returns 0 if the chain satisfies the C's K-T regularity invariant —
 * the per-packet analogue of the abstract `regular_chain` predicate
 * from KTDeque/DequePtr/Regularity.v.  Checked invariants:
 *
 *   1. Every link's depth is in [1, MAX_PACKET_DEPTH].
 *   2. Every buffer's encoded size is <= 5.
 *   3. The top link's outer buffers are `buf_not_full` (size <= 4).
 *      Lazy-singleton exception: a pure-Ending top (depth=1, tail
 *      NULL, FULL kind, with one of pre/suf B5 and the other B0) is
 *      accepted as the transient state produced by 5 same-side pushes
 *      from empty; it is split on the next op.
 *   4. Color alternation (KT99): every RED link's tail (if non-NULL)
 *      is GREEN.  Mirrors the assert(0) calls in green_of_red Cases
 *      2 & 3.
 *
 * Not enforced (the C uses flat packets that aggregate yellow runs;
 * see Phase S10 audit and the project memory entry "D4Cell vs
 * packets-and-chains tradeoff"):
 *   - per-link absorbability of deeper buffers (`buf_can_absorb_one`
 *     in Regularity.v).  Deeper buffers can transiently be B4 or B5
 *     between operations; the cascade fires on the next op that
 *     touches them.
 *
 * Negative return codes (distinct per violation, all non-zero):
 *   -1  depth out of range
 *   -2  outer pre buffer size > 5 (encoding error)
 *   -3  outer suf buffer size > 5 (encoding error)
 *   -4  top outer pre is B5 (violates buf_not_full at top)
 *   -5  top outer suf is B5 (violates buf_not_full at top)
 *   -8  RED link with non-GREEN, non-NULL tail (color alternation)
 *
 * ABI: callers checking `kt_check_regular(d) == 0` for OK remain
 * correct; the strengthened predicate only rejects more configs.
 */
int    kt_check_regular(kt_deque d);

/* Returns 0 if the K=1 DIFF invariant holds: every DIFF link's `base`
 * is a FULL link, never another DIFF.  Walks the chain via the
 * effective tail AND, for each DIFF encountered, also checks its base.
 *
 * Negative return codes:
 *   -1  a DIFF's base is itself a DIFF (K=1 violation)
 *   -2  malformed link kind (neither LINK_FULL nor LINK_DIFF)
 *   -3  a DIFF's base pointer is NULL
 */
int    kt_check_diff_invariant(kt_deque d);

typedef void (*kt_walk_cb)(kt_elem e, void* ctx);
void kt_walk(kt_deque d, kt_walk_cb cb, void* ctx);

size_t kt_alloc_packets(void);
size_t kt_alloc_chains(void);
size_t kt_alloc_pairs(void);
size_t kt_alloc_bufs(void);
void   kt_reset_alloc_counters(void);

/* Compact the arena: copy all chain links and pair elements reachable
 * from any of the `n_roots` deque values forward into a fresh region,
 * then release the previously-live regions.  After this call, the
 * deque values in `roots[]` point at the COPIED chain links; old
 * pointers are dangling.  Caller-cooperative; call when you know the
 * complete live set.
 *
 * IMPORTANT (safety):
 *   - The roots[] array MUST list EVERY currently-live deque value.
 *     Any persistent old version not in the array becomes dangling.
 *   - Element pointers (level 0 / user data) are NOT copied; only
 *     internal arena structure.  User-supplied storage[] etc. is
 *     left untouched.
 *   - Persistence semantics are preserved: copy-forward does not
 *     mutate the deque structure semantically; it just relocates it.
 *
 * Returns the number of bytes reclaimed (sum of chunk sizes freed
 * minus the size of the new chunk).  O(reachable cells).
 */
size_t kt_arena_compact(kt_deque* roots, size_t n_roots);

/* Phase U: full compaction (chain links AND pair blocks).
 *
 * Walks chain links and ALSO traverses every kt_buf slot to copy-forward
 * the pair-block storage they reference (level-1 2-blocks, level-2
 * 4-blocks, level-≥3 kt_pairs) into a fresh pair-block arena.  Bounds
 * RSS to O(reachable) data, whereas `kt_arena_compact` only relocates
 * chain links and lets the pair arena grow unbounded.
 *
 * MUCH more expensive than `kt_arena_compact`: cost is proportional to
 * total live pair-block nodes = O(N) for an N-element deque.  Call
 * rarely (e.g. every few million ops, or when pair-arena RSS exceeds a
 * threshold).
 *
 * Same safety contract as `kt_arena_compact`: roots[] must enumerate
 * every currently-live deque value; persistence is preserved by
 * copy-forwarding (no pre-existing live cell is mutated).
 *
 * Returns total bytes reclaimed (chain-link + pair-block).
 */
size_t kt_arena_compact_full(kt_deque* roots, size_t n_roots);

/* ====================================================================== */
/* Phase V: explicit allocation regions.                                  */
/*                                                                         */
/* A `kt_region` is a memory namespace owning two arenas (chain-link +    */
/* pair-block), a forwarding map, and bookkeeping.  Deques created in a   */
/* region are freed in O(chunks) when the region is destroyed.            */
/*                                                                         */
/* The legacy API (kt_push, kt_pop, ...) routes to a default region       */
/* shared across all clients of this thread; the new `_in` entry points   */
/* take an explicit region parameter.                                     */
/* ====================================================================== */

typedef struct kt_region kt_region;

/* Create a region.  hint = chunk-size hint (0 = use default ~4 MB). */
kt_region* kt_region_create(size_t hint);

/* Destroy a region — frees all chunks ever allocated in it.  After
 * this call, every deque value that was created or modified by an
 * _in operation on `r` is dangling.  Caller must not use them.
 *
 * O(chunk count); no traversal of allocated cells.
 */
void kt_region_destroy(kt_region* r);

/* Region-scoped variants of the public API.  All allocations route
 * to the given region's chain-link and pair-block arenas. */
kt_deque kt_empty_in (kt_region* r);
kt_deque kt_push_in  (kt_region* r, kt_elem x, kt_deque d);
kt_deque kt_inject_in(kt_region* r, kt_deque d, kt_elem x);
kt_deque kt_pop_in   (kt_region* r, kt_deque d, kt_elem* out, int* out_was_nonempty);
kt_deque kt_eject_in (kt_region* r, kt_deque d, kt_elem* out, int* out_was_nonempty);

/* Per-region compaction (extends Phase T / U).  roots[] must be deque
 * values created/owned by this region; the function relocates their
 * reachable structure within the region's arenas.  Same safety
 * contract as kt_arena_compact / kt_arena_compact_full.
 */
size_t kt_region_compact     (kt_region* r, kt_deque* roots, size_t n_roots);
size_t kt_region_compact_full(kt_region* r, kt_deque* roots, size_t n_roots);

#endif
