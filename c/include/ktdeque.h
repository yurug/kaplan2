/* ====================================================================== *
 * ktdeque.h - Kaplan-Tarjan persistent real-time deque, worst-case O(1).  *
 * ====================================================================== *
 *
 * A purely functional deque with worst-case O(1) per operation push, pop,
 * inject, eject.  Every kt_deque value is an immutable snapshot; an
 * operation returns a new snapshot sharing structure with the old one,
 * with no asymptotic penalty.  You can fork a deque, mutate one branch,
 * and the other branch is unaffected.
 *
 * Algorithm: KT99 / Viennot-Wendling-Guéneau-Pottier "packets and chains".
 *
 * For the *intuition* — why "no two reds adjacent" delivers worst-case
 * O(1), why packets aggregate yellow runs into a single allocation —
 * read the project's "why-bounded-cascade" note, hosted at
 *
 *     https://github.com/yurug/kaplan2/blob/main/kb/spec/why-bounded-cascade.md
 *
 * The implementation source (ktdeque_dequeptr.c, in the project's
 * monorepo at https://github.com/yurug/kaplan2/blob/main/c/src/ktdeque_dequeptr.c)
 * mirrors that document section by section.
 *
 *   --------------------------------------------------------------------
 *   QUICK START
 *   --------------------------------------------------------------------
 *
 *     #include "ktdeque.h"
 *
 *     long values[] = {1, 2, 3};
 *     kt_deque d = kt_empty();
 *     d = kt_push(kt_base(&values[0]), d);
 *     d = kt_push(kt_base(&values[1]), d);
 *     // d now holds [&values[1], &values[0]]
 *
 *     kt_elem x; int ok;
 *     d = kt_pop(d, &x, &ok);
 *     // ok = 1, x = &values[1]
 *
 *   See examples/hello.c for a full walkthrough.
 *
 *   --------------------------------------------------------------------
 *   ELEMENT MODEL
 *   --------------------------------------------------------------------
 *
 *   Elements are opaque kt_elem (= void*).  The deque does not copy or
 *   own user data; it stores the pointer-sized values you pass in.
 *   Common patterns:
 *
 *     - You own a long array `storage[N]`: pass kt_base(&storage[i]).
 *     - You own a struct: pass a pointer to it.
 *     - You want a small inline scalar: cast to (kt_elem) (size_t).
 *
 *   The low 3 bits of every kt_elem stored in the deque must be zero
 *   (the buffer's size is encoded in those bits — see the "Buffer
 *   (Buf5)" section of ktdeque_dequeptr.c in the project monorepo
 *   for why).  All malloc-aligned pointers and 8-byte-aligned scalars
 *   satisfy this.
 *
 *   --------------------------------------------------------------------
 *   THREADING
 *   --------------------------------------------------------------------
 *
 *   The default arena (used by the legacy kt_push / kt_pop / ... entry
 *   points) is per-thread (TLS).  Concurrent threads never share arena
 *   state; each thread can use the legacy API independently.
 *
 *   To pass a deque between threads, or to bound RSS deterministically,
 *   use the explicit-region API (kt_region_create / kt_*_in / ...) —
 *   see the bottom of this file.
 *
 *   --------------------------------------------------------------------
 *   ARENA MANAGEMENT
 *   --------------------------------------------------------------------
 *
 *   The library uses a bump-pointer arena to avoid per-op malloc.  Every
 *   kt_push allocates ~50-100 bytes of arena; long-running programs
 *   should periodically call kt_arena_compact() to reclaim arena space
 *   no longer reachable from any live deque (a Cheney-style copy
 *   collector specialized to the deque shape).  The roots[] array MUST
 *   list every currently-live deque value.
 *
 *   For benchmark numbers, the project overview, and the design
 *   decisions (ADRs) behind the implementation, see the project
 *   repository:
 *
 *     https://github.com/yurug/kaplan2
 */

#ifndef KT_DEQUE_H
#define KT_DEQUE_H

#include <stddef.h>
#include <stdint.h>

/* ====================================================================== *
 * Element type.                                                            *
 * ====================================================================== */

/** Opaque element handle.  See ELEMENT MODEL above for what to put here. */
typedef void* kt_elem;

/** Internal pair node — surfaces in the API only via kt_pair_make /
 *  kt_pair_split for users who want to assemble paired elements
 *  manually.  Most callers should ignore this and let the deque pair
 *  things internally. */
typedef struct kt_pair {
    kt_elem left;
    kt_elem right;
} kt_pair;

/** kt_base(x) : kt_elem.  Wrap a typed pointer or scalar to fit the
 *  kt_elem slot.  This is just a cast; provided for readability so call
 *  sites distinguish "user value going in" from internal pair handles. */
#define kt_base(x) ((kt_elem)(x))

/** Pack two elements into a single kt_elem holding a kt_pair, allocating
 *  a kt_pair node in the current arena.  Symmetric kt_pair_split
 *  reverses the operation.  Most users never call these directly. */
kt_elem kt_pair_make(kt_elem x, kt_elem y);

/** Inverse of kt_pair_make: store the two halves into [*x] and [*y]. */
void    kt_pair_split(kt_elem e, kt_elem* x, kt_elem* y);

/* ====================================================================== *
 * Deque value type and core operations.                                    *
 * ====================================================================== */

/** Opaque deque handle.  An immutable snapshot; operations never mutate
 *  the input — they return a new snapshot sharing structure. */
typedef void* kt_deque;

/** The empty deque.  All deques are eventually rooted at kt_empty(). */
kt_deque kt_empty(void);

/** Prepend [x] to the front of [d]; return the resulting deque.
 *  Worst-case O(1).  See §4 of why-bounded-cascade.md
 *  (https://github.com/yurug/kaplan2/blob/main/kb/spec/why-bounded-cascade.md) for why. */
kt_deque kt_push   (kt_elem x, kt_deque d);

/** Append [x] to the back of [d]; return the resulting deque.
 *  Mirror of kt_push.  Worst-case O(1). */
kt_deque kt_inject (kt_deque d, kt_elem x);

/** Remove and return the front element of [d].  On entry, [*out] and
 *  [*out_was_nonempty] are written; on exit, the function returns the
 *  remaining deque.
 *
 *  If [d] is empty: [*out_was_nonempty = 0], [*out] unchanged, and the
 *  returned deque is empty.  Otherwise: [*out_was_nonempty = 1] and
 *  [*out] holds the popped element.
 *
 *  Worst-case O(1). */
kt_deque kt_pop    (kt_deque d, kt_elem* out, int* out_was_nonempty);

/** Remove and return the back element of [d].  Mirror of kt_pop.
 *  Worst-case O(1). */
kt_deque kt_eject  (kt_deque d, kt_elem* out, int* out_was_nonempty);

/** Total number of elements in [d].  O(N): walks the whole structure.
 *  Provided for debugging and tests; not intended for hot-path use. */
size_t kt_length(kt_deque d);

/* ====================================================================== *
 * Debug / inspection.                                                      *
 * ====================================================================== */

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

/** Iterate every base element in the deque, in front-to-back order,
 *  invoking [cb(e, ctx)] for each one.  O(N).  Provided for diagnostics
 *  and tests; the verified pop / eject ops are the right tool for
 *  in-order consumption in production code. */
typedef void (*kt_walk_cb)(kt_elem e, void* ctx);
void kt_walk(kt_deque d, kt_walk_cb cb, void* ctx);

/* ====================================================================== *
 * Allocation counters.                                                     *
 * ====================================================================== *
 *
 * For wall-clock-equivalent cost reasoning at the C level: each kt_*
 * op allocates a bounded number of arena objects.  These counters
 * expose the running totals so a test (e.g. tests/wc_test.c) can
 * verify that `K` operations cost at most `c * K` allocations for
 * a small constant `c`.  Reset between runs with
 * kt_reset_alloc_counters().
 */

size_t kt_alloc_packets(void);
size_t kt_alloc_chains(void);
size_t kt_alloc_pairs(void);
size_t kt_alloc_bufs(void);
void   kt_reset_alloc_counters(void);

/* ====================================================================== *
 * Arena management.                                                        *
 * ====================================================================== *
 *
 * The library uses a bump-pointer arena to avoid the ~30-50 ns / call
 * overhead of malloc.  Every kt_push / kt_inject / etc. allocates
 * O(1) arena bytes; nothing is freed until the caller explicitly
 * compacts.
 *
 * For short-lived workloads this is fine.  For long-running programs
 * (millions of ops, especially with discarded intermediate states),
 * call kt_arena_compact() periodically to reclaim arena bytes that
 * are no longer reachable from any live deque.  A Cheney-style
 * semispace copy collector specialized to the deque shape; cost is
 * O(reachable cells), not O(arena size).
 *
 * SAFETY CONTRACT: roots[] MUST list every currently-live deque
 * value.  Any persistent old version not in roots[] becomes dangling.
 * If you don't know your full root set, prefer the kt_region_*
 * API below — it folds compaction into explicit lifetimes.
 */

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
