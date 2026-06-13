/* ====================================================================== *
 * ktcadeque.h - Kaplan-Tarjan persistent CATENABLE deque, C port.         *
 * ====================================================================== *
 *
 * A hand-written C port of the KT99 §6 catenable deque, layered on the
 * §4 deque of ktdeque.h.  Like that deque, every kc_cadeque value is an
 * immutable persistent snapshot; an operation returns a new snapshot
 * sharing structure with the old one.  The headline over the §4 deque
 * is catenation: kc_concat joins two catenable deques in worst-case
 * O(1).
 *
 * This C port mirrors, branch for branch, the machine-checked Rocq
 * development rocq/KTDeque/Catenable/ (the production op web
 * FlatChain.v / FlatOps.v, whose six keystone theorems + constant cost
 * bound are closed under the global context — `make cat-keystone-gate`).
 * The §6 prefix/suffix buffers are §4 deques (ktdeque.h), exactly as the
 * extracted OCaml artifact's buffers are the verified §4 chain.  This C
 * is validated against that extracted artifact by a deterministic
 * differential workload, not formally refined from it.
 *
 *   --------------------------------------------------------------------
 *   ELEMENT MODEL
 *   --------------------------------------------------------------------
 *
 *   Same as ktdeque.h: elements are opaque kt_elem (= void*); the deque
 *   stores the pointer-sized values you pass in and never owns user
 *   data.  Stored elements must be 8-byte aligned (low 3 bits zero).
 *
 *   --------------------------------------------------------------------
 *   OPERATIONS (all worst-case O(1))
 *   --------------------------------------------------------------------
 *
 *     kc_empty   ()            -> empty
 *     kc_push    (x, d)        -> d with x prepended
 *     kc_inject  (d, x)        -> d with x appended
 *     kc_pop     (d, &x, &ok)  -> d without its first element
 *     kc_eject   (d, &x, &ok)  -> d without its last element
 *     kc_concat  (d, e)        -> the concatenation d ++ e
 */

#ifndef KT_CADEQUE_H
#define KT_CADEQUE_H

#include <stddef.h>
#include "ktdeque.h"

/** Opaque catenable-deque handle.  An immutable persistent snapshot. */
typedef void* kc_cadeque;

/** The empty catenable deque. */
kc_cadeque kc_empty(void);

/** Prepend [x] to the front of [d]. */
kc_cadeque kc_push(kt_elem x, kc_cadeque d);

/** Append [x] to the back of [d]. */
kc_cadeque kc_inject(kc_cadeque d, kt_elem x);

/** Remove and return the front element of [d].  On entry [*out] and
 *  [*out_was_nonempty] are written; on exit the function returns the
 *  remaining deque.  Empty input: [*out_was_nonempty = 0]. */
kc_cadeque kc_pop(kc_cadeque d, kt_elem* out, int* out_was_nonempty);

/** Remove and return the back element of [d].  Mirror of kc_pop. */
kc_cadeque kc_eject(kc_cadeque d, kt_elem* out, int* out_was_nonempty);

/** Concatenate [d] and [e]: the result's sequence is [d]'s followed by
 *  [e]'s.  Worst-case O(1). */
kc_cadeque kc_concat(kc_cadeque d, kc_cadeque e);

/* ====================================================================== *
 * Debug / inspection.                                                      *
 * ====================================================================== */

/** Total number of elements in [d].  O(N): walks the whole structure. */
size_t kc_length(kc_cadeque d);

/** In-order traversal: calls [cb(e, ctx)] for each element, front to
 *  back. */
typedef void (*kc_walk_cb)(kt_elem e, void* ctx);
void kc_walk(kc_cadeque d, kc_walk_cb cb, void* ctx);

/* ====================================================================== *
 * Arena compaction.                                                        *
 * ====================================================================== *
 *
 * The §6 prefix/suffix buffers are §4 deques in a bump arena that is
 * never reclaimed automatically (a pure-push cadeque retains every
 * intermediate buffer version — O(N) arena links).  Like the §4 deque's
 * kt_arena_compact, call kc_arena_compact periodically to copy-forward
 * the live buffer structure and release the rest.
 *
 * SAFETY CONTRACT (same as kt_arena_compact): roots[] MUST list EVERY
 * currently-live kc_cadeque value; any persistent old version not in
 * roots[] becomes dangling.  After the call, roots[] still point at the
 * same §6 spine nodes (those are not relocated), but their embedded §4
 * buffers have been copied forward.  Returns bytes reclaimed. */
size_t kc_arena_compact(kc_cadeque* roots, size_t n_roots);

#endif /* KT_CADEQUE_H */
