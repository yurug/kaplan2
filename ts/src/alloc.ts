/**
 * Allocation counter — the JS analogue of the C port's `kt_alloc_packets()` /
 * `kt_alloc_pairs()` instrumentation (see `c/tests/wc_test.c`).
 *
 * Every persistent node the operations build (a chain `cons`/`end`, a packet
 * `pnode`, an element `pair`) bumps this counter.  Because the structure is
 * purely functional, a worst-case-O(1) operation allocates only a constant
 * number of new nodes per call and shares the rest; a recursive O(log n)
 * cascade would allocate Θ(log n).  `test/wc.ts` resets the counter before each
 * operation and asserts the per-op maximum stays *flat* as n grows.
 */
let count = 0;

export function bump(n = 1): void {
  count += n;
}
export function reset(): void {
  count = 0;
}
export function get(): number {
  return count;
}
