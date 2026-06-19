/**
 * ElementTree — a "level-ℓ element over A": a perfect binary tree of 2^ℓ base
 * values.  Port of `ElementTree` / `Coq_E` in `ocaml/extracted/kTDeque.ml`
 * (lines 70–104), itself from `rocq/KTDeque/Common/Element.v`.
 *
 *   - level 0  : a single base value           (`base`)
 *   - level ℓ+1: a pair of two level-ℓ elements (`pair`)
 *
 * The deque stores `Elt<A>` in its buffers; a buffer at chain-depth k holds
 * level-k elements (the pair tower).  `pair`/`unpair` are O(1); `toList`
 * flattens left-to-right, which is the semantics the oracle is compared against.
 */
import { bump } from "./alloc.js";

export type Elt<A> =
  | { readonly tag: "base"; readonly lvl: 0; readonly v: A }
  | { readonly tag: "pair"; readonly lvl: number; readonly l: Elt<A>; readonly r: Elt<A> };

export function base<A>(a: A): Elt<A> {
  return { tag: "base", lvl: 0, v: a };
}

export function level<A>(e: Elt<A>): number {
  return e.lvl;
}

/** Pair two SAME-level elements into one level-(ℓ+1) element. */
export function pair<A>(x: Elt<A>, y: Elt<A>): Elt<A> {
  bump(); // one new persistent node
  return { tag: "pair", lvl: x.lvl + 1, l: x, r: y };
}

/** Inverse of `pair`; `null` on a base element (mirrors the OCaml `option`). */
export function unpair<A>(e: Elt<A>): [Elt<A>, Elt<A>] | null {
  return e.tag === "pair" ? [e.l, e.r] : null;
}

/** Flatten to the underlying base values, left-to-right. */
export function toList<A>(e: Elt<A>): A[] {
  if (e.tag === "base") return [e.v];
  return toList(e.l).concat(toList(e.r));
}
