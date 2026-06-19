/**
 * Buf5 — a buffer holding 0..5 elements, represented as a readonly array.
 * Port of the `buf5` type and its operations in `ocaml/extracted/kTDeque.ml`
 * (and `rocq/KTDeque/Common/Buf5.v`).  Operations are generic over the element
 * type `T`; the pairing-aware concat helpers live in `deque.ts`.
 *
 * Conventions (matching the extraction):
 *   - push / pop act on the FRONT; inject / eject act on the BACK.
 *   - `*_naive` succeed unless the size bound (0 or 5) is hit, returning `null`.
 *   - `green_*` require size ∈ {2,3}; `yellow_*` require size ∈ {1,2,3,4}.
 */

export type Buf<T> = readonly T[]; // invariant: 0 <= length <= 5

export const bsize = (b: Buf<unknown>): number => b.length;

// ---- colours (exact: rocq/KTDeque/Common/Color.v:44) ----
export type Color = "green" | "yellow" | "red";

export const bufColor = (b: Buf<unknown>): Color => {
  const n = b.length;
  return n === 0 || n === 5 ? "red" : n === 1 || n === 4 ? "yellow" : "green";
};

export const colorMeet = (a: Color, b: Color): Color =>
  a === "red" || b === "red" ? "red" : a === "yellow" || b === "yellow" ? "yellow" : "green";

// ---- naive (size-bounded) ops ----
export const pushNaive = <T>(x: T, b: Buf<T>): Buf<T> | null => (b.length < 5 ? [x, ...b] : null);
export const injectNaive = <T>(b: Buf<T>, x: T): Buf<T> | null => (b.length < 5 ? [...b, x] : null);
export const popNaive = <T>(b: Buf<T>): [T, Buf<T>] | null =>
  b.length > 0 ? [b[0]!, b.slice(1)] : null;
export const ejectNaive = <T>(b: Buf<T>): [Buf<T>, T] | null =>
  b.length > 0 ? [b.slice(0, -1), b[b.length - 1]!] : null;

// ---- colour-guarded ops (return null if the size is outside the colour band) ----
const inRange = (n: number, lo: number, hi: number) => n >= lo && n <= hi;

export const greenPush = <T>(x: T, b: Buf<T>): Buf<T> | null =>
  inRange(b.length, 2, 3) ? [x, ...b] : null;
export const greenInject = <T>(b: Buf<T>, x: T): Buf<T> | null =>
  inRange(b.length, 2, 3) ? [...b, x] : null;
export const greenPop = <T>(b: Buf<T>): [T, Buf<T>] | null =>
  inRange(b.length, 2, 3) ? [b[0]!, b.slice(1)] : null;
export const greenEject = <T>(b: Buf<T>): [Buf<T>, T] | null =>
  inRange(b.length, 2, 3) ? [b.slice(0, -1), b[b.length - 1]!] : null;

export const yellowPush = <T>(x: T, b: Buf<T>): Buf<T> | null =>
  inRange(b.length, 1, 4) ? [x, ...b] : null;
export const yellowInject = <T>(b: Buf<T>, x: T): Buf<T> | null =>
  inRange(b.length, 1, 4) ? [...b, x] : null;
export const yellowPop = <T>(b: Buf<T>): [T, Buf<T>] | null =>
  inRange(b.length, 1, 4) ? [b[0]!, b.slice(1)] : null;
export const yellowEject = <T>(b: Buf<T>): [Buf<T>, T] | null =>
  inRange(b.length, 1, 4) ? [b.slice(0, -1), b[b.length - 1]!] : null;

// ---- small builders (prefix23 / suffix23 / suffix12) ----
export const prefix23 = <T>(opt: T | null, bc: readonly [T, T]): Buf<T> =>
  opt !== null ? [opt, bc[0], bc[1]] : [bc[0], bc[1]];
export const suffix23 = <T>(ab: readonly [T, T], opt: T | null): Buf<T> =>
  opt !== null ? [ab[0], ab[1], opt] : [ab[0], ab[1]];
export const suffix12 = <T>(x: T, opt: T | null): Buf<T> => (opt !== null ? [x, opt] : [x]);

// ---- decompositions (used by the green_of_red repair) ----
export type PreDecomp<T> =
  | { tag: "under"; x: T | null } // size 0 or 1: the buffer is empty / nearly so
  | { tag: "ok"; b: Buf<T> } // size 2 or 3
  | { tag: "over"; b: Buf<T>; c: T; d: T }; // size 4 or 5: two overflow elements c,d

export const prefixDecompose = <T>(b: Buf<T>): PreDecomp<T> => {
  switch (b.length) {
    case 0:
      return { tag: "under", x: null };
    case 1:
      return { tag: "under", x: b[0]! };
    case 4:
      return { tag: "over", b: [b[0]!, b[1]!], c: b[2]!, d: b[3]! };
    case 5:
      return { tag: "over", b: [b[0]!, b[1]!, b[2]!], c: b[3]!, d: b[4]! };
    default:
      return { tag: "ok", b };
  }
};

export type SufDecomp<T> =
  | { tag: "under"; x: T | null }
  | { tag: "ok"; b: Buf<T> }
  | { tag: "over"; b: Buf<T>; a: T; b2: T };

export const suffixDecompose = <T>(b: Buf<T>): SufDecomp<T> => {
  switch (b.length) {
    case 0:
      return { tag: "under", x: null };
    case 1:
      return { tag: "under", x: b[0]! };
    case 4:
      return { tag: "over", b: [b[2]!, b[3]!], a: b[0]!, b2: b[1]! };
    case 5:
      return { tag: "over", b: [b[2]!, b[3]!, b[4]!], a: b[0]!, b2: b[1]! };
    default:
      return { tag: "ok", b };
  }
};

export type Sandwich<T> =
  | { tag: "alone"; x: T | null }
  | { tag: "sandwich"; first: T; mid: Buf<T>; last: T };

export const bufferUnsandwich = <T>(b: Buf<T>): Sandwich<T> => {
  if (b.length === 0) return { tag: "alone", x: null };
  if (b.length === 1) return { tag: "alone", x: b[0]! };
  return { tag: "sandwich", first: b[0]!, mid: b.slice(1, -1), last: b[b.length - 1]! };
};

/** prefix_rot x b: prepend x, return (new buffer, ejected last element). */
export const prefixRot = <T>(x: T, b: Buf<T>): [Buf<T>, T] =>
  b.length === 0 ? [[], x] : [[x, ...b.slice(0, -1)], b[b.length - 1]!];

/** suffix_rot b x: append x, return (popped first element, new buffer). */
export const suffixRot = <T>(b: Buf<T>, x: T): [T, Buf<T>] =>
  b.length === 0 ? [x, []] : [b[0]!, [...b.slice(1), x]];

/** buffer_halve: split into an optional odd head and a buffer of consecutive pairs. */
export const bufferHalve = <T>(b: Buf<T>): [T | null, Buf<readonly [T, T]>] => {
  const odd = b.length % 2 === 1 ? b[0]! : null;
  const start = odd !== null ? 1 : 0;
  const pairs: [T, T][] = [];
  for (let i = start; i < b.length; i += 2) pairs.push([b[i]!, b[i + 1]!]);
  return [odd, pairs];
};
