/**
 * Section-4 Kaplan–Tarjan deque: purely-functional, worst-case O(1) per op.
 *
 * Faithful port of the Rocq-extracted certified PRODUCTION implementation
 * `ocaml/extracted/kTDeque.ml` — the `push_kt2`/`pop_kt2`/`inject_kt2`/
 * `eject_kt2` family over the colour-tagged `kChain` (from
 * `rocq/KTDeque/DequePtr/OpsKT.v`).  The explicit colour TAG on each anchor
 * (set by `make_yellow_k`/`make_red_k`) is load-bearing: operations dispatch on
 * the tag, not on the recomputed buffer colour, which is what keeps yellow runs
 * aggregated so the repair (`green_of_red_k`) stays O(1) — never a recursive
 * cascade (the project hard rule).  Verified by `test/fuzz.ts` and `test/wc.ts`.
 */
import { type Elt, base, level, pair, unpair, toList as eltToList } from "./element.js";
import * as B from "./buf5.js";
import { type Buf, type Color } from "./buf5.js";
import { bump } from "./alloc.js";

// ===================================================================
//  Types.  A Packet aggregates a (possibly nested) yellow run; a Chain
//  is a spine of colour-tagged anchor packets ending in one buffer.
// ===================================================================
export type Packet<A> =
  | { readonly tag: "hole" }
  | { readonly tag: "pnode"; readonly pre: Buf<Elt<A>>; readonly inner: Packet<A>; readonly suf: Buf<Elt<A>> };

export type Chain<A> =
  | { readonly tag: "end"; readonly b: Buf<Elt<A>> }
  | { readonly tag: "cons"; readonly color: Color; readonly p: Packet<A>; readonly c: Chain<A> };

const HOLE: Packet<never> = { tag: "hole" };
const hole = <A>(): Packet<A> => HOLE as Packet<A>; // shared constant, no allocation
const pnode = <A>(pre: Buf<Elt<A>>, inner: Packet<A>, suf: Buf<Elt<A>>): Packet<A> => {
  bump();
  return { tag: "pnode", pre, inner, suf };
};
const end = <A>(b: Buf<Elt<A>>): Chain<A> => {
  bump();
  return { tag: "end", b };
};
const cons = <A>(color: Color, p: Packet<A>, c: Chain<A>): Chain<A> => {
  bump();
  return { tag: "cons", color, p, c };
};
const consG = <A>(p: Packet<A>, c: Chain<A>): Chain<A> => cons("green", p, c);

// ===================================================================
//  Sequence semantics (chain_to_list) — the oracle comparison target.
// ===================================================================
const bufSeqE = <A>(b: Buf<Elt<A>>): A[] => b.flatMap(eltToList);
const packetSeq = <A>(p: Packet<A>, inner: A[]): A[] =>
  p.tag === "hole" ? inner : bufSeqE(p.pre).concat(packetSeq(p.inner, inner), bufSeqE(p.suf));
const chainSeq = <A>(c: Chain<A>): A[] =>
  c.tag === "end" ? bufSeqE(c.b) : packetSeq(c.p, chainSeq(c.c));

// ===================================================================
//  Pairing-aware buffer helpers (kTDeque.ml:854–1020).
// ===================================================================
const pairOne = <A>(p: readonly [Elt<A>, Elt<A>]): Elt<A> | null =>
  level(p[0]) === level(p[1]) ? pair(p[0], p[1]) : null;

const pairEachBuf = <A>(b: Buf<readonly [Elt<A>, Elt<A>]>): Buf<Elt<A>> | null => {
  const out: Elt<A>[] = [];
  for (const p of b) {
    const x = pairOne(p);
    if (x === null) return null;
    out.push(x);
  }
  return out;
};

const greenPrefixConcat = <A>(b1: Buf<Elt<A>>, b2: Buf<Elt<A>>): [Buf<Elt<A>>, Buf<Elt<A>>] | null => {
  const d = B.prefixDecompose(b1);
  switch (d.tag) {
    case "under": {
      const gp = B.greenPop(b2);
      if (gp === null) return null;
      const up = unpair(gp[0]);
      return up === null ? null : [B.prefix23(d.x, up), gp[1]];
    }
    case "ok":
      return [d.b, b2];
    case "over": {
      if (level(d.c) !== level(d.d)) return null;
      const b2p = B.greenPush(pair(d.c, d.d), b2);
      return b2p === null ? null : [d.b, b2p];
    }
  }
};

const greenSuffixConcat = <A>(b1: Buf<Elt<A>>, b2: Buf<Elt<A>>): [Buf<Elt<A>>, Buf<Elt<A>>] | null => {
  const d = B.suffixDecompose(b2);
  switch (d.tag) {
    case "under": {
      const ge = B.greenEject(b1);
      if (ge === null) return null;
      const up = unpair(ge[1]);
      return up === null ? null : [ge[0], B.suffix23(up, d.x)];
    }
    case "ok":
      return [b1, d.b];
    case "over": {
      if (level(d.a) !== level(d.b2)) return null;
      const b1p = B.greenInject(b1, pair(d.a, d.b2));
      return b1p === null ? null : [b1p, d.b];
    }
  }
};

const prefixConcat = <A>(b1: Buf<Elt<A>>, b2: Buf<Elt<A>>): [Buf<Elt<A>>, Buf<Elt<A>>] | null => {
  const d = B.prefixDecompose(b1);
  switch (d.tag) {
    case "under": {
      const yp = B.yellowPop(b2);
      if (yp === null) return null;
      const up = unpair(yp[0]);
      return up === null ? null : [B.prefix23(d.x, up), yp[1]];
    }
    case "ok":
      return [d.b, b2];
    case "over": {
      if (level(d.c) !== level(d.d)) return null;
      const b2p = B.yellowPush(pair(d.c, d.d), b2);
      return b2p === null ? null : [d.b, b2p];
    }
  }
};

const suffixConcat = <A>(b1: Buf<Elt<A>>, b2: Buf<Elt<A>>): [Buf<Elt<A>>, Buf<Elt<A>>] | null => {
  const d = B.suffixDecompose(b2);
  switch (d.tag) {
    case "under": {
      const ye = B.yellowEject(b1);
      if (ye === null) return null;
      const up = unpair(ye[1]);
      return up === null ? null : [ye[0], B.suffix23(up, d.x)];
    }
    case "ok":
      return [b1, d.b];
    case "over": {
      if (level(d.a) !== level(d.b2)) return null;
      const b1p = B.yellowInject(b1, pair(d.a, d.b2));
      return b1p === null ? null : [b1p, d.b];
    }
  }
};

// buffer_push_chain / buffer_inject_chain (used inside make_small; all-green).
const bufferPushChain = <A>(x: Elt<A>, b: Buf<Elt<A>>): Chain<A> => {
  if (b.length < 5) return end([x, ...b]);
  return consG(pnode([x, b[0]!, b[1]!], hole(), [b[2]!, b[3]!, b[4]!]), end([]));
};
const bufferInjectChain = <A>(b: Buf<Elt<A>>, x: Elt<A>): Chain<A> => {
  if (b.length < 5) return end([...b, x]);
  return consG(pnode([b[0]!, b[1]!, b[2]!], hole(), [b[3]!, b[4]!, x]), end([]));
};

const mkEndingFromOptions = <A>(
  p1: Elt<A> | null,
  mid: readonly [Elt<A>, Elt<A>] | null,
  s1: Elt<A> | null,
): Chain<A> => {
  const xs: Elt<A>[] = [];
  if (p1 !== null) xs.push(p1);
  if (mid !== null) xs.push(mid[0], mid[1]);
  if (s1 !== null) xs.push(s1);
  return end(xs);
};

// ===================================================================
//  make_small: the bottommost-level repair (green_of_red, p0 = Hole,
//  tail = Ending).  kTDeque.ml:1054–1160.  Produces an all-green chain
//  (chain_to_kchain_g tags it green; we build green cons directly).
// ===================================================================
const makeSmall = <A>(b1: Buf<Elt<A>>, b2: Buf<Elt<A>>, b3: Buf<Elt<A>>): Chain<A> | null => {
  const pd = B.prefixDecompose(b1);
  const sd = B.suffixDecompose(b3);
  if (pd.tag === "under") {
    if (sd.tag === "under") {
      const us = B.bufferUnsandwich(b2);
      if (us.tag === "alone") {
        if (us.x !== null) {
          const pe = unpair(us.x);
          return pe === null ? null : mkEndingFromOptions(pd.x, pe, sd.x);
        }
        return mkEndingFromOptions(pd.x, null, sd.x);
      }
      const pab = unpair(us.first);
      if (pab === null) return null;
      const pcd = unpair(us.last);
      if (pcd === null) return null;
      return consG(pnode(B.prefix23(pd.x, pab), hole(), B.suffix23(pcd, sd.x)), end(us.mid));
    } else if (sd.tag === "ok") {
      const pop = B.popNaive(b2);
      if (pop !== null) {
        const pcd = unpair(pop[0]);
        return pcd === null ? null : consG(pnode(B.prefix23(pd.x, pcd), hole(), sd.b), end(pop[1]));
      }
      if (pd.x !== null) {
        const s = B.pushNaive(pd.x, sd.b);
        return s === null ? null : end(s);
      }
      return end(sd.b);
    } else {
      if (level(sd.a) !== level(sd.b2)) return null;
      const [cdPaired, center] = B.suffixRot(b2, pair(sd.a, sd.b2));
      const pcd = unpair(cdPaired);
      return pcd === null ? null : consG(pnode(B.prefix23(pd.x, pcd), hole(), sd.b), end(center));
    }
  } else if (pd.tag === "ok") {
    if (sd.tag === "under") {
      const ej = B.ejectNaive(b2);
      if (ej !== null) {
        const pab = unpair(ej[1]);
        return pab === null ? null : consG(pnode(pd.b, hole(), B.suffix23(pab, sd.x)), end(ej[0]));
      }
      if (sd.x !== null) {
        const p = B.injectNaive(pd.b, sd.x);
        return p === null ? null : end(p);
      }
      return end(pd.b);
    } else if (sd.tag === "ok") {
      return consG(pnode(pd.b, hole(), sd.b), end(b2));
    } else {
      if (level(sd.a) !== level(sd.b2)) return null;
      return consG(pnode(pd.b, hole(), sd.b), bufferInjectChain(b2, pair(sd.a, sd.b2)));
    }
  } else {
    if (level(pd.c) !== level(pd.d)) return null;
    if (sd.tag === "under") {
      const [center, abPaired] = B.prefixRot(pair(pd.c, pd.d), b2);
      const pab = unpair(abPaired);
      return pab === null ? null : consG(pnode(pd.b, hole(), B.suffix23(pab, sd.x)), end(center));
    } else if (sd.tag === "ok") {
      return consG(pnode(pd.b, hole(), sd.b), bufferPushChain(pair(pd.c, pd.d), b2));
    } else {
      if (level(sd.a) !== level(sd.b2)) return null;
      const cdPaired = pair(pd.c, pd.d);
      const abPaired = pair(sd.a, sd.b2);
      const [midOpt, restPairs] = B.bufferHalve(b2);
      const rest = pairEachBuf(restPairs);
      if (rest === null) return null;
      const p2 = B.suffix12(cdPaired, midOpt);
      return consG(pnode(pd.b, pnode(p2, hole(), [abPaired]), sd.b), end(rest));
    }
  }
};

// ===================================================================
//  green_of_red_k: the bounded repair (kTDeque.ml:1374–1414).  Fires
//  only on a Red-tagged top; exactly one of three cases; NO recursion.
// ===================================================================
const greenOfRedK = <A>(c: Chain<A>): Chain<A> | null => {
  if (c.tag === "end" || c.color !== "red") return null;
  const p = c.p;
  if (p.tag === "hole") return null;
  const { pre: pre1, inner: p0, suf: suf1 } = p;
  if (p0.tag === "hole") {
    const c1 = c.c;
    if (c1.tag === "end") return makeSmall(pre1, c1.b, suf1);
    const p1 = c1.p;
    if (p1.tag === "hole") return null;
    const { pre: pre2, inner: child, suf: suf2 } = p1;
    const gp = greenPrefixConcat(pre1, pre2);
    if (gp === null) return null;
    const gs = greenSuffixConcat(suf2, suf1);
    if (gs === null) return null;
    return consG(pnode(gp[0], pnode(gp[1], child, gs[0]), gs[1]), c1.c);
  }
  const { pre: pre2, inner: child, suf: suf2 } = p0;
  const pc = prefixConcat(pre1, pre2);
  if (pc === null) return null;
  const sc = suffixConcat(suf2, suf1);
  if (sc === null) return null;
  return consG(pnode(pc[0], hole(), sc[1]), cons("red", pnode(pc[1], child, sc[0]), c.c));
};

const ensureGreenK = <A>(c: Chain<A>): Chain<A> | null =>
  c.tag === "cons" && c.color === "red" ? greenOfRedK(c) : c;

const makeYellowK = <A>(pre: Buf<Elt<A>>, i: Packet<A>, suf: Buf<Elt<A>>, c: Chain<A>): Chain<A> | null => {
  const cp = ensureGreenK(c);
  return cp === null ? null : cons("yellow", pnode(pre, i, suf), cp);
};

const makeRedK = <A>(pre: Buf<Elt<A>>, i: Packet<A>, suf: Buf<Elt<A>>, c: Chain<A>): Chain<A> | null =>
  greenOfRedK(cons("red", pnode(pre, i, suf), c));

// ===================================================================
//  The four operations (push_kt2/inject_kt2/pop_kt2/eject_kt2): dispatch
//  on the stored colour TAG (kTDeque.ml:1442–1565).
// ===================================================================
export const pushKt = <A>(x: Elt<A>, c: Chain<A>): Chain<A> | null => {
  if (c.tag === "end") {
    const b = B.pushNaive(x, c.b);
    if (b !== null) return end(b);
    if (c.b.length !== 5) return null;
    const o = c.b;
    return consG(pnode([x, o[0]!, o[1]!], hole(), [o[2]!, o[3]!, o[4]!]), end([]));
  }
  const p = c.p;
  if (p.tag === "hole") return null;
  switch (c.color) {
    case "green": {
      const pre = B.greenPush(x, p.pre);
      return pre === null ? null : makeYellowK(pre, p.inner, p.suf, c.c);
    }
    case "yellow": {
      const pre = B.yellowPush(x, p.pre);
      return pre === null ? null : makeRedK(pre, p.inner, p.suf, c.c);
    }
    case "red":
      return null;
  }
};

export const injectKt = <A>(c: Chain<A>, x: Elt<A>): Chain<A> | null => {
  if (c.tag === "end") {
    const b = B.injectNaive(c.b, x);
    if (b !== null) return end(b);
    if (c.b.length !== 5) return null;
    const o = c.b;
    return consG(pnode([o[0]!, o[1]!, o[2]!], hole(), [o[3]!, o[4]!, x]), end([]));
  }
  const p = c.p;
  if (p.tag === "hole") return null;
  switch (c.color) {
    case "green": {
      const suf = B.greenInject(p.suf, x);
      return suf === null ? null : makeYellowK(p.pre, p.inner, suf, c.c);
    }
    case "yellow": {
      const suf = B.yellowInject(p.suf, x);
      return suf === null ? null : makeRedK(p.pre, p.inner, suf, c.c);
    }
    case "red":
      return null;
  }
};

export const popKt = <A>(c: Chain<A>): [Elt<A>, Chain<A>] | null => {
  if (c.tag === "end") {
    const r = B.popNaive(c.b);
    return r === null ? null : [r[0], end(r[1])];
  }
  const p = c.p;
  if (p.tag === "hole") return null;
  switch (c.color) {
    case "green": {
      const r = B.greenPop(p.pre);
      if (r === null) return null;
      const c2 = makeYellowK(r[1], p.inner, p.suf, c.c);
      return c2 === null ? null : [r[0], c2];
    }
    case "yellow": {
      const r = B.yellowPop(p.pre);
      if (r === null) return null;
      const c2 = makeRedK(r[1], p.inner, p.suf, c.c);
      return c2 === null ? null : [r[0], c2];
    }
    case "red":
      return null;
  }
};

export const ejectKt = <A>(c: Chain<A>): [Chain<A>, Elt<A>] | null => {
  if (c.tag === "end") {
    const r = B.ejectNaive(c.b);
    return r === null ? null : [end(r[0]), r[1]];
  }
  const p = c.p;
  if (p.tag === "hole") return null;
  switch (c.color) {
    case "green": {
      const r = B.greenEject(p.suf);
      if (r === null) return null;
      const c2 = makeYellowK(p.pre, p.inner, r[0], c.c);
      return c2 === null ? null : [c2, r[1]];
    }
    case "yellow": {
      const r = B.yellowEject(p.suf);
      if (r === null) return null;
      const c2 = makeRedK(p.pre, p.inner, r[0], c.c);
      return c2 === null ? null : [c2, r[1]];
    }
    case "red":
      return null;
  }
};

// ===================================================================
//  Public, element-level API.
// ===================================================================
export const emptyChain = <A>(): Chain<A> => end([]);

const unwrap = <A>(e: Elt<A>): A => {
  if (e.tag === "base") return e.v;
  const xs = eltToList(e);
  if (xs.length !== 1) throw new Error("ktdeque: popped element is not at level 0");
  return xs[0]!;
};

const must = <T>(x: T | null, op: string): T => {
  if (x === null) throw new Error(`ktdeque: ${op} returned null on a regular deque (invariant violation)`);
  return x;
};

export const push = <A>(x: A, c: Chain<A>): Chain<A> => must(pushKt(base(x), c), "push");
export const inject = <A>(c: Chain<A>, x: A): Chain<A> => must(injectKt(c, base(x)), "inject");
export const pop = <A>(c: Chain<A>): [A, Chain<A>] | null => {
  const r = popKt(c);
  return r === null ? null : [unwrap(r[0]), r[1]];
};
export const eject = <A>(c: Chain<A>): [Chain<A>, A] | null => {
  const r = ejectKt(c);
  return r === null ? null : [r[0], unwrap(r[1])];
};

export const toList = <A>(c: Chain<A>): A[] => chainSeq(c);
export const length = <A>(c: Chain<A>): number => chainSeq(c).length;

// ===================================================================
//  Regularity invariant check (analogue of C `kt_check_regular`,
//  matching `regular_kt`): reading anchor TAGS top→bottom, the top is
//  non-Red and no Yellow/Red anchor is followed by a Red one.
// ===================================================================
const headColor = <A>(c: Chain<A>): Color => (c.tag === "end" ? "green" : c.color);

export function checkRegular<A>(c: Chain<A>): { ok: true } | { ok: false; reason: string } {
  let cur: Chain<A> = c;
  let first = true;
  while (cur.tag === "cons") {
    if (cur.p.tag === "hole") return { ok: false, reason: "cons node carries a Hole packet" };
    if (first && cur.color === "red") return { ok: false, reason: "top anchor is Red after the operation" };
    if ((cur.color === "yellow" || cur.color === "red") && headColor(cur.c) === "red")
      return { ok: false, reason: "a Yellow/Red anchor is followed by a Red anchor (two Reds adjacent)" };
    first = false;
    cur = cur.c;
  }
  return { ok: true };
}
