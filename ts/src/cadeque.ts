/**
 * Section-6 Kaplan–Tarjan CATENABLE deque: purely-functional, worst-case O(1)
 * per operation INCLUDING `concat`.
 *
 * Faithful port of the Rocq-extracted implementation
 * `ocaml/extracted/kTCadeque.ml` (from `rocq/KTDeque/Catenable/`).  Buffers are
 * plain lists; the structure is a tree (`cchain`) of stored triples with the
 * four-colour rule (green ≥8 / yellow 7 / orange 6 / red 5).  `concat` rearranges
 * a constant number of cells at the root and shares both operands wholesale.
 *
 * Verified by `test/fuzz6.ts` (differential vs a naive list oracle, concat
 * included), the `test/wc.ts` cost bound, and a byte-for-byte trace diff against
 * this very OCaml extraction (`test/difftrace.ts` ↔ `ocaml/.../difftrace6`).
 */
import { bump } from "./alloc.js";

// ===================================================================
//  Types (kTCadeque.ml:60–85).  Buffers are lists (arrays).
// ===================================================================
export type Kind = "only" | "left" | "right";
type Buf<T> = readonly T[];

export type Stored<A> =
  | { readonly tag: "ground"; readonly v: A }
  | { readonly tag: "small"; readonly b: Buf<Stored<A>> }
  | { readonly tag: "big"; readonly pre: Buf<Stored<A>>; readonly child: Cchain<A>; readonly suf: Buf<Stored<A>> };

export type Cnode<A> = { readonly tag: "node"; readonly k: Kind; readonly pre: Buf<Stored<A>>; readonly suf: Buf<Stored<A>> };

export type Cbody<A> =
  | { readonly tag: "bhole" }
  | { readonly tag: "bsingle"; readonly n: Cnode<A>; readonly b: Cbody<A> }
  | { readonly tag: "bpairY"; readonly n: Cnode<A>; readonly b: Cbody<A>; readonly rc: Cchain<A> }
  | { readonly tag: "bpairO"; readonly n: Cnode<A>; readonly lc: Cchain<A>; readonly b: Cbody<A> };

export type Cpacket<A> = { readonly tag: "pkt"; readonly body: Cbody<A>; readonly n: Cnode<A> };

export type Cchain<A> =
  | { readonly tag: "cempty" }
  | { readonly tag: "csingle"; readonly p: Cpacket<A>; readonly rest: Cchain<A> }
  | { readonly tag: "cpair"; readonly l: Cchain<A>; readonly r: Cchain<A> };

// constructors (bump = one persistent node, for the worst-case cost test)
const sground = <A>(v: A): Stored<A> => ({ tag: "ground", v });
const ssmall = <A>(b: Buf<Stored<A>>): Stored<A> => (bump(), { tag: "small", b });
const sbig = <A>(pre: Buf<Stored<A>>, child: Cchain<A>, suf: Buf<Stored<A>>): Stored<A> =>
  (bump(), { tag: "big", pre, child, suf });
const node = <A>(k: Kind, pre: Buf<Stored<A>>, suf: Buf<Stored<A>>): Cnode<A> =>
  (bump(), { tag: "node", k, pre, suf });
const BHOLE: Cbody<never> = { tag: "bhole" };
const bhole = <A>(): Cbody<A> => BHOLE as Cbody<A>;
const bsingle = <A>(n: Cnode<A>, b: Cbody<A>): Cbody<A> => (bump(), { tag: "bsingle", n, b });
const bpairY = <A>(n: Cnode<A>, b: Cbody<A>, rc: Cchain<A>): Cbody<A> => (bump(), { tag: "bpairY", n, b, rc });
const bpairO = <A>(n: Cnode<A>, lc: Cchain<A>, b: Cbody<A>): Cbody<A> => (bump(), { tag: "bpairO", n, lc, b });
const pkt = <A>(body: Cbody<A>, n: Cnode<A>): Cpacket<A> => (bump(), { tag: "pkt", body, n });
const CEMPTY: Cchain<never> = { tag: "cempty" };
const cempty = <A>(): Cchain<A> => CEMPTY as Cchain<A>;
const csingle = <A>(p: Cpacket<A>, rest: Cchain<A>): Cchain<A> => (bump(), { tag: "csingle", p, rest });
const cpair = <A>(l: Cchain<A>, r: Cchain<A>): Cchain<A> => (bump(), { tag: "cpair", l, r });

// list helpers (= OCaml app / rev / fold)
const app = <T>(a: Buf<T>, b: Buf<T>): Buf<T> => a.concat(b);

export const cadEmpty = <A>(): Cchain<A> => cempty();

// ===================================================================
//  Sequence semantics (kTCadeque.ml:92–154).
// ===================================================================
const storedSeq = <A>(s: Stored<A>): A[] => {
  if (s.tag === "ground") return [s.v];
  if (s.tag === "small") return s.b.flatMap(storedSeq);
  return s.pre.flatMap(storedSeq).concat(cchainSeq(s.child), s.suf.flatMap(storedSeq));
};
const cnodeSeq = <A>(n: Cnode<A>, mid: A[]): A[] =>
  n.pre.flatMap(storedSeq).concat(mid, n.suf.flatMap(storedSeq));
const cbodySeq = <A>(b: Cbody<A>, inner: A[]): A[] => {
  switch (b.tag) {
    case "bhole":
      return inner;
    case "bsingle":
      return cnodeSeq(b.n, cbodySeq(b.b, inner));
    case "bpairY":
      return cnodeSeq(b.n, cbodySeq(b.b, inner).concat(cchainSeq(b.rc)));
    case "bpairO":
      return cnodeSeq(b.n, cchainSeq(b.lc).concat(cbodySeq(b.b, inner)));
  }
};
const cpacketSeq = <A>(p: Cpacket<A>, inner: A[]): A[] => cbodySeq(p.body, cnodeSeq(p.n, inner));
const cchainSeq = <A>(c: Cchain<A>): A[] => {
  switch (c.tag) {
    case "cempty":
      return [];
    case "csingle":
      return cpacketSeq(c.p, cchainSeq(c.rest));
    case "cpair":
      return cchainSeq(c.l).concat(cchainSeq(c.r));
  }
};
export const cadToList = <A>(c: Cchain<A>): A[] => cchainSeq(c);

// ===================================================================
//  Colours (kTCadeque.ml:156–192).
// ===================================================================
export type Gyor = "CG" | "CY" | "CO" | "CR";
export const nodeColor = <A>(hasChild: boolean, n: Cnode<A>): Gyor => {
  if (!hasChild) return "CG";
  const m = n.k === "only" ? Math.min(n.pre.length, n.suf.length) : n.k === "left" ? n.pre.length : n.suf.length;
  return m >= 8 ? "CG" : m === 7 ? "CY" : m === 6 ? "CO" : "CR";
};
export const chainHasNode = <A>(c: Cchain<A>): boolean => c.tag !== "cempty";

// ===================================================================
//  Node + buffer helpers (kTCadeque.ml:194–311).
// ===================================================================
const nodePush = <A>(s: Stored<A>, n: Cnode<A>): Cnode<A> =>
  n.pre.length === 0 ? node(n.k, [], [s, ...n.suf]) : node(n.k, [s, ...n.pre], n.suf);
const nodeInject = <A>(n: Cnode<A>, s: Stored<A>): Cnode<A> =>
  n.suf.length === 0 ? node(n.k, app(n.pre, [s]), []) : node(n.k, n.pre, app(n.suf, [s]));

const bufPop2 = <T>(b: Buf<T>): [[T, T], Buf<T>] | null =>
  b.length >= 2 ? [[b[0]!, b[1]!], b.slice(2)] : null;
const bufEject2 = <T>(b: Buf<T>): [[Buf<T>, T], T] | null =>
  b.length >= 2 ? [[b.slice(0, -2), b[b.length - 2]!], b[b.length - 1]!] : null;
const bufEject3 = <T>(b: Buf<T>): [[[Buf<T>, T], T], T] | null =>
  b.length >= 3 ? [[[b.slice(0, -3), b[b.length - 3]!], b[b.length - 2]!], b[b.length - 1]!] : null;

// root_and_child: peel the head node off a packet, re-threading its body.
export const rootAndChild = <A>(p: Cpacket<A>, rest: Cchain<A>): [Cnode<A>, Cchain<A>] => {
  const c = p.body;
  switch (c.tag) {
    case "bhole":
      return [p.n, rest];
    case "bsingle":
      return [c.n, csingle(pkt(c.b, p.n), rest)];
    case "bpairY":
      return [c.n, cpair(csingle(pkt(c.b, p.n), rest), c.rc)];
    case "bpairO":
      return [c.n, cpair(c.lc, csingle(pkt(c.b, p.n), rest))];
  }
};

// tree_of: the colour-driven smart constructor (kTCadeque.ml:223–249).
const treeOf = <A>(n: Cnode<A>, child: Cchain<A>): Cchain<A> => {
  const col = nodeColor(chainHasNode(child), n);
  if (col === "CY") {
    if (child.tag === "cempty") return csingle(pkt(bhole(), n), child);
    if (child.tag === "csingle") return csingle(pkt(bsingle(n, child.p.body), child.p.n), child.rest);
    // cpair
    if (child.l.tag === "csingle")
      return csingle(pkt(bpairY(n, child.l.p.body, child.r), child.l.p.n), child.l.rest);
    return csingle(pkt(bhole(), n), child);
  }
  if (col === "CO") {
    if (child.tag === "cempty") return csingle(pkt(bhole(), n), child);
    if (child.tag === "csingle") return csingle(pkt(bsingle(n, child.p.body), child.p.n), child.rest);
    // cpair
    if (child.r.tag === "csingle")
      return csingle(pkt(bpairO(n, child.l, child.r.p.body), child.r.p.n), child.r.rest);
    return csingle(pkt(bhole(), n), child);
  }
  return csingle(pkt(bhole(), n), child);
};

const pktUpdate = <A>(upd: (n: Cnode<A>) => Cnode<A>, p: Cpacket<A>, rest: Cchain<A>): Cchain<A> => {
  const [n, child] = rootAndChild(p, rest);
  return treeOf(upd(n), child);
};

// ===================================================================
//  push / inject (kTCadeque.ml:257–280).
// ===================================================================
const pushChain = <A>(s: Stored<A>, c: Cchain<A>): Cchain<A> => {
  switch (c.tag) {
    case "cempty":
      return csingle(pkt(bhole(), node("only", [s], [])), cempty());
    case "csingle":
      return pktUpdate((n) => nodePush(s, n), c.p, c.rest);
    case "cpair":
      return cpair(pushChain(s, c.l), c.r);
  }
};
const injectChain = <A>(c: Cchain<A>, s: Stored<A>): Cchain<A> => {
  switch (c.tag) {
    case "cempty":
      return csingle(pkt(bhole(), node("only", [], [s])), cempty());
    case "csingle":
      return pktUpdate((n) => nodeInject(n, s), c.p, c.rest);
    case "cpair":
      return cpair(c.l, injectChain(c.r, s));
  }
};

export const cadPush = <A>(x: A, d: Cchain<A>): Cchain<A> => pushChain(sground(x), d);
export const cadInject = <A>(d: Cchain<A>, x: A): Cchain<A> => injectChain(d, sground(x));

// ===================================================================
//  concat (kTCadeque.ml:313–584).
// ===================================================================
const degenerateBuf = <A>(c: Cchain<A>): Buf<Stored<A>> | null => {
  if (c.tag !== "csingle" || c.p.body.tag !== "bhole" || c.rest.tag !== "cempty") return null;
  const n = c.p.n;
  if (n.k !== "only") return null;
  if (n.pre.length === 0) return n.suf;
  if (n.suf.length === 0) return n.pre;
  return null;
};

const makeLeftOnly = <A>(p1: Buf<Stored<A>>, d1: Cchain<A>, s1: Buf<Stored<A>>): Cchain<A> | null => {
  if (d1.tag === "cempty") {
    if (s1.length <= 8) {
      const e = bufEject2(s1);
      if (e === null) return null;
      const [[s1p, y], z] = e;
      return treeOf(node("left", app(p1, s1p), [y, z]), cempty());
    }
    if (s1.length < 3) return null;
    const [a, b, c] = [s1[0]!, s1[1]!, s1[2]!];
    const srest = s1.slice(3);
    const e = bufEject2(srest);
    if (e === null) return null;
    const [[smid, y], z] = e;
    return treeOf(node("left", app(p1, [a, b, c]), [y, z]), pushChain(ssmall(smid), cempty()));
  }
  const e = bufEject2(s1);
  if (e === null) return null;
  const [[s1p, y], z] = e;
  return treeOf(node("left", p1, [y, z]), injectChain(d1, ssmall(s1p)));
};

const makeLeft = <A>(c: Cchain<A>): Cchain<A> | null => {
  if (c.tag === "cempty") return null;
  if (c.tag === "csingle") {
    const [n, d1] = rootAndChild(c.p, c.rest);
    return makeLeftOnly(n.pre, d1, n.suf);
  }
  // cpair
  if (c.l.tag !== "csingle" || c.r.tag !== "csingle") return null;
  const [n1, d1] = rootAndChild(c.l.p, c.l.rest);
  const [n2, d2] = rootAndChild(c.r.p, c.r.rest);
  if (d1.tag === "cempty") return makeLeftOnly(app(n1.pre, app(n1.suf, n2.pre)), d2, n2.suf);
  const e = bufEject2(n2.suf);
  if (e === null) return null;
  const [[s2p, y], z] = e;
  return treeOf(node("left", n1.pre, [y, z]), injectChain(d1, sbig(app(n1.suf, n2.pre), d2, s2p)));
};

const makeRightOnly = <A>(p1: Buf<Stored<A>>, d1: Cchain<A>, s1: Buf<Stored<A>>): Cchain<A> | null => {
  if (d1.tag === "cempty") {
    if (p1.length <= 8) {
      const pp = bufPop2(p1);
      if (pp === null) return null;
      const [[x, y], p1p] = pp;
      return treeOf(node("right", [x, y], app(p1p, s1)), cempty());
    }
    const pp = bufPop2(p1);
    if (pp === null) return null;
    const [[x, y], p1p] = pp;
    const e = bufEject3(p1p);
    if (e === null) return null;
    const [[[pmid, a], b], c] = e;
    return treeOf(node("right", [x, y], app([a, b, c], s1)), pushChain(ssmall(pmid), cempty()));
  }
  const pp = bufPop2(p1);
  if (pp === null) return null;
  const [[x, y], p1p] = pp;
  return treeOf(node("right", [x, y], s1), pushChain(ssmall(p1p), d1));
};

const makeRight = <A>(c: Cchain<A>): Cchain<A> | null => {
  if (c.tag === "cempty") return null;
  if (c.tag === "csingle") {
    const [n, d1] = rootAndChild(c.p, c.rest);
    return makeRightOnly(n.pre, d1, n.suf);
  }
  if (c.l.tag !== "csingle" || c.r.tag !== "csingle") return null;
  const [n1, d1] = rootAndChild(c.l.p, c.l.rest);
  const [n2, d2] = rootAndChild(c.r.p, c.r.rest);
  if (d2.tag === "cempty") return makeRightOnly(n1.pre, d1, app(n1.suf, app(n2.pre, n2.suf)));
  const pp = bufPop2(n1.pre);
  if (pp === null) return null;
  const [[x, y], p1p] = pp;
  return treeOf(node("right", [x, y], n2.suf), pushChain(sbig(p1p, d1, app(n1.suf, n2.pre)), d2));
};

const concatSmallLeft = <A>(p3: Buf<Stored<A>>, e: Cchain<A>): Cchain<A> | null => {
  if (p3.length < 8) return p3.reduceRight<Cchain<A>>((acc, x) => pushChain(x, acc), e);
  if (e.tag === "cempty") return null;
  if (e.tag === "csingle") {
    const [n2, d2] = rootAndChild(e.p, e.rest);
    if (d2.tag === "cempty") {
      const ej = bufEject2(n2.pre);
      if (ej === null) return null;
      const [[p2p, y], z] = ej;
      return treeOf(node("only", p3, [y, z, ...n2.suf]), pushChain(ssmall(p2p), cempty()));
    }
    return treeOf(node("only", p3, n2.suf), pushChain(ssmall(n2.pre), d2));
  }
  // cpair
  if (e.l.tag !== "csingle") return null;
  const [n2, d2] = rootAndChild(e.l.p, e.l.rest);
  return cpair(treeOf(node("left", p3, n2.suf), pushChain(ssmall(n2.pre), d2)), e.r);
};

const concatSmallRight = <A>(d: Cchain<A>, s3: Buf<Stored<A>>): Cchain<A> | null => {
  if (s3.length < 8) return s3.reduce<Cchain<A>>((acc, x) => injectChain(acc, x), d);
  if (d.tag === "cempty") return null;
  if (d.tag === "csingle") {
    const [n1, d1] = rootAndChild(d.p, d.rest);
    if (d1.tag === "cempty") {
      const pp = bufPop2(n1.suf);
      if (pp === null) return null;
      const [[x, y], s1p] = pp;
      return treeOf(node("only", app(n1.pre, [x, y]), s3), pushChain(ssmall(s1p), cempty()));
    }
    return treeOf(node("only", n1.pre, s3), injectChain(d1, ssmall(n1.suf)));
  }
  if (d.r.tag !== "csingle") return null;
  const [n1, d1] = rootAndChild(d.r.p, d.r.rest);
  return cpair(d.l, treeOf(node("right", n1.pre, s3), injectChain(d1, ssmall(n1.suf))));
};

export const cadConcat = <A>(d: Cchain<A>, e: Cchain<A>): Cchain<A> | null => {
  if (d.tag === "cempty") return e;
  if (e.tag === "cempty") return d;
  const p = degenerateBuf(d);
  if (p !== null) {
    const s = degenerateBuf(e);
    if (s !== null) {
      if (p.length < 8 || s.length < 8) return csingle(pkt(bhole(), node("only", app(p, s), [])), cempty());
      return csingle(pkt(bhole(), node("only", p, s)), cempty());
    }
    return concatSmallLeft(p, e);
  }
  const s = degenerateBuf(e);
  if (s !== null) return concatSmallRight(d, s);
  const t = makeLeft(d);
  if (t === null) return null;
  const u = makeRight(e);
  if (u === null) return null;
  return cpair(t, u);
};

// ===================================================================
//  pop / eject + the pop/eject-side repair (kTCadeque.ml:586–1043).
// ===================================================================
const nodePop = <A>(n: Cnode<A>): [Stored<A>, Cnode<A>] | null => {
  if (n.pre.length === 0) {
    if (n.suf.length === 0) return null;
    return [n.suf[0]!, node(n.k, [], n.suf.slice(1))];
  }
  return [n.pre[0]!, node(n.k, n.pre.slice(1), n.suf)];
};
const nodeEject = <A>(n: Cnode<A>): [Cnode<A>, Stored<A>] | null => {
  if (n.suf.length === 0) {
    if (n.pre.length === 0) return null;
    return [node(n.k, n.pre.slice(0, -1), []), n.pre[n.pre.length - 1]!];
  }
  return [node(n.k, n.pre, n.suf.slice(0, -1)), n.suf[n.suf.length - 1]!];
};

const rebuildChildless = <A>(n: Cnode<A>): Cchain<A> => {
  if (n.k === "only") {
    if (n.pre.length === 0 && n.suf.length === 0) return cempty();
    if (n.pre.length === 0 || n.suf.length === 0) return csingle(pkt(bhole(), n), cempty());
    if (n.pre.length < 5 || n.suf.length < 5)
      return csingle(pkt(bhole(), node("only", app(n.pre, n.suf), [])), cempty());
    return csingle(pkt(bhole(), n), cempty());
  }
  if (n.pre.length === 0 && n.suf.length === 0) return cempty();
  return csingle(pkt(bhole(), n), cempty());
};

const popRaw = <A>(c: Cchain<A>): [Stored<A>, Cchain<A>] | null => {
  if (c.tag === "cempty") return null;
  if (c.tag === "csingle") {
    const [n, child] = rootAndChild(c.p, c.rest);
    const np = nodePop(n);
    if (np === null) return null;
    const [x, np2] = np;
    return [x, child.tag === "cempty" ? rebuildChildless(np2) : treeOf(np2, child)];
  }
  // cpair
  const lp = popRaw(c.l);
  if (lp === null) return null;
  const [x, lprime] = lp;
  if (lprime.tag === "cempty") return [x, c.r];
  if (lprime.tag === "csingle" && lprime.p.body.tag === "bhole" && lprime.rest.tag === "cempty") {
    const ln = lprime.p.n;
    if (ln.pre.length < 4 && c.r.tag === "csingle") {
      const [n2, d2] = rootAndChild(c.r.p, c.r.rest);
      return [x, treeOf(node("only", app(ln.pre, app(ln.suf, n2.pre)), n2.suf), d2)];
    }
    if (ln.pre.length < 4 && c.r.tag !== "csingle") return null;
  }
  return [x, cpair(lprime, c.r)];
};

const ejectRaw = <A>(c: Cchain<A>): [Cchain<A>, Stored<A>] | null => {
  if (c.tag === "cempty") return null;
  if (c.tag === "csingle") {
    const [n, child] = rootAndChild(c.p, c.rest);
    const ne = nodeEject(n);
    if (ne === null) return null;
    const [ne2, x] = ne;
    return [child.tag === "cempty" ? rebuildChildless(ne2) : treeOf(ne2, child), x];
  }
  const re = ejectRaw(c.r);
  if (re === null) return null;
  const [rprime, x] = re;
  if (rprime.tag === "cempty") return [c.l, x];
  if (rprime.tag === "csingle" && rprime.p.body.tag === "bhole" && rprime.rest.tag === "cempty") {
    const rn = rprime.p.n;
    if (rn.suf.length < 4 && c.l.tag === "csingle") {
      const [n1, d1] = rootAndChild(c.l.p, c.l.rest);
      return [treeOf(node("only", n1.pre, app(n1.suf, app(rn.pre, rn.suf))), d1), x];
    }
    if (rn.suf.length < 4 && c.l.tag !== "csingle") return null;
  }
  return [cpair(c.l, rprime), x];
};

const repairFront = <A>(
  k: Kind,
  body: Cbody<A>,
  p1: Buf<Stored<A>>,
  s1: Buf<Stored<A>>,
  rest: Cchain<A>,
): Cchain<A> | null => {
  const pr = popRaw(rest);
  if (pr === null) return null;
  const [s, d1p] = pr;
  if (s.tag === "ground") return null;
  if (s.tag === "small") return csingle(pkt(body, node(k, app(p1, s.b), s1)), d1p);
  const d3 = cadConcat(s.child, pushChain(ssmall(s.suf), d1p));
  return d3 === null ? null : csingle(pkt(body, node(k, app(p1, s.pre), s1)), d3);
};

const repairBack = <A>(
  k: Kind,
  body: Cbody<A>,
  p1: Buf<Stored<A>>,
  s1: Buf<Stored<A>>,
  rest: Cchain<A>,
): Cchain<A> | null => {
  const er = ejectRaw(rest);
  if (er === null) return null;
  const [d1p, s] = er;
  if (s.tag === "ground") return null;
  if (s.tag === "small") return csingle(pkt(body, node(k, p1, app(s.b, s1))), d1p);
  const d3 = cadConcat(injectChain(d1p, ssmall(s.pre)), s.child);
  return d3 === null ? null : csingle(pkt(body, node(k, p1, app(s.suf, s1))), d3);
};

const drainBoth = <A>(c: Cchain<A>): [[Stored<A>, Stored<A> | null], Cchain<A>] | null => {
  if (c.tag === "cempty") return null;
  if (c.tag === "csingle") {
    const [n, dd] = rootAndChild(c.p, c.rest);
    const np = nodePop(n);
    if (np === null) return null;
    const [cellF, n1] = np;
    const ne = nodeEject(n1);
    if (ne !== null) {
      const [n2, cellB] = ne;
      return [[cellF, cellB], dd.tag === "cempty" ? rebuildChildless(n2) : treeOf(n2, dd)];
    }
    return dd.tag === "cempty" ? [[cellF, null], cempty()] : null;
  }
  // cpair
  const lp = popRaw(c.l);
  if (lp === null) return null;
  const [cellF, lprime] = lp;
  const re = ejectRaw(c.r);
  if (re === null) return null;
  const [rprime, cellB] = re;
  const fallback: [[Stored<A>, Stored<A> | null], Cchain<A>] = [[cellF, cellB], cpair(lprime, rprime)];
  if (lprime.tag !== "csingle" || lprime.p.body.tag !== "bhole") return fallback;
  const ln = lprime.p.n;
  if (lprime.rest.tag === "cempty") {
    if (rprime.tag === "csingle" && rprime.p.body.tag === "bhole") {
      const rn = rprime.p.n;
      if (rprime.rest.tag === "cempty") {
        if (ln.pre.length < 5 || rn.suf.length < 5)
          return [[cellF, cellB], csingle(pkt(bhole(), node("only", app(ln.pre, ln.suf), app(rn.pre, rn.suf))), cempty())];
        return fallback;
      }
      if (ln.pre.length < 5) {
        const [n2, d2] = rootAndChild(rprime.p, rprime.rest);
        return [[cellF, cellB], treeOf(node("only", app(ln.pre, app(ln.suf, n2.pre)), n2.suf), d2)];
      }
      return fallback;
    }
    if (ln.pre.length < 5) {
      if (rprime.tag !== "csingle") return fallback;
      const [n2, d2] = rootAndChild(rprime.p, rprime.rest);
      return [[cellF, cellB], treeOf(node("only", app(ln.pre, app(ln.suf, n2.pre)), n2.suf), d2)];
    }
    return fallback;
  }
  // lprime.rest non-empty: try to borrow from the right
  if (rprime.tag === "csingle" && rprime.p.body.tag === "bhole" && rprime.rest.tag === "cempty") {
    const rn = rprime.p.n;
    if (rn.suf.length < 5) {
      const [n2, d2] = rootAndChild(lprime.p, lprime.rest);
      return [[cellF, cellB], treeOf(node("only", n2.pre, app(n2.suf, app(rn.pre, rn.suf))), d2)];
    }
  }
  return fallback;
};

const repairBoth = <A>(
  body: Cbody<A>,
  p1: Buf<Stored<A>>,
  s1: Buf<Stored<A>>,
  rest: Cchain<A>,
): Cchain<A> | null => {
  const db = drainBoth(rest);
  if (db === null) return null;
  const [[cellF, o], mid] = db;
  if (o !== null) {
    const cellB = o;
    let front: [Buf<Stored<A>>, Cchain<A>] | null;
    if (cellF.tag === "ground") front = null;
    else if (cellF.tag === "small") front = [cellF.b, mid];
    else {
      const d4 = cadConcat(cellF.child, pushChain(ssmall(cellF.suf), mid));
      front = d4 === null ? null : [cellF.pre, d4];
    }
    if (front === null) return null;
    const [pf, d4] = front;
    if (cellB.tag === "ground") return null;
    if (cellB.tag === "small") return csingle(pkt(body, node("only", app(p1, pf), app(cellB.b, s1))), d4);
    const d5 = cadConcat(injectChain(d4, ssmall(cellB.pre)), cellB.child);
    return d5 === null ? null : csingle(pkt(body, node("only", app(p1, pf), app(cellB.suf, s1))), d5);
  }
  if (cellF.tag === "ground") return null;
  if (cellF.tag === "small") return csingle(pkt(body, node("only", app(p1, cellF.b), s1)), cempty());
  return csingle(pkt(body, node("only", app(p1, cellF.pre), app(cellF.suf, s1))), cellF.child);
};

const repairPacket = <A>(p: Cpacket<A>, rest: Cchain<A>): Cchain<A> | null => {
  const { body, n } = p;
  if (nodeColor(chainHasNode(rest), n) !== "CR") return csingle(p, rest);
  if (n.k === "only") {
    if (n.suf.length >= 8) return repairFront("only", body, n.pre, n.suf, rest);
    if (n.pre.length >= 8) return repairBack("only", body, n.pre, n.suf, rest);
    return repairBoth(body, n.pre, n.suf, rest);
  }
  if (n.k === "left") return repairFront("left", body, n.pre, n.suf, rest);
  return repairBack("right", body, n.pre, n.suf, rest);
};

const repairPopSide = <A>(c: Cchain<A>): Cchain<A> | null => {
  if (c.tag === "cempty") return cempty();
  if (c.tag === "csingle") return repairPacket(c.p, c.rest);
  if (c.l.tag !== "csingle") return null;
  const lp = repairPacket(c.l.p, c.l.rest);
  return lp === null ? null : cpair(lp, c.r);
};
const repairEjectSide = <A>(c: Cchain<A>): Cchain<A> | null => {
  if (c.tag === "cempty") return cempty();
  if (c.tag === "csingle") return repairPacket(c.p, c.rest);
  if (c.r.tag !== "csingle") return null;
  const rp = repairPacket(c.r.p, c.r.rest);
  return rp === null ? null : cpair(c.l, rp);
};

const cadPopRaw = <A>(d: Cchain<A>): [A, Cchain<A>] | null => {
  const pr = popRaw(d);
  if (pr === null) return null;
  const [s, dp] = pr;
  if (s.tag !== "ground") return null;
  const dpp = repairPopSide(dp);
  return dpp === null ? null : [s.v, dpp];
};
const cadEjectRaw = <A>(d: Cchain<A>): [Cchain<A>, A] | null => {
  const er = ejectRaw(d);
  if (er === null) return null;
  const [dp, s] = er;
  if (s.tag !== "ground") return null;
  const dpp = repairEjectSide(dp);
  return dpp === null ? null : [dpp, s.v];
};

// ===================================================================
//  Public API (throws on the "impossible" null cases = invariant
//  violations, which the fuzzer surfaces).
// ===================================================================
const must = <T>(x: T | null, op: string): T => {
  if (x === null) throw new Error(`ktcadeque: ${op} returned null on a regular cadeque (invariant violation)`);
  return x;
};

export const cadConcatChecked = <A>(d: Cchain<A>, e: Cchain<A>): Cchain<A> => must(cadConcat(d, e), "concat");
export const cadPop = <A>(d: Cchain<A>): [A, Cchain<A>] | null => cadPopRaw(d);
export const cadEject = <A>(d: Cchain<A>): [Cchain<A>, A] | null => cadEjectRaw(d);
