"use strict";
var KTDeque = (() => {
  var __defProp = Object.defineProperty;
  var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
  var __getOwnPropNames = Object.getOwnPropertyNames;
  var __hasOwnProp = Object.prototype.hasOwnProperty;
  var __export = (target, all) => {
    for (var name in all)
      __defProp(target, name, { get: all[name], enumerable: true });
  };
  var __copyProps = (to, from, except, desc) => {
    if (from && typeof from === "object" || typeof from === "function") {
      for (let key of __getOwnPropNames(from))
        if (!__hasOwnProp.call(to, key) && key !== except)
          __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
    }
    return to;
  };
  var __toCommonJS = (mod) => __copyProps(__defProp({}, "__esModule", { value: true }), mod);

  // src/browser.ts
  var browser_exports = {};
  __export(browser_exports, {
    concat6: () => concat6,
    eject4: () => eject4,
    eject6: () => eject6,
    empty4: () => empty4,
    empty6: () => empty6,
    inject4: () => inject4,
    inject6: () => inject6,
    pop4: () => pop4,
    pop6: () => pop6,
    push4: () => push4,
    push6: () => push6,
    snapshot4: () => snapshot4,
    snapshot6: () => snapshot6,
    toList4: () => toList4,
    toList6: () => toList6
  });

  // src/alloc.ts
  var count = 0;
  function bump(n = 1) {
    count += n;
  }

  // src/element.ts
  function base(a) {
    return { tag: "base", lvl: 0, v: a };
  }
  function level(e) {
    return e.lvl;
  }
  function pair(x, y) {
    bump();
    return { tag: "pair", lvl: x.lvl + 1, l: x, r: y };
  }
  function unpair(e) {
    return e.tag === "pair" ? [e.l, e.r] : null;
  }
  function toList(e) {
    if (e.tag === "base") return [e.v];
    return toList(e.l).concat(toList(e.r));
  }

  // src/buf5.ts
  var bufColor = (b) => {
    const n = b.length;
    return n === 0 || n === 5 ? "red" : n === 1 || n === 4 ? "yellow" : "green";
  };
  var colorMeet = (a, b) => a === "red" || b === "red" ? "red" : a === "yellow" || b === "yellow" ? "yellow" : "green";
  var pushNaive = (x, b) => b.length < 5 ? [x, ...b] : null;
  var injectNaive = (b, x) => b.length < 5 ? [...b, x] : null;
  var popNaive = (b) => b.length > 0 ? [b[0], b.slice(1)] : null;
  var ejectNaive = (b) => b.length > 0 ? [b.slice(0, -1), b[b.length - 1]] : null;
  var inRange = (n, lo, hi) => n >= lo && n <= hi;
  var greenPush = (x, b) => inRange(b.length, 2, 3) ? [x, ...b] : null;
  var greenInject = (b, x) => inRange(b.length, 2, 3) ? [...b, x] : null;
  var greenPop = (b) => inRange(b.length, 2, 3) ? [b[0], b.slice(1)] : null;
  var greenEject = (b) => inRange(b.length, 2, 3) ? [b.slice(0, -1), b[b.length - 1]] : null;
  var yellowPush = (x, b) => inRange(b.length, 1, 4) ? [x, ...b] : null;
  var yellowInject = (b, x) => inRange(b.length, 1, 4) ? [...b, x] : null;
  var yellowPop = (b) => inRange(b.length, 1, 4) ? [b[0], b.slice(1)] : null;
  var yellowEject = (b) => inRange(b.length, 1, 4) ? [b.slice(0, -1), b[b.length - 1]] : null;
  var prefix23 = (opt, bc) => opt !== null ? [opt, bc[0], bc[1]] : [bc[0], bc[1]];
  var suffix23 = (ab, opt) => opt !== null ? [ab[0], ab[1], opt] : [ab[0], ab[1]];
  var suffix12 = (x, opt) => opt !== null ? [x, opt] : [x];
  var prefixDecompose = (b) => {
    switch (b.length) {
      case 0:
        return { tag: "under", x: null };
      case 1:
        return { tag: "under", x: b[0] };
      case 4:
        return { tag: "over", b: [b[0], b[1]], c: b[2], d: b[3] };
      case 5:
        return { tag: "over", b: [b[0], b[1], b[2]], c: b[3], d: b[4] };
      default:
        return { tag: "ok", b };
    }
  };
  var suffixDecompose = (b) => {
    switch (b.length) {
      case 0:
        return { tag: "under", x: null };
      case 1:
        return { tag: "under", x: b[0] };
      case 4:
        return { tag: "over", b: [b[2], b[3]], a: b[0], b2: b[1] };
      case 5:
        return { tag: "over", b: [b[2], b[3], b[4]], a: b[0], b2: b[1] };
      default:
        return { tag: "ok", b };
    }
  };
  var bufferUnsandwich = (b) => {
    if (b.length === 0) return { tag: "alone", x: null };
    if (b.length === 1) return { tag: "alone", x: b[0] };
    return { tag: "sandwich", first: b[0], mid: b.slice(1, -1), last: b[b.length - 1] };
  };
  var prefixRot = (x, b) => b.length === 0 ? [[], x] : [[x, ...b.slice(0, -1)], b[b.length - 1]];
  var suffixRot = (b, x) => b.length === 0 ? [x, []] : [b[0], [...b.slice(1), x]];
  var bufferHalve = (b) => {
    const odd = b.length % 2 === 1 ? b[0] : null;
    const start = odd !== null ? 1 : 0;
    const pairs = [];
    for (let i = start; i < b.length; i += 2) pairs.push([b[i], b[i + 1]]);
    return [odd, pairs];
  };

  // src/deque.ts
  var HOLE = { tag: "hole" };
  var hole = () => HOLE;
  var pnode = (pre, inner, suf) => {
    bump();
    return { tag: "pnode", pre, inner, suf };
  };
  var end = (b) => {
    bump();
    return { tag: "end", b };
  };
  var cons = (color, p, c) => {
    bump();
    return { tag: "cons", color, p, c };
  };
  var consG = (p, c) => cons("green", p, c);
  var bufSeqE = (b) => b.flatMap(toList);
  var packetSeq = (p, inner) => p.tag === "hole" ? inner : bufSeqE(p.pre).concat(packetSeq(p.inner, inner), bufSeqE(p.suf));
  var chainSeq = (c) => c.tag === "end" ? bufSeqE(c.b) : packetSeq(c.p, chainSeq(c.c));
  var pairOne = (p) => level(p[0]) === level(p[1]) ? pair(p[0], p[1]) : null;
  var pairEachBuf = (b) => {
    const out = [];
    for (const p of b) {
      const x = pairOne(p);
      if (x === null) return null;
      out.push(x);
    }
    return out;
  };
  var greenPrefixConcat = (b1, b2) => {
    const d = prefixDecompose(b1);
    switch (d.tag) {
      case "under": {
        const gp = greenPop(b2);
        if (gp === null) return null;
        const up = unpair(gp[0]);
        return up === null ? null : [prefix23(d.x, up), gp[1]];
      }
      case "ok":
        return [d.b, b2];
      case "over": {
        if (level(d.c) !== level(d.d)) return null;
        const b2p = greenPush(pair(d.c, d.d), b2);
        return b2p === null ? null : [d.b, b2p];
      }
    }
  };
  var greenSuffixConcat = (b1, b2) => {
    const d = suffixDecompose(b2);
    switch (d.tag) {
      case "under": {
        const ge = greenEject(b1);
        if (ge === null) return null;
        const up = unpair(ge[1]);
        return up === null ? null : [ge[0], suffix23(up, d.x)];
      }
      case "ok":
        return [b1, d.b];
      case "over": {
        if (level(d.a) !== level(d.b2)) return null;
        const b1p = greenInject(b1, pair(d.a, d.b2));
        return b1p === null ? null : [b1p, d.b];
      }
    }
  };
  var prefixConcat = (b1, b2) => {
    const d = prefixDecompose(b1);
    switch (d.tag) {
      case "under": {
        const yp = yellowPop(b2);
        if (yp === null) return null;
        const up = unpair(yp[0]);
        return up === null ? null : [prefix23(d.x, up), yp[1]];
      }
      case "ok":
        return [d.b, b2];
      case "over": {
        if (level(d.c) !== level(d.d)) return null;
        const b2p = yellowPush(pair(d.c, d.d), b2);
        return b2p === null ? null : [d.b, b2p];
      }
    }
  };
  var suffixConcat = (b1, b2) => {
    const d = suffixDecompose(b2);
    switch (d.tag) {
      case "under": {
        const ye = yellowEject(b1);
        if (ye === null) return null;
        const up = unpair(ye[1]);
        return up === null ? null : [ye[0], suffix23(up, d.x)];
      }
      case "ok":
        return [b1, d.b];
      case "over": {
        if (level(d.a) !== level(d.b2)) return null;
        const b1p = yellowInject(b1, pair(d.a, d.b2));
        return b1p === null ? null : [b1p, d.b];
      }
    }
  };
  var bufferPushChain = (x, b) => {
    if (b.length < 5) return end([x, ...b]);
    return consG(pnode([x, b[0], b[1]], hole(), [b[2], b[3], b[4]]), end([]));
  };
  var bufferInjectChain = (b, x) => {
    if (b.length < 5) return end([...b, x]);
    return consG(pnode([b[0], b[1], b[2]], hole(), [b[3], b[4], x]), end([]));
  };
  var mkEndingFromOptions = (p1, mid, s1) => {
    const xs = [];
    if (p1 !== null) xs.push(p1);
    if (mid !== null) xs.push(mid[0], mid[1]);
    if (s1 !== null) xs.push(s1);
    return end(xs);
  };
  var makeSmall = (b1, b2, b3) => {
    const pd = prefixDecompose(b1);
    const sd = suffixDecompose(b3);
    if (pd.tag === "under") {
      if (sd.tag === "under") {
        const us = bufferUnsandwich(b2);
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
        return consG(pnode(prefix23(pd.x, pab), hole(), suffix23(pcd, sd.x)), end(us.mid));
      } else if (sd.tag === "ok") {
        const pop2 = popNaive(b2);
        if (pop2 !== null) {
          const pcd = unpair(pop2[0]);
          return pcd === null ? null : consG(pnode(prefix23(pd.x, pcd), hole(), sd.b), end(pop2[1]));
        }
        if (pd.x !== null) {
          const s = pushNaive(pd.x, sd.b);
          return s === null ? null : end(s);
        }
        return end(sd.b);
      } else {
        if (level(sd.a) !== level(sd.b2)) return null;
        const [cdPaired, center] = suffixRot(b2, pair(sd.a, sd.b2));
        const pcd = unpair(cdPaired);
        return pcd === null ? null : consG(pnode(prefix23(pd.x, pcd), hole(), sd.b), end(center));
      }
    } else if (pd.tag === "ok") {
      if (sd.tag === "under") {
        const ej = ejectNaive(b2);
        if (ej !== null) {
          const pab = unpair(ej[1]);
          return pab === null ? null : consG(pnode(pd.b, hole(), suffix23(pab, sd.x)), end(ej[0]));
        }
        if (sd.x !== null) {
          const p = injectNaive(pd.b, sd.x);
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
        const [center, abPaired] = prefixRot(pair(pd.c, pd.d), b2);
        const pab = unpair(abPaired);
        return pab === null ? null : consG(pnode(pd.b, hole(), suffix23(pab, sd.x)), end(center));
      } else if (sd.tag === "ok") {
        return consG(pnode(pd.b, hole(), sd.b), bufferPushChain(pair(pd.c, pd.d), b2));
      } else {
        if (level(sd.a) !== level(sd.b2)) return null;
        const cdPaired = pair(pd.c, pd.d);
        const abPaired = pair(sd.a, sd.b2);
        const [midOpt, restPairs] = bufferHalve(b2);
        const rest = pairEachBuf(restPairs);
        if (rest === null) return null;
        const p2 = suffix12(cdPaired, midOpt);
        return consG(pnode(pd.b, pnode(p2, hole(), [abPaired]), sd.b), end(rest));
      }
    }
  };
  var greenOfRedK = (c) => {
    if (c.tag === "end" || c.color !== "red") return null;
    const p = c.p;
    if (p.tag === "hole") return null;
    const { pre: pre1, inner: p0, suf: suf1 } = p;
    if (p0.tag === "hole") {
      const c1 = c.c;
      if (c1.tag === "end") return makeSmall(pre1, c1.b, suf1);
      const p1 = c1.p;
      if (p1.tag === "hole") return null;
      const { pre: pre22, inner: child2, suf: suf22 } = p1;
      const gp = greenPrefixConcat(pre1, pre22);
      if (gp === null) return null;
      const gs = greenSuffixConcat(suf22, suf1);
      if (gs === null) return null;
      return consG(pnode(gp[0], pnode(gp[1], child2, gs[0]), gs[1]), c1.c);
    }
    const { pre: pre2, inner: child, suf: suf2 } = p0;
    const pc = prefixConcat(pre1, pre2);
    if (pc === null) return null;
    const sc = suffixConcat(suf2, suf1);
    if (sc === null) return null;
    return consG(pnode(pc[0], hole(), sc[1]), cons("red", pnode(pc[1], child, sc[0]), c.c));
  };
  var ensureGreenK = (c) => c.tag === "cons" && c.color === "red" ? greenOfRedK(c) : c;
  var makeYellowK = (pre, i, suf, c) => {
    const cp = ensureGreenK(c);
    return cp === null ? null : cons("yellow", pnode(pre, i, suf), cp);
  };
  var makeRedK = (pre, i, suf, c) => greenOfRedK(cons("red", pnode(pre, i, suf), c));
  var pushKt = (x, c) => {
    if (c.tag === "end") {
      const b = pushNaive(x, c.b);
      if (b !== null) return end(b);
      if (c.b.length !== 5) return null;
      const o = c.b;
      return consG(pnode([x, o[0], o[1]], hole(), [o[2], o[3], o[4]]), end([]));
    }
    const p = c.p;
    if (p.tag === "hole") return null;
    switch (c.color) {
      case "green": {
        const pre = greenPush(x, p.pre);
        return pre === null ? null : makeYellowK(pre, p.inner, p.suf, c.c);
      }
      case "yellow": {
        const pre = yellowPush(x, p.pre);
        return pre === null ? null : makeRedK(pre, p.inner, p.suf, c.c);
      }
      case "red":
        return null;
    }
  };
  var injectKt = (c, x) => {
    if (c.tag === "end") {
      const b = injectNaive(c.b, x);
      if (b !== null) return end(b);
      if (c.b.length !== 5) return null;
      const o = c.b;
      return consG(pnode([o[0], o[1], o[2]], hole(), [o[3], o[4], x]), end([]));
    }
    const p = c.p;
    if (p.tag === "hole") return null;
    switch (c.color) {
      case "green": {
        const suf = greenInject(p.suf, x);
        return suf === null ? null : makeYellowK(p.pre, p.inner, suf, c.c);
      }
      case "yellow": {
        const suf = yellowInject(p.suf, x);
        return suf === null ? null : makeRedK(p.pre, p.inner, suf, c.c);
      }
      case "red":
        return null;
    }
  };
  var popKt = (c) => {
    if (c.tag === "end") {
      const r = popNaive(c.b);
      return r === null ? null : [r[0], end(r[1])];
    }
    const p = c.p;
    if (p.tag === "hole") return null;
    switch (c.color) {
      case "green": {
        const r = greenPop(p.pre);
        if (r === null) return null;
        const c2 = makeYellowK(r[1], p.inner, p.suf, c.c);
        return c2 === null ? null : [r[0], c2];
      }
      case "yellow": {
        const r = yellowPop(p.pre);
        if (r === null) return null;
        const c2 = makeRedK(r[1], p.inner, p.suf, c.c);
        return c2 === null ? null : [r[0], c2];
      }
      case "red":
        return null;
    }
  };
  var ejectKt = (c) => {
    if (c.tag === "end") {
      const r = ejectNaive(c.b);
      return r === null ? null : [end(r[0]), r[1]];
    }
    const p = c.p;
    if (p.tag === "hole") return null;
    switch (c.color) {
      case "green": {
        const r = greenEject(p.suf);
        if (r === null) return null;
        const c2 = makeYellowK(p.pre, p.inner, r[0], c.c);
        return c2 === null ? null : [c2, r[1]];
      }
      case "yellow": {
        const r = yellowEject(p.suf);
        if (r === null) return null;
        const c2 = makeRedK(p.pre, p.inner, r[0], c.c);
        return c2 === null ? null : [c2, r[1]];
      }
      case "red":
        return null;
    }
  };
  var emptyChain = () => end([]);
  var unwrap = (e) => {
    if (e.tag === "base") return e.v;
    const xs = toList(e);
    if (xs.length !== 1) throw new Error("ktdeque: popped element is not at level 0");
    return xs[0];
  };
  var must = (x, op) => {
    if (x === null) throw new Error(`ktdeque: ${op} returned null on a regular deque (invariant violation)`);
    return x;
  };
  var push = (x, c) => must(pushKt(base(x), c), "push");
  var inject = (c, x) => must(injectKt(c, base(x)), "inject");
  var pop = (c) => {
    const r = popKt(c);
    return r === null ? null : [unwrap(r[0]), r[1]];
  };
  var eject = (c) => {
    const r = ejectKt(c);
    return r === null ? null : [r[0], unwrap(r[1])];
  };
  var toList2 = (c) => chainSeq(c);

  // src/cadeque.ts
  var sground = (v) => ({ tag: "ground", v });
  var ssmall = (b) => (bump(), { tag: "small", b });
  var sbig = (pre, child, suf) => (bump(), { tag: "big", pre, child, suf });
  var node = (k, pre, suf) => (bump(), { tag: "node", k, pre, suf });
  var BHOLE = { tag: "bhole" };
  var bhole = () => BHOLE;
  var bsingle = (n, b) => (bump(), { tag: "bsingle", n, b });
  var bpairY = (n, b, rc) => (bump(), { tag: "bpairY", n, b, rc });
  var bpairO = (n, lc, b) => (bump(), { tag: "bpairO", n, lc, b });
  var pkt = (body, n) => (bump(), { tag: "pkt", body, n });
  var CEMPTY = { tag: "cempty" };
  var cempty = () => CEMPTY;
  var csingle = (p, rest) => (bump(), { tag: "csingle", p, rest });
  var cpair = (l, r) => (bump(), { tag: "cpair", l, r });
  var app = (a, b) => a.concat(b);
  var cadEmpty = () => cempty();
  var storedSeq = (s) => {
    if (s.tag === "ground") return [s.v];
    if (s.tag === "small") return s.b.flatMap(storedSeq);
    return s.pre.flatMap(storedSeq).concat(cchainSeq(s.child), s.suf.flatMap(storedSeq));
  };
  var cnodeSeq = (n, mid) => n.pre.flatMap(storedSeq).concat(mid, n.suf.flatMap(storedSeq));
  var cbodySeq = (b, inner) => {
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
  var cpacketSeq = (p, inner) => cbodySeq(p.body, cnodeSeq(p.n, inner));
  var cchainSeq = (c) => {
    switch (c.tag) {
      case "cempty":
        return [];
      case "csingle":
        return cpacketSeq(c.p, cchainSeq(c.rest));
      case "cpair":
        return cchainSeq(c.l).concat(cchainSeq(c.r));
    }
  };
  var cadToList = (c) => cchainSeq(c);
  var nodeColor = (hasChild, n) => {
    if (!hasChild) return "CG";
    const m = n.k === "only" ? Math.min(n.pre.length, n.suf.length) : n.k === "left" ? n.pre.length : n.suf.length;
    return m >= 8 ? "CG" : m === 7 ? "CY" : m === 6 ? "CO" : "CR";
  };
  var chainHasNode = (c) => c.tag !== "cempty";
  var nodePush = (s, n) => n.pre.length === 0 ? node(n.k, [], [s, ...n.suf]) : node(n.k, [s, ...n.pre], n.suf);
  var nodeInject = (n, s) => n.suf.length === 0 ? node(n.k, app(n.pre, [s]), []) : node(n.k, n.pre, app(n.suf, [s]));
  var bufPop2 = (b) => b.length >= 2 ? [[b[0], b[1]], b.slice(2)] : null;
  var bufEject2 = (b) => b.length >= 2 ? [[b.slice(0, -2), b[b.length - 2]], b[b.length - 1]] : null;
  var bufEject3 = (b) => b.length >= 3 ? [[[b.slice(0, -3), b[b.length - 3]], b[b.length - 2]], b[b.length - 1]] : null;
  var rootAndChild = (p, rest) => {
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
  var treeOf = (n, child) => {
    const col = nodeColor(chainHasNode(child), n);
    if (col === "CY") {
      if (child.tag === "cempty") return csingle(pkt(bhole(), n), child);
      if (child.tag === "csingle") return csingle(pkt(bsingle(n, child.p.body), child.p.n), child.rest);
      if (child.l.tag === "csingle")
        return csingle(pkt(bpairY(n, child.l.p.body, child.r), child.l.p.n), child.l.rest);
      return csingle(pkt(bhole(), n), child);
    }
    if (col === "CO") {
      if (child.tag === "cempty") return csingle(pkt(bhole(), n), child);
      if (child.tag === "csingle") return csingle(pkt(bsingle(n, child.p.body), child.p.n), child.rest);
      if (child.r.tag === "csingle")
        return csingle(pkt(bpairO(n, child.l, child.r.p.body), child.r.p.n), child.r.rest);
      return csingle(pkt(bhole(), n), child);
    }
    return csingle(pkt(bhole(), n), child);
  };
  var pktUpdate = (upd, p, rest) => {
    const [n, child] = rootAndChild(p, rest);
    return treeOf(upd(n), child);
  };
  var pushChain = (s, c) => {
    switch (c.tag) {
      case "cempty":
        return csingle(pkt(bhole(), node("only", [s], [])), cempty());
      case "csingle":
        return pktUpdate((n) => nodePush(s, n), c.p, c.rest);
      case "cpair":
        return cpair(pushChain(s, c.l), c.r);
    }
  };
  var injectChain = (c, s) => {
    switch (c.tag) {
      case "cempty":
        return csingle(pkt(bhole(), node("only", [], [s])), cempty());
      case "csingle":
        return pktUpdate((n) => nodeInject(n, s), c.p, c.rest);
      case "cpair":
        return cpair(c.l, injectChain(c.r, s));
    }
  };
  var cadPush = (x, d) => pushChain(sground(x), d);
  var cadInject = (d, x) => injectChain(d, sground(x));
  var degenerateBuf = (c) => {
    if (c.tag !== "csingle" || c.p.body.tag !== "bhole" || c.rest.tag !== "cempty") return null;
    const n = c.p.n;
    if (n.k !== "only") return null;
    if (n.pre.length === 0) return n.suf;
    if (n.suf.length === 0) return n.pre;
    return null;
  };
  var makeLeftOnly = (p1, d1, s1) => {
    if (d1.tag === "cempty") {
      if (s1.length <= 8) {
        const e3 = bufEject2(s1);
        if (e3 === null) return null;
        const [[s1p2, y3], z3] = e3;
        return treeOf(node("left", app(p1, s1p2), [y3, z3]), cempty());
      }
      if (s1.length < 3) return null;
      const [a, b, c] = [s1[0], s1[1], s1[2]];
      const srest = s1.slice(3);
      const e2 = bufEject2(srest);
      if (e2 === null) return null;
      const [[smid, y2], z2] = e2;
      return treeOf(node("left", app(p1, [a, b, c]), [y2, z2]), pushChain(ssmall(smid), cempty()));
    }
    const e = bufEject2(s1);
    if (e === null) return null;
    const [[s1p, y], z] = e;
    return treeOf(node("left", p1, [y, z]), injectChain(d1, ssmall(s1p)));
  };
  var makeLeft = (c) => {
    if (c.tag === "cempty") return null;
    if (c.tag === "csingle") {
      const [n, d12] = rootAndChild(c.p, c.rest);
      return makeLeftOnly(n.pre, d12, n.suf);
    }
    if (c.l.tag !== "csingle" || c.r.tag !== "csingle") return null;
    const [n1, d1] = rootAndChild(c.l.p, c.l.rest);
    const [n2, d2] = rootAndChild(c.r.p, c.r.rest);
    if (d1.tag === "cempty") return makeLeftOnly(app(n1.pre, app(n1.suf, n2.pre)), d2, n2.suf);
    const e = bufEject2(n2.suf);
    if (e === null) return null;
    const [[s2p, y], z] = e;
    return treeOf(node("left", n1.pre, [y, z]), injectChain(d1, sbig(app(n1.suf, n2.pre), d2, s2p)));
  };
  var makeRightOnly = (p1, d1, s1) => {
    if (d1.tag === "cempty") {
      if (p1.length <= 8) {
        const pp3 = bufPop2(p1);
        if (pp3 === null) return null;
        const [[x3, y3], p1p3] = pp3;
        return treeOf(node("right", [x3, y3], app(p1p3, s1)), cempty());
      }
      const pp2 = bufPop2(p1);
      if (pp2 === null) return null;
      const [[x2, y2], p1p2] = pp2;
      const e = bufEject3(p1p2);
      if (e === null) return null;
      const [[[pmid, a], b], c] = e;
      return treeOf(node("right", [x2, y2], app([a, b, c], s1)), pushChain(ssmall(pmid), cempty()));
    }
    const pp = bufPop2(p1);
    if (pp === null) return null;
    const [[x, y], p1p] = pp;
    return treeOf(node("right", [x, y], s1), pushChain(ssmall(p1p), d1));
  };
  var makeRight = (c) => {
    if (c.tag === "cempty") return null;
    if (c.tag === "csingle") {
      const [n, d12] = rootAndChild(c.p, c.rest);
      return makeRightOnly(n.pre, d12, n.suf);
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
  var concatSmallLeft = (p3, e) => {
    if (p3.length < 8) return p3.reduceRight((acc, x) => pushChain(x, acc), e);
    if (e.tag === "cempty") return null;
    if (e.tag === "csingle") {
      const [n22, d22] = rootAndChild(e.p, e.rest);
      if (d22.tag === "cempty") {
        const ej = bufEject2(n22.pre);
        if (ej === null) return null;
        const [[p2p, y], z] = ej;
        return treeOf(node("only", p3, [y, z, ...n22.suf]), pushChain(ssmall(p2p), cempty()));
      }
      return treeOf(node("only", p3, n22.suf), pushChain(ssmall(n22.pre), d22));
    }
    if (e.l.tag !== "csingle") return null;
    const [n2, d2] = rootAndChild(e.l.p, e.l.rest);
    return cpair(treeOf(node("left", p3, n2.suf), pushChain(ssmall(n2.pre), d2)), e.r);
  };
  var concatSmallRight = (d, s3) => {
    if (s3.length < 8) return s3.reduce((acc, x) => injectChain(acc, x), d);
    if (d.tag === "cempty") return null;
    if (d.tag === "csingle") {
      const [n12, d12] = rootAndChild(d.p, d.rest);
      if (d12.tag === "cempty") {
        const pp = bufPop2(n12.suf);
        if (pp === null) return null;
        const [[x, y], s1p] = pp;
        return treeOf(node("only", app(n12.pre, [x, y]), s3), pushChain(ssmall(s1p), cempty()));
      }
      return treeOf(node("only", n12.pre, s3), injectChain(d12, ssmall(n12.suf)));
    }
    if (d.r.tag !== "csingle") return null;
    const [n1, d1] = rootAndChild(d.r.p, d.r.rest);
    return cpair(d.l, treeOf(node("right", n1.pre, s3), injectChain(d1, ssmall(n1.suf))));
  };
  var cadConcat = (d, e) => {
    if (d.tag === "cempty") return e;
    if (e.tag === "cempty") return d;
    const p = degenerateBuf(d);
    if (p !== null) {
      const s2 = degenerateBuf(e);
      if (s2 !== null) {
        if (p.length < 8 || s2.length < 8) return csingle(pkt(bhole(), node("only", app(p, s2), [])), cempty());
        return csingle(pkt(bhole(), node("only", p, s2)), cempty());
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
  var nodePop = (n) => {
    if (n.pre.length === 0) {
      if (n.suf.length === 0) return null;
      return [n.suf[0], node(n.k, [], n.suf.slice(1))];
    }
    return [n.pre[0], node(n.k, n.pre.slice(1), n.suf)];
  };
  var nodeEject = (n) => {
    if (n.suf.length === 0) {
      if (n.pre.length === 0) return null;
      return [node(n.k, n.pre.slice(0, -1), []), n.pre[n.pre.length - 1]];
    }
    return [node(n.k, n.pre, n.suf.slice(0, -1)), n.suf[n.suf.length - 1]];
  };
  var rebuildChildless = (n) => {
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
  var popRaw = (c) => {
    if (c.tag === "cempty") return null;
    if (c.tag === "csingle") {
      const [n, child] = rootAndChild(c.p, c.rest);
      const np = nodePop(n);
      if (np === null) return null;
      const [x2, np2] = np;
      return [x2, child.tag === "cempty" ? rebuildChildless(np2) : treeOf(np2, child)];
    }
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
  var ejectRaw = (c) => {
    if (c.tag === "cempty") return null;
    if (c.tag === "csingle") {
      const [n, child] = rootAndChild(c.p, c.rest);
      const ne = nodeEject(n);
      if (ne === null) return null;
      const [ne2, x2] = ne;
      return [child.tag === "cempty" ? rebuildChildless(ne2) : treeOf(ne2, child), x2];
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
  var repairFront = (k, body, p1, s1, rest) => {
    const pr = popRaw(rest);
    if (pr === null) return null;
    const [s, d1p] = pr;
    if (s.tag === "ground") return null;
    if (s.tag === "small") return csingle(pkt(body, node(k, app(p1, s.b), s1)), d1p);
    const d3 = cadConcat(s.child, pushChain(ssmall(s.suf), d1p));
    return d3 === null ? null : csingle(pkt(body, node(k, app(p1, s.pre), s1)), d3);
  };
  var repairBack = (k, body, p1, s1, rest) => {
    const er = ejectRaw(rest);
    if (er === null) return null;
    const [d1p, s] = er;
    if (s.tag === "ground") return null;
    if (s.tag === "small") return csingle(pkt(body, node(k, p1, app(s.b, s1))), d1p);
    const d3 = cadConcat(injectChain(d1p, ssmall(s.pre)), s.child);
    return d3 === null ? null : csingle(pkt(body, node(k, p1, app(s.suf, s1))), d3);
  };
  var drainBoth = (c) => {
    if (c.tag === "cempty") return null;
    if (c.tag === "csingle") {
      const [n, dd] = rootAndChild(c.p, c.rest);
      const np = nodePop(n);
      if (np === null) return null;
      const [cellF2, n1] = np;
      const ne = nodeEject(n1);
      if (ne !== null) {
        const [n2, cellB2] = ne;
        return [[cellF2, cellB2], dd.tag === "cempty" ? rebuildChildless(n2) : treeOf(n2, dd)];
      }
      return dd.tag === "cempty" ? [[cellF2, null], cempty()] : null;
    }
    const lp = popRaw(c.l);
    if (lp === null) return null;
    const [cellF, lprime] = lp;
    const re = ejectRaw(c.r);
    if (re === null) return null;
    const [rprime, cellB] = re;
    const fallback = [[cellF, cellB], cpair(lprime, rprime)];
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
    if (rprime.tag === "csingle" && rprime.p.body.tag === "bhole" && rprime.rest.tag === "cempty") {
      const rn = rprime.p.n;
      if (rn.suf.length < 5) {
        const [n2, d2] = rootAndChild(lprime.p, lprime.rest);
        return [[cellF, cellB], treeOf(node("only", n2.pre, app(n2.suf, app(rn.pre, rn.suf))), d2)];
      }
    }
    return fallback;
  };
  var repairBoth = (body, p1, s1, rest) => {
    const db = drainBoth(rest);
    if (db === null) return null;
    const [[cellF, o], mid] = db;
    if (o !== null) {
      const cellB = o;
      let front;
      if (cellF.tag === "ground") front = null;
      else if (cellF.tag === "small") front = [cellF.b, mid];
      else {
        const d42 = cadConcat(cellF.child, pushChain(ssmall(cellF.suf), mid));
        front = d42 === null ? null : [cellF.pre, d42];
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
  var repairPacket = (p, rest) => {
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
  var repairPopSide = (c) => {
    if (c.tag === "cempty") return cempty();
    if (c.tag === "csingle") return repairPacket(c.p, c.rest);
    if (c.l.tag !== "csingle") return null;
    const lp = repairPacket(c.l.p, c.l.rest);
    return lp === null ? null : cpair(lp, c.r);
  };
  var repairEjectSide = (c) => {
    if (c.tag === "cempty") return cempty();
    if (c.tag === "csingle") return repairPacket(c.p, c.rest);
    if (c.r.tag !== "csingle") return null;
    const rp = repairPacket(c.r.p, c.r.rest);
    return rp === null ? null : cpair(c.l, rp);
  };
  var cadPopRaw = (d) => {
    const pr = popRaw(d);
    if (pr === null) return null;
    const [s, dp] = pr;
    if (s.tag !== "ground") return null;
    const dpp = repairPopSide(dp);
    return dpp === null ? null : [s.v, dpp];
  };
  var cadEjectRaw = (d) => {
    const er = ejectRaw(d);
    if (er === null) return null;
    const [dp, s] = er;
    if (s.tag !== "ground") return null;
    const dpp = repairEjectSide(dp);
    return dpp === null ? null : [dpp, s.v];
  };
  var must2 = (x, op) => {
    if (x === null) throw new Error(`ktcadeque: ${op} returned null on a regular cadeque (invariant violation)`);
    return x;
  };
  var cadConcatChecked = (d, e) => must2(cadConcat(d, e), "concat");
  var cadPop = (d) => cadPopRaw(d);
  var cadEject = (d) => cadEjectRaw(d);

  // src/snapshot.ts
  function snapshot4(c) {
    const cells = [];
    let depth = 0;
    let cur = c;
    for (; ; ) {
      if (cur.tag === "end") {
        cells.push({ id: `L${depth}`, depth, pre: cur.b.length, suf: 0, color: bufColor(cur.b), anchor: true, ending: true });
        return { cells };
      }
      let p = cur.p;
      let first = true;
      while (p.tag === "pnode") {
        cells.push({
          id: `L${depth}`,
          depth,
          pre: p.pre.length,
          suf: p.suf.length,
          color: colorMeet(bufColor(p.pre), bufColor(p.suf)),
          anchor: first,
          ending: false
        });
        depth++;
        first = false;
        p = p.inner;
      }
      cur = cur.c;
    }
  }
  var gyorToColor = (g) => g === "CG" ? "green" : g === "CY" ? "yellow" : g === "CO" ? "orange" : "red";
  function snapshot6(root) {
    const nodes = [];
    const edges = [];
    let counter = 0;
    const fresh = () => `T${counter++}`;
    const walk = (c, parent, kind, depth) => {
      if (c.tag === "cempty") return;
      if (c.tag === "cpair") {
        if (parent === null) {
          const id2 = fresh();
          nodes.push({ id: id2, role: "pair", pre: 0, suf: 0, color: "green", depth });
          walk(c.l, id2, "left", depth + 1);
          walk(c.r, id2, "right", depth + 1);
        } else {
          walk(c.l, parent, "left", depth);
          walk(c.r, parent, "right", depth);
        }
        return;
      }
      const p = c.p;
      const [n, child] = rootAndChild(p, c.rest);
      const id = fresh();
      nodes.push({
        id,
        role: n.k,
        pre: n.pre.length,
        suf: n.suf.length,
        color: gyorToColor(nodeColor(chainHasNode(child), n)),
        depth
      });
      if (parent !== null) edges.push({ from: parent, to: id, kind });
      walk(child, id, "child", depth + 1);
    };
    walk(root, null, "child", 0);
    return { nodes, edges };
  }

  // src/browser.ts
  var empty4 = emptyChain;
  var push4 = push;
  var inject4 = inject;
  var pop4 = pop;
  var eject4 = eject;
  var toList4 = toList2;
  var empty6 = cadEmpty;
  var push6 = cadPush;
  var inject6 = cadInject;
  var pop6 = cadPop;
  var eject6 = cadEject;
  var concat6 = cadConcatChecked;
  var toList6 = cadToList;
  return __toCommonJS(browser_exports);
})();
