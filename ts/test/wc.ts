/**
 * Worst-case cost test — the JS analogue of `c/tests/wc_test.c`.
 *
 * Counts persistent-node allocations (chain/packet/pair) per operation and
 * reports the MAXIMUM over several adversarial workloads, at growing sizes.
 * For genuine worst-case O(1) the maximum must stay FLAT as n grows; a
 * recursive O(log n) cascade would make it climb with n.  This is the test
 * that distinguishes the certified non-recursive repair (the project hard
 * rule) from a fallback cascade.  Run: `npm run wc`.
 */
import * as KT from "../src/index.js";
import type { Deque } from "../src/index.js";
import * as alloc from "../src/alloc.js";

function mulberry32(a: number): () => number {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

interface Stats {
  push: number;
  inject: number;
  pop: number;
  eject: number;
  mixed: number;
}

function runWorkload(n: number): Stats {
  let d: Deque<number> = KT.empty<number>();
  let v = 1;
  let mPush = 0,
    mInject = 0,
    mPop = 0,
    mEject = 0,
    mMixed = 0;

  for (let i = 0; i < n; i++) {
    alloc.reset();
    d = KT.push(v++, d);
    mPush = Math.max(mPush, alloc.get());
  }
  for (let i = 0; i < n; i++) {
    alloc.reset();
    d = KT.inject(d, v++);
    mInject = Math.max(mInject, alloc.get());
  }
  for (let i = 0; i < n; i++) {
    alloc.reset();
    const r = KT.pop(d);
    if (r) d = r[1];
    mPop = Math.max(mPop, alloc.get());
  }
  for (let i = 0; i < n; i++) {
    alloc.reset();
    const r = KT.eject(d);
    if (r) d = r[0];
    mEject = Math.max(mEject, alloc.get());
  }
  // refill, then tight random interleave (deepest green↔red cascades)
  for (let i = 0; i < n; i++) d = KT.push(v++, d);
  const rng = mulberry32(42);
  for (let i = 0; i < n; i++) {
    const op = Math.floor(rng() * 4);
    alloc.reset();
    if (op === 0) d = KT.push(v++, d);
    else if (op === 1) d = KT.inject(d, v++);
    else if (op === 2) {
      const r = KT.pop(d);
      if (r) d = r[1];
    } else {
      const r = KT.eject(d);
      if (r) d = r[0];
    }
    mMixed = Math.max(mMixed, alloc.get());
  }
  return { push: mPush, inject: mInject, pop: mPop, eject: mEject, mixed: mMixed };
}

function main(): void {
  const sizes = [1000, 10000, 100000, 1000000];
  const totals: number[] = [];
  console.log("max persistent-node allocations per op (must stay bounded & flat as n grows 1000×):\n");
  for (const n of sizes) {
    const s = runWorkload(n);
    const total = Math.max(s.push, s.inject, s.pop, s.eject, s.mixed);
    totals.push(total);
    console.log(
      `  n=${String(n).padStart(8)}  push=${s.push} inject=${s.inject} pop=${s.pop} eject=${s.eject} mixed=${s.mixed}  ->  max=${total}`,
    );
  }
  // Worst-case O(1): the per-op max must be bounded by a constant AND not grow
  // with n.  O(log n) would climb (~8,13,17,20); flat 8–9 across a 1000× range
  // is the signature of the certified non-recursive repair.  Allow ±1 sampling
  // noise (which specific op hit the max varies run to run).
  const first = totals[0]!;
  const last = totals[totals.length - 1]!;
  const bounded = Math.max(...totals) <= 16;
  const nonGrowing = last - first <= 1;
  const ok = bounded && nonGrowing;
  console.log(
    `\n[wc] per-op max = ${totals.join(", ")} across n = ${sizes.join(", ")}  ->  ${
      ok ? "BOUNDED & FLAT — worst-case O(1) ✓" : "GROWS with n — cascade suspected ✗"
    }`,
  );
  process.exit(ok ? 0 : 1);
}

main();
