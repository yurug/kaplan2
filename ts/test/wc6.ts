/**
 * §6 worst-case cost test.  Counts persistent-node allocations per operation —
 * the headline being that `concat` of two size-n deques allocates a CONSTANT
 * number of nodes (rearranges O(1) cells at the root, shares both operands)
 * regardless of n.  push/pop are likewise flat.  Run: `npm run wc6`.
 *
 * (Model-layer caveat, per ocaml/extracted/dune: buffers are lists and colours
 * recompute length, so extracted *wall-clock* is O(root buffer size); the
 * mechanized constant bound counts buffer primitives.  Here we count structural
 * node allocations, which is the O(1)-shape signal.)
 */
import { cadEmpty, cadPush, cadConcatChecked, cadPop, type Cchain } from "../src/cadeque.js";
import * as alloc from "../src/alloc.js";

function build(n: number, start: number): Cchain<number> {
  let d: Cchain<number> = cadEmpty<number>();
  for (let i = 0; i < n; i++) d = cadPush(start + i, d);
  return d;
}

function main(): void {
  // The §6 model uses list buffers (extracted wall-clock O(root buffer size)),
  // so we cap n where it stays fast; the allocation maxima are already flat
  // across this 16× range, which is the O(1)-shape signal.
  const sizes = [1000, 4000, 16000];
  const concatAllocs: number[] = [];
  const pushMaxes: number[] = [];
  const popMaxes: number[] = [];
  console.log("§6 per-op persistent-node allocations (must stay bounded & flat as n grows):\n");
  for (const n of sizes) {
    // push max while building
    let d: Cchain<number> = cadEmpty<number>();
    let pushMax = 0;
    for (let i = 0; i < n; i++) {
      alloc.reset();
      d = cadPush(i + 1, d);
      pushMax = Math.max(pushMax, alloc.get());
    }
    // concat of two size-n deques
    const a = build(n, 0);
    const b = build(n, n);
    alloc.reset();
    cadConcatChecked(a, b);
    const cAlloc = alloc.get();
    // pop max while draining d
    let popMax = 0;
    for (let i = 0; i < n; i++) {
      alloc.reset();
      const r = cadPop(d);
      if (r === null) break;
      d = r[1];
      popMax = Math.max(popMax, alloc.get());
    }
    concatAllocs.push(cAlloc);
    pushMaxes.push(pushMax);
    popMaxes.push(popMax);
    console.log(`  n=${String(n).padStart(7)}  push_max=${pushMax}  pop_max=${popMax}  concat=${cAlloc}`);
  }
  const flat = (a: number[]) => a[a.length - 1]! - a[0]! <= 1;
  const ok =
    flat(concatAllocs) &&
    flat(pushMaxes) &&
    flat(popMaxes) &&
    Math.max(...concatAllocs, ...pushMaxes, ...popMaxes) <= 64;
  console.log(
    `\n[wc6] concat allocs = ${concatAllocs.join(", ")}  (push ${pushMaxes.join(",")}, pop ${popMaxes.join(",")}) ` +
      `across n = ${sizes.join(", ")}  ->  ${ok ? "BOUNDED & FLAT — worst-case O(1) incl. concat ✓" : "GROWS with n ✗"}`,
  );
  process.exit(ok ? 0 : 1);
}

main();
