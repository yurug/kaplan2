/**
 * Differential fuzzer — the JS analogue of `c/tests/fuzz.c`.
 *
 * For each deterministic seed: run a random sequence of push/inject/pop/eject
 * against both the port and the naive `Oracle`, and after EVERY op assert
 *   (1) pop/eject return values agree with the oracle,
 *   (2) the deque stays regular (`checkRegular`),
 *   (3) (for short runs) the full flattened sequence matches the oracle,
 * with a final full-sequence comparison.  A second pass stresses persistence:
 * forked snapshots must keep reading their own sequence after the live branch
 * is mutated further.  Run: `npm run fuzz [nSeeds]`.
 */
import * as KT from "../src/index.js";
import type { Deque } from "../src/index.js";
import { Oracle } from "./oracle.js";

// deterministic PRNG (mulberry32) so any failure reproduces from its seed
function mulberry32(a: number): () => number {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const arrEq = (a: readonly number[], b: readonly number[]): boolean =>
  a.length === b.length && a.every((x, i) => x === b[i]);

function fuzzSeed(seed: number, n: number): string | null {
  const rng = mulberry32(seed);
  let d: Deque<number> = KT.empty<number>();
  const ref = new Oracle<number>();
  let next = 1;
  const fullCheck = n <= 200;

  for (let i = 0; i < n; i++) {
    const op = Math.floor(rng() * 100);
    if (op < 30) {
      d = KT.push(next, d);
      ref.push(next++);
    } else if (op < 60) {
      d = KT.inject(d, next);
      ref.inject(next++);
    } else if (op < 80) {
      const r = KT.pop(d);
      if (ref.length > 0) {
        if (r === null) return `i=${i}: pop returned null but oracle non-empty`;
        const rv = ref.pop();
        if (r[0] !== rv) return `i=${i}: pop mismatch got=${r[0]} exp=${rv}`;
        d = r[1];
      } else if (r !== null) {
        return `i=${i}: pop returned ${r[0]} on empty deque`;
      }
    } else {
      const r = KT.eject(d);
      if (ref.length > 0) {
        if (r === null) return `i=${i}: eject returned null but oracle non-empty`;
        const rv = ref.eject();
        if (r[1] !== rv) return `i=${i}: eject mismatch got=${r[1]} exp=${rv}`;
        d = r[0];
      } else if (r !== null) {
        return `i=${i}: eject returned ${r[1]} on empty deque`;
      }
    }

    const reg = KT.checkRegular(d);
    if (!reg.ok) return `i=${i}: irregular — ${reg.reason}`;
    if (fullCheck && !arrEq(KT.toList(d), ref.toList()))
      return `i=${i}: sequence mismatch\n   got ${JSON.stringify(KT.toList(d))}\n   exp ${JSON.stringify(ref.toList())}`;
  }
  if (!arrEq(KT.toList(d), ref.toList()))
    return `final sequence mismatch\n   got ${JSON.stringify(KT.toList(d))}\n   exp ${JSON.stringify(ref.toList())}`;
  return null;
}

// Persistence: snapshot the deque (+ its expected list) at random points, mutate
// the live branch, then verify every snapshot still reads its own sequence.
function persistenceSeed(seed: number, n: number): string | null {
  const rng = mulberry32(seed ^ 0x5bd1e995);
  let d: Deque<number> = KT.empty<number>();
  const ref = new Oracle<number>();
  let next = 1;
  const snaps: { d: Deque<number>; list: number[] }[] = [];
  for (let i = 0; i < n; i++) {
    if (rng() < 0.5) {
      d = KT.push(next, d);
      ref.push(next++);
    } else {
      const r = KT.pop(d);
      if (ref.length > 0 && r !== null) {
        ref.pop();
        d = r[1];
      }
    }
    if (rng() < 0.1) snaps.push({ d, list: KT.toList(d) });
  }
  for (let k = 0; k < snaps.length; k++) {
    const s = snaps[k]!;
    if (!arrEq(KT.toList(s.d), s.list)) return `snapshot ${k} changed after later ops (persistence broken)`;
  }
  return null;
}

function main(): void {
  const nSeeds = Number(process.argv[2] ?? "1000");
  const lengths = [60, 200, 1000, 4000];
  let failed = 0;
  for (let s = 0; s < nSeeds; s++) {
    const len = lengths[s % lengths.length]!;
    const seed = (Math.imul(s, 0x9e3779b1) + 0xdeadbeef) >>> 0;
    let reason: string | null;
    try {
      reason = fuzzSeed(seed, len) ?? persistenceSeed(seed, Math.min(len, 600));
    } catch (e) {
      reason = `threw: ${(e as Error).message}`;
    }
    if (reason !== null) {
      failed++;
      console.error(`FAIL seed=${seed} (s=${s}) len=${len}: ${reason}`);
      if (failed >= 8) break;
    }
    if (s % 100 === 0) process.stderr.write(`  ${s}/${nSeeds} (failed=${failed})\r`);
  }
  console.log(`\n[fuzz] seeds=${nSeeds}  failed=${failed}  ${failed === 0 ? "PASS ✓" : "FAIL ✗"}`);
  process.exit(failed > 0 ? 1 : 0);
}

main();
