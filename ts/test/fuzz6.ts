/**
 * §6 catenable-deque differential fuzzer.  Random push/inject/pop/eject AND
 * concat against a naive array oracle (concat = array concatenation); full
 * flattened-sequence equality after every op.  Run: `npm run fuzz6 [nSeeds]`.
 */
import {
  cadEmpty,
  cadPush,
  cadInject,
  cadPop,
  cadEject,
  cadConcatChecked,
  cadToList,
  type Cchain,
} from "../src/cadeque.js";

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
  let d: Cchain<number> = cadEmpty<number>();
  let ref: number[] = [];
  let next = 1;

  for (let i = 0; i < n; i++) {
    const op = Math.floor(rng() * 100);
    if (op < 28) {
      d = cadPush(next, d);
      ref.unshift(next++);
    } else if (op < 56) {
      d = cadInject(d, next);
      ref.push(next++);
    } else if (op < 71) {
      const r = cadPop(d);
      if (ref.length > 0) {
        if (r === null) return `i=${i}: pop null but oracle non-empty`;
        if (r[0] !== ref[0]) return `i=${i}: pop got=${r[0]} exp=${ref[0]}`;
        ref.shift();
        d = r[1];
      } else if (r !== null) return `i=${i}: pop returned ${r[0]} on empty`;
    } else if (op < 86) {
      const r = cadEject(d);
      if (ref.length > 0) {
        if (r === null) return `i=${i}: eject null but oracle non-empty`;
        if (r[1] !== ref[ref.length - 1]) return `i=${i}: eject got=${r[1]} exp=${ref[ref.length - 1]}`;
        ref.pop();
        d = r[0];
      } else if (r !== null) return `i=${i}: eject returned ${r[1]} on empty`;
    } else {
      // concat with a freshly-built random operand
      const cnt = Math.floor(rng() * 14);
      let d2: Cchain<number> = cadEmpty<number>();
      const ref2: number[] = [];
      for (let j = 0; j < cnt; j++) {
        if (rng() < 0.5) {
          d2 = cadPush(next, d2);
          ref2.unshift(next++);
        } else {
          d2 = cadInject(d2, next);
          ref2.push(next++);
        }
      }
      d = cadConcatChecked(d, d2);
      ref = ref.concat(ref2);
    }
    if (!arrEq(cadToList(d), ref))
      return `i=${i} op=${op}: sequence mismatch\n   got ${JSON.stringify(cadToList(d))}\n   exp ${JSON.stringify(ref)}`;
  }
  return null;
}

function main(): void {
  const nSeeds = Number(process.argv[2] ?? "1000");
  const lengths = [40, 120, 400, 1200];
  let failed = 0;
  for (let s = 0; s < nSeeds; s++) {
    const len = lengths[s % lengths.length]!;
    const seed = (Math.imul(s, 0x9e3779b1) + 0xdeadbeef) >>> 0;
    let reason: string | null;
    try {
      reason = fuzzSeed(seed, len);
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
  console.log(`\n[fuzz6] seeds=${nSeeds}  failed=${failed}  ${failed === 0 ? "PASS ✓" : "FAIL ✗"}`);
  process.exit(failed > 0 ? 1 : 0);
}

main();
