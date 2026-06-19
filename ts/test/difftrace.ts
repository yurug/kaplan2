/**
 * difftrace.ts — TypeScript twin of ocaml/extracted/difftrace6.ml.  Identical
 * mulberry32 PRNG and op sequence; prints one line per op = the current
 * sequence, space-separated.  Diff its output byte-for-byte against the OCaml
 * extraction's difftrace6 to cross-check the §6 port against the reference.
 *   Args: [SEED] [N]   (defaults 12345 200)
 */
import { cadEmpty, cadPush, cadInject, cadPop, cadEject, cadConcatChecked, cadToList, type Cchain } from "../src/cadeque.js";

let state = 0;
function seedPrng(s: number): void {
  state = s | 0;
}
function nextUnit(): number {
  let a = state | 0;
  a = (a + 0x6d2b79f5) | 0;
  state = a;
  let t = Math.imul(a ^ (a >>> 15), 1 | a);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  const r = (t ^ (t >>> 14)) >>> 0;
  return r / 4294967296;
}
const irange = (n: number): number => Math.floor(nextUnit() * n);

function main(): void {
  const seed = Number(process.argv[2] ?? "12345");
  const n = Number(process.argv[3] ?? "200");
  seedPrng(seed);
  let d: Cchain<number> = cadEmpty<number>();
  let next = 1;
  const out: string[] = [];
  for (let i = 0; i < n; i++) {
    const op = irange(100);
    if (op < 28) {
      d = cadPush(next, d);
      next++;
    } else if (op < 56) {
      d = cadInject(d, next);
      next++;
    } else if (op < 71) {
      const r = cadPop(d);
      if (r !== null) d = r[1];
    } else if (op < 86) {
      const r = cadEject(d);
      if (r !== null) d = r[0];
    } else {
      const cnt = irange(14);
      let d2: Cchain<number> = cadEmpty<number>();
      for (let j = 0; j < cnt; j++) {
        if (nextUnit() < 0.5) {
          d2 = cadPush(next, d2);
          next++;
        } else {
          d2 = cadInject(d2, next);
          next++;
        }
      }
      d = cadConcatChecked(d, d2);
    }
    out.push(cadToList(d).join(" "));
  }
  process.stdout.write(out.join("\n") + "\n");
}

main();
