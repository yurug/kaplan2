// Replay a seed, check regularity after each op, and on the first irregular
// state dump the op and the full chain structure (sizes + colours per level).
import * as KT from "../src/index.js";
import type { Deque } from "../src/index.js";
import type { Chain, Packet } from "../src/deque.js";
import { bufColor } from "../src/buf5.js";

function mulberry32(a: number): () => number {
  return () => {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function dumpPacket(p: Packet<number>, indent: string): string {
  if (p.tag === "hole") return `${indent}Hole`;
  const col = bufColor(p.pre) === "red" || bufColor(p.suf) === "red" ? "RED" : "ok";
  return (
    `${indent}PNode pre=${p.pre.length}(${bufColor(p.pre)}) suf=${p.suf.length}(${bufColor(p.suf)}) [${col}]\n` +
    dumpPacket(p.inner, indent + "  ")
  );
}

function dumpChain(c: Chain<number>, depth = 0): string {
  if (c.tag === "end") return `${"  ".repeat(depth)}Ending b=${c.b.length}(${bufColor(c.b)})`;
  return (
    `${"  ".repeat(depth)}Cons:\n` +
    dumpPacket(c.p, "  ".repeat(depth) + "  ") +
    "\n" +
    dumpChain(c.c, depth + 1)
  );
}

const seed = Number(process.argv[2] ?? "2095397024");
const n = Number(process.argv[3] ?? "200");
const rng = mulberry32(seed);
let d: Deque<number> = KT.empty<number>();
let prev: Deque<number> = d;
let next = 1;
const log: string[] = [];

for (let i = 0; i < n; i++) {
  const op = Math.floor(rng() * 100);
  let name = "";
  try {
    if (op < 30) {
      name = `push ${next}`;
      d = KT.push(next++, d);
    } else if (op < 60) {
      name = `inject ${next}`;
      d = KT.inject(d, next++);
    } else if (op < 80) {
      name = "pop";
      const r = KT.pop(d);
      if (r) d = r[1];
    } else {
      name = "eject";
      const r = KT.eject(d);
      if (r) d = r[0];
    }
  } catch (e) {
    console.log(`\n=== THREW at i=${i} op=${name} ===\n${(e as Error).message}`);
    console.log(`\n--- chain BEFORE this op ---\n${dumpChain(prev as Chain<number>)}`);
    process.exit(0);
  }
  log.push(name);
  const reg = KT.checkRegular(d);
  if (!reg.ok) {
    console.log(`\n=== FIRST IRREGULAR at i=${i} op=${name}: ${reg.reason} ===`);
    console.log(`\n--- chain BEFORE this op ---\n${dumpChain(prev as Chain<number>)}`);
    console.log(`\n--- chain AFTER this op ---\n${dumpChain(d as Chain<number>)}`);
    console.log(`\n--- last ops ---\n${log.slice(-8).join("\n")}`);
    process.exit(0);
  }
  prev = d;
}
console.log(`seed=${seed}: ${n} ops, all regular`);
