# `ts/` — TypeScript port of the Kaplan–Tarjan deque

A faithful TypeScript port of the kaplan2 §4 purely-functional **worst-case
O(1)** deque (§6 catenable `concat` is in progress), verified by **the same
method as the [`c/`](../c) port**: differential testing against a naive oracle,
a structural regularity check after every operation, a persistence stress, and
a flat-allocations worst-case cost bound.

The source of truth it is translated from is the Rocq-extracted certified
implementation [`ocaml/extracted/kTDeque.ml`](../ocaml/extracted/kTDeque.ml)
(the `*_kt2` production operations over the colour-tagged `kChain`, from
`rocq/KTDeque/DequePtr/OpsKT.v`).  The test — not the translation — is the
authority on correctness.

## Layout

```
src/
  element.ts   ElementTree: a level-ℓ element = a perfect binary tree of 2^ℓ base values
  buf5.ts      Buf5 (0..5 elements) + colours + size-guarded buffer ops
  deque.ts     Chain/Packet model, green_of_red_k repair, the four *_kt2 ops, checkRegular
  index.ts     public API: empty / push / inject / pop / eject / toList / length
  alloc.ts     allocation counter (for the worst-case cost test)
test/
  oracle.ts    naive array-backed reference deque (the ground truth)
  fuzz.ts      differential fuzzer + persistence stress  (analogue of c/tests/fuzz.c)
  wc.ts        worst-case allocations-per-op bound        (analogue of c/tests/wc_test.c)
  debug.ts     replay a seed and dump the chain at the first irregular op
```

## Run

```sh
npm install        # typescript + esbuild + @types/node (dev only)
npm run typecheck  # tsc --noEmit (strict)
npm run fuzz 2000  # 2000 differential seeds  (default 1000)
npm run wc         # worst-case cost: per-op alloc max must stay flat as n→1e6
npm test           # typecheck + fuzz + wc  (the pre-commit gate)
npm run bundle     # dist/ktdeque.js — dependency-free ESM bundle for the browser viz
```

Passing looks like: `[fuzz] seeds=2000 failed=0 PASS ✓` and
`[wc] ... BOUNDED & FLAT — worst-case O(1) ✓`.

## Hard rule

Per the project [CLAUDE.md](../CLAUDE.md): the operations are the **non-recursive**
`*_kt2` repair (`green_of_red_k` touches a constant number of cells via packet
aggregation), never a recursive `*_full` cascade.  `npm run wc` is the test that
would catch a regression to an O(log n) cascade.
