# `ts/` — TypeScript port of the Kaplan–Tarjan deque

A faithful TypeScript port of the kaplan2 **§4** purely-functional worst-case
O(1) deque **and the §6 catenable deque (`concat`)**, verified by **the same
method as the [`c/`](../c) port**: differential testing against a naive oracle,
a structural regularity check after every operation, a persistence stress, a
flat-allocations worst-case cost bound, and — for §6 — a **byte-for-byte trace
diff against the Rocq-extracted OCaml reference**.

The source of truth it is translated from is the Rocq-extracted certified
implementation [`ocaml/extracted/kTDeque.ml`](../ocaml/extracted/kTDeque.ml)
(the `*_kt2` production operations over the colour-tagged `kChain`, from
`rocq/KTDeque/DequePtr/OpsKT.v`).  The test — not the translation — is the
authority on correctness.

## Layout

```
src/
  element.ts   ElementTree: a level-ℓ element = a perfect binary tree of 2^ℓ base values (§4)
  buf5.ts      Buf5 (0..5 elements) + colours + size-guarded buffer ops (§4)
  deque.ts     §4: Chain/Packet model, green_of_red_k repair, the four *_kt2 ops, checkRegular
  cadeque.ts   §6: stored-triple cchain tree, tree_of, the pop/eject repair, and O(1) concat
  index.ts     public API (§4 push/pop/inject/eject; §6 cadPush/…/cadConcat)
  alloc.ts     allocation counter (for the worst-case cost tests)
test/
  oracle.ts    naive array-backed reference deque (the ground truth)
  fuzz.ts      §4 differential fuzzer + persistence stress  (analogue of c/tests/fuzz.c)
  wc.ts        §4 worst-case allocations-per-op bound        (analogue of c/tests/wc_test.c)
  fuzz6.ts     §6 differential fuzzer incl. concat            (analogue of c/tests/fuzz_cadeque.c)
  wc6.ts       §6 worst-case cost incl. O(1) concat
  difftrace.ts §6 trace driver — diffed against the OCaml extraction (see below)
  debug.ts     §4: replay a seed and dump the chain at the first irregular op
```

## Run

```sh
npm install        # typescript + esbuild + @types/node (dev only)
npm run typecheck  # tsc --noEmit (strict)
npm run fuzz 2000  # §4: 2000 differential seeds  (default 1000)
npm run wc         # §4: per-op alloc max must stay flat as n→1e6
npm run fuzz6 2000 # §6: differential seeds incl. concat
npm run wc6        # §6: per-op allocs flat incl. O(1) concat
npm test           # typecheck + all four  (the pre-commit gate)
npm run bundle     # dist/ktdeque.js — dependency-free ESM bundle for the browser viz

./difftrace-vs-ocaml.sh 60   # §6 byte-for-byte vs the Rocq-extracted OCaml reference (needs dune)
```

Passing looks like `[fuzz] … PASS ✓`, `[wc] … worst-case O(1) ✓`,
`[fuzz6] … PASS ✓`, `[wc6] … incl. concat ✓`, and `[difftrace] … IDENTICAL ✓`.

## Hard rule

Per the project [CLAUDE.md](../CLAUDE.md): the operations are the **non-recursive**
`*_kt2` repair (`green_of_red_k` touches a constant number of cells via packet
aggregation), never a recursive `*_full` cascade.  `npm run wc` is the test that
would catch a regression to an O(log n) cascade.
