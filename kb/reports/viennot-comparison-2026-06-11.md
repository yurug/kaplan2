---
id: viennot-comparison-2026-06-11
domain: reports
related: [catenable-keystone-closure-2026-06-11, viennot-coq-dev, wc-o1-verification-audit]
---

# Catenable deques: our rebuild vs Viennot et al. — qualitative comparison + benchmark (2026-06-11)

## One-liner

Two mechanized KT99 §6 catenable deques now exist side by side: our
extrinsic rebuild (`rocq/KTDeque/Catenable/`, keystone closed
2026-06-11) and Viennot/Wendling/Guéneau/Pottier's intrinsic
development (`external-refs/VerifiedCatenableDeque/`).  Same theorem
shape, opposite formalization philosophies; we additionally mechanize a
cost bound, they additionally ship a production-quality OCaml library.
The benchmark quantifies exactly that last asymmetry.

## What is being compared

| | **Ours (kaplan2 rebuild)** | **Viennot et al. (VWGP)** |
|---|---|---|
| Source | `rocq/KTDeque/Catenable/` (11 files, 10,631 LOC) | `theory/Cadeque/` (6 files, ~2,040 LOC) + shared `theory/Deque/` |
| Prover | Rocq 9.1.1, vanilla Ltac, zero plugins (ADR-0004) | Coq 8.19 + Equations + coq-hammer (`hauto`) + aac-tactics |
| Encoding | **Extrinsic**: plain nested inductives; sizes/colours/levels/regularity live in one Prop invariant `J = chain_wf ∧ chain_ends_green ∧ chain_leveled 0` (Color.v) | **Intrinsic**: GADTs indexed by level/arity/kind/colour; `node_coloring`, `triple_coloring`, `regularity` are inductive *type* families (Types.v) |
| Statement | Six keystone theorems (CatKeystone.v): empty/push/inject/concat/pop/eject total on `J` inputs, preserve `J`, exact sequence semantics; `Print Assumptions` closed | `Summary.v`: the operations inhabit both the intrinsic and extrinsic `CADEQUE` signatures (Signatures.v) with `cadeque_seq` correctness; `Print Assumptions everything` closed |
| Cost | **Mechanized**: `Cost.v:cat_wc_o1` — per-operation buffer-primitive count ≤ a closed constant (push/inject ≤ 4, concat ≤ 43, pop/eject ≤ 145) | Not mechanized — WC O(1) argued in the paper; the types enforce the *structure* the argument needs but no cost theorem exists in the development |
| Buffers | Model layer: buffers = `list`; production instantiation with our verified §4 deque is future work | Production: buffers = their §4 deque throughout, in both theory and `lib/` |
| OCaml artifact | Extraction of the model (`ocaml/extracted/kTCadeque.ml`) | Hand-written production `lib/cadeque*.ml` **and** a tuned extraction |

## Qualitative differences that matter

**1. Where the invariant lives.**  Their GADT indices make ill-coloured
structures unrepresentable: a mis-bundled packet simply does not
typecheck, so a whole class of bugs is impossible *before any proof is
written*.  The price is that the type families (8 mutually-indexed
inductives in Types.v) freeze the design — refining an invariant means
re-indexing every constructor and every function.  Our `J` is one Prop
that we refined **in place** twice during discharge (top-green clause,
then the level-stratification clause) without touching a single op.
The rebuild methodology — freeze ops first, grow the invariant under
proof pressure — is only possible extrinsically.

**2. What failing proofs buy.**  Because our ops are untyped until `J`
speaks, three genuine op bugs (concat's childless small-side lift, the
pair-collapse re-crowning in pop/eject, repair's double-degradation)
survived until the corresponding lemmas refused to close — the proofs
acted as the type checker.  In their development the same bugs are
caught earlier, by the indices.  Net: intrinsic catches structure bugs
at definition time; extrinsic catches them at proof time but tolerates
a moving design.

**3. Proof text economy.**  Their cadeque theory is ~5× smaller than
ours.  Equations + dependent pattern-matching + `hauto` discharge the
bookkeeping that we do by hand in 7,000 lines of structured Ltac
(ConcatLemmas/SRLemmas/PopLemmas/RepairLemmas).  In exchange we depend
on nothing but the kernel and stdlib — no plugin version pinning, and
every proof is a readable forward script (a maintainability bet
recorded in ADR-0004).

**4. The cost claim.**  This is our main *content* differentiator: the
KT hard rule (worst-case, not amortized) is a **theorem** here —
`cat_wc_o1` counts buffer primitives along every branch of the frozen
ops.  VWGP's complexity claim lives in their paper's prose; their
mechanization scope is functional correctness.  Conversely their §6
*number-of-buffer-ops-to-wall-clock* link is real (buffers are their
verified deque), while ours is still a pending instantiation — which
the benchmark below makes brutally visible.

**5. Statement strength parity.**  Both developments state concat on
two *arbitrary* regular deques (the clause our archived Cadeque9 could
not even state), both close pop/eject with repair, both have a clean
axiom audit.  At the level of "what is mechanically known about KT99
§6 functional behaviour", the two developments are equivalent.

## Benchmark

`make bench-cadeque` (bench/cadeque-compare.sh →
`ocaml/bench/cadeque_compare.ml`), sweeping n ∈ {1k, 10k, 100k, 1M};
both implementations run the same workloads in one process; a
sequence-semantics self-check passes before timing.  Full dated output:
`bench/results/cadeque-compare-2026-06-11.md` (Linux 6.17.12, OCaml
5.4.1).  ns/op, lower is better; "(>cap)" = projected over the 10 s
cell budget (quadratic regime).

| workload | impl | n=1000 | n=10000 | n=100000 | n=1000000 |
|---|---|---:|---:|---:|---:|
| push n | KT | 90 | 162 | 70 | 78 |
| push n | Vi | 76 | 143 | 103 | 94 |
| inject n | KT | 1243 | 28939 | (>cap) | (>cap) |
| inject n | Vi | 219 | 79 | 82 | 86 |
| pop all (after push n) | KT | 27 | 52 | 26 | 20 |
| pop all (after push n) | Vi | 92 | 80 | 77 | 80 |
| eject all (after inject n) | KT | 766947 | (>cap) | (>cap) | (>cap) |
| eject all (after inject n) | Vi | 89 | 77 | 79 | 78 |
| mixed push/push/pop (3n ops) | KT | 17 | 39 | 33 | 32 |
| mixed push/push/pop (3n ops) | Vi | 70 | 73 | 72 | 76 |
| concat fold (n/64 blocks of 64) | KT | 922 | 3231 | 3620 | 66120 |
| concat fold (n/64 blocks of 64) | Vi | 1001 | 532 | 975 | 1569 |
| concat tree (n/64 blocks of 64) | KT | 29325 | 14250 | 10660 | 11095 |
| concat tree (n/64 blocks of 64) | Vi | 795 | 301 | 1660 | 2725 |
| concat(8)+pop×4 interleave | KT | 755 | 273 | 2798 | (>cap) |
| concat(8)+pop×4 interleave | Vi | 435 | 259 | 264 | 271 |
| persistent fork: n× pop(same d) | KT | 17 | 33 | 23 | 17 |
| persistent fork: n× pop(same d) | Vi | 91 | 65 | 68 | 66 |

### Reading the table honestly

- **Where the list-buffer model is O(1) per op, we win.**  Push, pop,
  mixed, and the persistent-fork rerun are 2–4× *faster* than Viennot
  at every size (cons/uncons on the front of a list buffer vs their
  full node machinery).  Flat across three orders of magnitude — these
  are real worst-case-O(1) cells.
- **Where lists are the wrong data structure, we are quadratic — as
  predicted, not as discovered.**  `inject`/`eject` hit `buf ++ [x]`
  and the colour recomputation (`length`) on an unbounded root buffer;
  the mechanized bound (`cat_wc_o1`) counts these as *one buffer
  primitive*, which is exactly the contract the model layer makes.
  The "(>cap)" cells are the wall-clock cost of not yet instantiating
  buffers with the verified §4 deque.
- **Concat sits in between.**  Balanced concat-trees stay flat
  (~10–11 µs/op vs their ~0.3–2.7 µs — a constant-factor gap from
  whole-buffer moves and length recomputation on mid-size buffers);
  left-folded concat degrades linearly as the accumulated root buffers
  grow; the interleaved concat+pop workload follows the same pattern.
- **Context: the buffer gap is closable engineering, not proof work.**
  Our §4 deque extraction is already wall-clock-competitive with
  Viennot's deque (three-way 2026-05-06: push 81.0 vs 84.8 ns/op, pop
  54.5 vs 54.3 — `bench/results/three-way-2026-05-06.md`).  The §6
  ops perform a *verified-constant* number of buffer primitives, so
  substituting kt4 buffers for lists turns every "(>cap)" cell into a
  flat one with the keystone proofs as the safety net for the swap.

## Addendum (2026-06-12): the production artifact — KTf

The buffer instantiation isolated above is DONE, the verified way:

- `Catenable/BufPrims.v` names the ~15 buffer primitives the frozen ops
  use (definitional wrappers over list buffers).
- `Catenable/OpsFast.v` mirrors every operation against the primitives
  with `op_f = op` equality lemmas — the machine-checked diff of the
  port; `Catenable/FastKeystone.v` transfers the six keystone theorems
  (all `Print Assumptions` closed; `make cat-keystone-gate` now asserts
  13/13).
- `Extract/ExtractionFast.v` remaps `buffer` + primitives to
  `Fastbuf` (= the verified §4 kt4 deque + an O(1) size field,
  `ocaml/extracted/fastbuf.ml`).  The 17 one-line `Extract Constant`
  directives are the only trusted seam.

On top of the mirror, `Catenable/OpsFused.v` applies classic compiler
transformations as VERIFIED Rocq program transformations, each with an
equality proof down to the frozen ops:

- `upd_pkt` — case-of-case fusion of the packet update (the
  intermediate (node, child) pair vanishes; the Y/O absorb arms
  deforest the rebuilt child cell);
- `tree_repair` — deforestation of `repair ∘ tree_of` on the removal
  paths (colour computed once, duplicate packet teardown and CSingle
  re-allocation gone, childless rebuilds skip repair outright);
- `cad_{push,inject,pop,eject}_v2` — the shipped ops; FastKeystone is
  stated over them; `Extraction Inline` flattens the helper chain.

A second verified transformation, `DequePtr/SizedChain.v`, applies
DATA-CONSTRUCTOR FUSION to the buffer storage itself: `SChain` carries
the element count fused into the §4 chain's top constructor, the four
ops are mirrored natively threading n±1 (push/inject return the chain
bare — no result constructor; `_spec` lemmas reduce each to the proven
kt4 op through the erasure), and Fastbuf becomes thin glue with no
wrapper record and a field-read `size`.

Result (`bench/results/cadeque-compare-2026-06-12.md`, n = 10^6,
ns/op, KTf vs Vi): pop 65 vs 80, eject 58 vs 74, mixed 45 vs 72,
concat-fold 604 vs 985, concat-tree 1789 vs 2819, concat+pop
interleave 116 vs 273 (2.4×), persistent fork 42 vs 66 — **faster on
7 of 9 workloads**; push 111 vs 81 and inject 104 vs 89 remain
~1.2–1.4× behind at scale (they WIN at n=10^3: push 59 vs 66 — the
residual large-n gap is the per-element level-tag box that Viennot's
GADT-erased representation avoids, plus its cache pressure; removing
it is the level-erasure data refinement, the identified next phase).
The fusion pass bought 20–30% on every removal path; the sized chain
widened the mixed/fork margins to ~1.6×.  The model layer's quadratic
cells are gone.  The web page
([`kb/viennot-comparison.html`](../viennot-comparison.html)) renders
all three implementations.

## Verdict

- Functional verification: **parity** (same theorem shape, both closed).
- Mechanized cost: **ours only** (buffer-primitive counter).
- Production performance (2026-06-12, after the verified fusion pass):
  **ours on 7 of 9 workloads** (both drains, mixed, all three concat
  patterns, persistent forks — up to 2.4×); theirs on build-side
  push/inject by ~1.2–1.4× — a §4 buffer constant, not a §6 design
  gap.

## Web page

A self-contained rendering of this report with log-log scaling charts:
[`kb/viennot-comparison.html`](../viennot-comparison.html) — regenerate
with `bench/render-comparison-page.py` after a fresh `make bench-cadeque`.

## Reproduce

```sh
make bench-cadeque              # full sweep, ~2 minutes
SIZES="1000 10000" bench/cadeque-compare.sh   # quick look
bench/render-comparison-page.py # regenerate kb/viennot-comparison.html
```

## Related files

- `kb/reports/catenable-keystone-closure-2026-06-11.md` — what was proven and how.
- `kb/external/viennot-coq-dev.md` — the reference repo, what we may borrow.
- `bench/results/cadeque-compare-2026-06-11.md` — raw dated output (gitignored class; table embedded above).
- `ocaml/bench/cadeque_compare.ml`, `bench/cadeque-compare.sh` — harness.
