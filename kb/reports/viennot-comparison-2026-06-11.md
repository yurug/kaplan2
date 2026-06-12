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
ns/op, KTf vs Vi): pop 74 vs 83, eject 69 vs 75, mixed 48 vs 72,
concat-fold 597 vs 987, concat-tree 1903 vs 2899, concat+pop
interleave 122 vs 268 (2.2×), persistent fork 40 vs 65 — **faster on
7 of 9 workloads**; push 113 vs 80 and inject 109 vs 91 remain
~1.2–1.4× behind at scale (they WIN at n=10^3: push 49 vs 67).
The fusion pass bought 20–30% on every removal path; the sized chain
removed the wrapper record and result constructor.  The model layer's
quadratic cells are gone.  The web page
([`kb/viennot-comparison.html`](../viennot-comparison.html)) renders
all three implementations.

**Negative result, measured and reverted (level-erasure seam).**  A
tag-checked zero-box element representation (leaves unboxed,
level-carrying tag-3 pair blocks behind an `Extract Constant` remap of
the six ElementTree members) was implemented and A/B-benchmarked under
identical machine load: it LOST 10–25% across the board (push 139 vs
the sized chain's 112; fork 57 vs 42).  Mechanism: `E.level`/`E.unpair`
are consulted at every pairing site, and the tag check replaces a hot
field read on the freshly-allocated sigT box with a header-byte load on
the cold leaf payload — the box doubles as a level cache.  Conclusion:
matching Viennot's build-side numbers requires erasing the level
CHECKS, not the level data (unchecked `EPair`, blind `unpair` — sound
exactly where their erased GADT indices are: statically).  That is the
conditional-naturality mirror of the §4 ops in Rocq — the genuine
next-phase project.  (The reverted implementation survives at commit
`4d774ab` for reference.)

## Addendum (2026-06-12, check erasure): the third verified pass

`Common/ErasedTree.v` + `DequePtr/ErasedOps.v`: mirrors of the §4
sized ops over CHECK-FREE elements — every `Nat.eq_dec (E.level …)` +
proof-carrying `E.pair` becomes an unchecked `EPair`, every
`match E.unpair` a structural match.  Each mirror carries a
success-conditional naturality lemma (`f args = Some r ->
f_e (er args) = Some (er r)`) down to the keystone-proven kt4 ops;
the audit showed every `unpair = None` arm is failure propagation, so
the blind extraction (`Extract Inductive etree` → `eraw.ml`: zero-box
leaves, one-block pairs, field reads without discrimination) is pinned
by the lemmas on every input reachable from regular chains.  This is
the statically-justified form of Viennot's erased GADT indices.

Result (`bench/results/cadeque-compare-2026-06-12.md`, KTf vs Vi):
margins widen across the board — at 10⁶: mixed 48 vs 73, concat-fold
549 vs 1078 (2×), concat-tree 1414 vs 3023 (2.1×), interleave 116 vs
271 (2.3×), fork 44 vs 65, pop 65 vs 81, eject 61 vs 75 — and the
build ops now WIN at small/mid sizes (push 51 vs 57 at 10³, 96 vs 102
at 10⁴), trailing only at 10⁶ (112 vs 84, 103 vs 90).  With element
representation now cost-free, the residual large-n gap is the §6
spine's allocation count (CSingle∘Pkt∘Node = three nested blocks per
op vs their flatter cells) under large-heap GC pressure — a §6
representation-fusion data refinement is the next candidate phase.

## Addendum (2026-06-12, spine fusion): the fourth verified pass — a measured neutral

`Catenable/FlatChain.v` + `FlatOps.v` + `FlatKeystone.v`: data-constructor
fusion of the §6 spine.  The dominant cell `CSingle (Pkt BHole (Node k p s))
rest` (three nested blocks, rebuilt by every push/inject and every green/red
rebundle) becomes the single constructor `FFlat k p s rest`; the general
packet cell fuses `CSingle∘Pkt` into `FSingle`.  Correctness is by a TOTAL
erasure `fc_er : fchain -> cchain` with an unconditional commutation lemma
per operation (`op_f (erased args) = option_map fc_er (op_x args)`) across
the entire production web — push/inject, the concat builders, raw pop/eject,
and the full repair web including `drain_both` (a 169-leaf shape analysis
closed by one uniform tactic).  The six keystone theorems transfer
(`FlatKeystone.v`; gate now 19/19), and extraction ships the fused ops
(`kTFlatCadeque.ml`).

**The measured verdict is NEUTRAL** (same-binary interleaved A/B,
`ocaml/bench/flat_ab*.ml`, taskset-pinned, medians of 9 at 10⁶):
pop 63→61, eject 63→59, push 103→105, inject 103→103, mixed 48→49,
concat-fold parity, fork 43→49.  The working hypothesis — that the §6
spine's allocation count drives the residual 10⁶ push/inject gap — is
**refuted**: spine cells are replaced on every operation, so they die in
the minor heap, and OCaml's bump-allocated young garbage costs ~nothing;
fusing three young blocks into one is invisible at this scale.  The
artifact is kept as production (strictly fewer allocations, full theorem
backing, no net regression), and the residual diagnosis moves DOWN a
layer: the remaining push/inject constant lives in the per-operation §4
buffer work (the Fastbuf push path itself) versus Viennot's flat
steady-state buffer cells — i.e. in retained structure and instruction
count, not in §6 garbage volume.

Final standings with the fused artifact
(`bench/results/cadeque-compare-2026-06-12.md`, KTf vs Vi at 10⁶):
pop 63 vs 80, eject 61 vs 76, mixed 47 vs 72, concat-fold 476 vs 1079
(2.3×), concat-tree 1523 vs 2881 (1.9×), interleave 116 vs 265 (2.3×),
fork 51 vs 66 — 7/9; push 117 vs 87, inject 105 vs 89.

## Addendum (2026-06-12, element unboxing): the fifth pass — 9/9

Profiling the push loop head-to-head (perf + GC stats) located the
residual exactly: **we retained 5.0 live words per element vs their
3.0** — one `FGround` box (a 2-word block) around EVERY element in the
§6 buffers, the §6 analogue of the §4 `sigT` box.  The extra 2 w/el
drove 60% more promotion and the major-GC tax (marking + sweep) that
was the whole push/inject deficit; instruction counts outside GC were
already comparable.

The erasure reuses the blind-seam recipe one layer up.  Under `J`,
`chain_leveled 0` stratifies cells perfectly: level-0 cells are always
ground, child-level cells never are — so no §6 site discriminates
ground-vs-structural with both arms live.  The two match disciplines
became named wrappers (`cell_case_ground` / `cell_case_struct` in
FlatChain.v), and `fstored` extracts to the zero-box carrier `Sraw.t`
(`ground = Obj.repr` — the cell IS its payload; small/big = ordinary
tagged blocks).  No raw `fstored` match survives extraction (the
carrier match function traps), the fallback continuations are dropped
blindly, and FlatKeystone.v is the static justification that they are
unreachable on `fJ` inputs.  Gate stays 19/19; the Coq proofs are
unchanged in substance.  Two harness fixes landed alongside: `Nat.min`
extraction (was recursive Peano over int) and per-cell `Gc.compact` in
the bench (cells no longer inherit the model layer's quadratic
allocation history).

Result: retained memory **equals Viennot's exactly** (3.00 w/el), and
KTf now beats Viennot on **all 36 cells** of the sweep.  At 10⁶:
push 89 vs 96, inject 89 vs 97, pop 61 vs 78, eject 59 vs 75, mixed
46 vs 76, concat-fold 146 vs 1174 (8×), concat-tree 1425 vs 3166
(2.2×), interleave 91 vs 277 (3×), fork 42 vs 67.  Paired A/B vs the
previous artifact: push 97→80, inject 95→79, mixed 47→43, fold 7→2
ns/op.

## Verdict

- Functional verification: **parity** (same theorem shape, both closed).
- Mechanized cost: **ours only** (buffer-primitive counter).
- Production performance (2026-06-12, after the element-unboxing
  pass): **ours on 9 of 9 workloads, every size** — up to 8× on
  concat-fold, 3× on interleave, ~1.3–1.7× on drains/mixed/fork, and
  ~1.1× on push/inject; retained memory identical (3.00 live
  words/element).

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
