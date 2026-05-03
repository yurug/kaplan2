---
id: lessons
domain: meta
last-updated: 2026-05-03
---

# Lessons learned

Distilled, project-agnostic guidance for conducting a multi-language
verified-data-structure project (Rocq + OCaml + C + Rust). Captured
from extensive practice on the Kaplan-Tarjan deque, but framed so it
applies to any similar effort.

## What works

### Project setup

- **KB-first.** Build a knowledge base (PRD, specs, ADRs, properties,
  glossary) before touching code. The KB is the contract you read
  the source against. Without it, every implementation choice is a
  re-discovery.
- **One ADR per architectural decision.** When you make a choice
  (encoding style, heap layout, refinement strategy), write a short
  ADR with one-liner, scope, decision, alternatives rejected, and
  related files. Future-you will not remember why.
- **Pin toolchain versions in the KB.** "Rocq 9.1.1, dune 3.22" is a
  fact that decays. Write it down where it can be diffed.
- **An execution manual is not a spec.** Treat user-supplied execution
  manuals as one input among several. Cross-reference against the
  primary papers; flag conflicts and ask, don't auto-resolve.

### Verification engineering

- **Zero-admit invariant from day one.** `grep -rn "Admitted\|admit\."`
  must always return empty in the source tree. Once you allow one,
  the proof debt compounds. If a proof is too hard, leave it as a
  comment block stating the goal — never a stub `Admitted` lemma.
- **Define the invariant before optimizing the operations.** If you
  optimize first and try to fit an invariant later, you will discover
  the optimization broke the invariant after you've already shipped
  benchmarks.
- **Cost bound by structural inspection, not induction on depth.**
  Worst-case O(1) means proving cost ≤ k by reading the code, not by
  unrolling a recursion. If your proof needs `Fixpoint`, you've lost
  the bound.
- **Sequence preservation first, regularity preservation second.**
  Sequence (`op preserves the abstract list of elements`) is the
  easier and more important property. Get it before tackling the
  invariant preservation theorems.
- **Separate "proof artifact" operations from production operations.**
  Recursive `*_full` ops are useful as proof targets but must not be
  what you ship. Mark them clearly; document that the production
  paths are the non-recursive `exec_*_C`.

### Multi-language ports

- **Rocq is the source of truth; OCaml is extracted; C and Rust are
  hand-translated.** Don't reverse the dependency. Don't make the
  OCaml a hand-edited fork of the extraction.
- **Differential testing on the same fuzz workload.** Run the C/Rust
  port and the OCaml extraction on identical input streams; diff the
  output sequences. Anything else is theatre.
- **Self-contained per-language trees.** Every language tree should
  have its own README, its own build (`dune build` / `make` /
  `cargo`), and a clear path to "how does this relate to the spec".
  A reader should be able to enter `c/` and never have to look at
  the Rocq.

### Performance work

- **Measure before optimizing, measure after, and keep both.** Save
  the baseline numbers. Compare against them after every change.
  Without a recorded baseline you can't tell forward progress from
  regression.
- **Adversarial benchmarks reveal worst-case behavior.** Pure
  push-only or pop-only is misleading. Alt-push-pop, mixed
  P/I/Po/E, and fork-stress workloads expose what amortized analysis
  hides. Worst-case O(1) shows up as flat-across-sizes only here.
- **Profile the hot path symbolically before micro-optimizing.**
  Three causes of slowness — code-size cache pressure (L1i),
  per-op intrinsic work, allocator behavior — require different
  fixes. Treating them as one problem leads to wrong optimizations.

### Tactical Rocq

- **Use a single canonical name for aliased modules.** If
  `Module E := X.E` appears in both `Foo.v` and `Bar.v`, terms
  produced by one don't unify with terms produced by the other,
  even though they're definitionally equal. Pick one canonical
  reference per proof file and use it throughout.
- **Avoid blacklisting the term you want to reduce on a constructor.**
  When using `cbn -[X]` to keep `X` folded inside, make sure you don't
  also block the structural reduction that exposes the position of
  `X`. A common pattern: `cbn -[buf_seq_E]` reduces packet_seq on
  the outer constructor while keeping inner buffers folded.
- **Rebalancing equalities deserve a named lemma.** When the same
  `a ++ b ++ X ++ c ++ d = a' ++ b' ++ X ++ c' ++ d'` shape
  appears in multiple cases, factor it into a helper (e.g.,
  `rebal_eq`). Inline `rewrite + app_assoc` chains are unreadable
  and break easily.
- **Track implicit-argument inference carefully.** `Set Implicit
  Arguments` makes call sites brittle: a lemma whose `A` is
  implicit cannot be applied with `(lemma A _ _ H)` — only
  `(lemma H)`. When pose-proofing, count the explicit args.

### Extraction-aware design

- **Existentials extract to OCaml particularly well.** A Coq
  `{ l : nat & T l }` extracts to a 2-field block (the level and the
  payload, accessed via `Obj.magic`). Pattern matching and component
  projection are essentially free at runtime. A handwritten inductive
  with multi-arity constructors of similar logical content (e.g.,
  `XF1 a b | XF2 a b c d | …`) is *not* an obvious win: while it can
  save allocations on the construction side (one block of size 4
  vs. nested 2-blocks), the destruction side has to *materialize* fresh
  wrappers for the children, which the existential representation
  avoids. A balanced workload (build / destruct equally) washes out;
  asymmetric workloads see modest movement in either direction.
  **Implication**: when designing a verified data structure for OCaml
  extraction, default to existential / sigma-type encodings for
  recursively decomposable values. Pure inductives are fine for spec
  but rarely beat sigma types in extracted performance.
- **The abstraction is what makes representation changes cheap to
  *try* — but cheap to try does not guarantee cheap to win.** Hide
  the representation behind a Module Type, prove things abstractly,
  and you can A/B alternative instances in minutes. Most A/B
  experiments will fail to outperform the canonical instance; the
  point of the abstraction is that you find this out cheaply rather
  than after committing to an architecture.
- **Buffer-size choice depends on persistence.** For a fixed-capacity
  buffer at the heart of a deque-like structure, the right size is
  determined by whether you ship a persistent or a mutable
  implementation. *Persistent*: each push allocates a new buffer of
  the full capacity, so per-push cost is proportional to capacity.
  Cascades happen ~once per (capacity) pushes, so the two effects
  cancel and the constant factor (allocator throughput) dominates.
  Empirically the sweet spot is 5-7. *Mutable*: per-push cost stays
  O(1) regardless; cascades are the only non-trivial cost; larger
  is unambiguously better up to L1/L2 cache thresholds. The same
  algorithm wants very different buffer sizes in the two regimes.
- **Modern gcc -O3 has already done most "manual engineering"
  optimizations.** Static-code-reading audits often predict large
  gains from extracting cold paths into `__attribute__((cold,noinline))`
  helpers, manually adding `inline` keywords, replacing branches with
  LUTs, etc. With `__builtin_expect` already in place, gcc does this
  automatically: cold-section splitting (visible as `.cold` symbols
  in `nm`), inlining via size heuristics, branch reordering. *Manual*
  versions of these optimizations frequently *regress* because they
  add function-call overhead or memory loads that the compiler had
  already eliminated. **Validate audit predictions empirically before
  committing.** Lever-of-last-resort: a sampling profiler (perf,
  vtune) to find the real hot path, not static reading.
- **Persistent C beats OCaml only with arena compaction enabled.**
  OCaml's minor GC is essentially a built-in generational arena that
  fits in L2 and reclaims short-lived blocks for free. A bump-pointer
  C arena without compaction grows unbounded and quickly spills the
  working set out of cache, paying L3/RAM latency on every read.
  Default *on* compaction at K = 4096 (compact every 4096 ops);
  smaller intervals don't help in practice. The C wins on pop / eject
  by ~30% with compaction on; without it, the C is 4-5× slower than
  OCaml on the same workload.

### Subagents and delegation

- **Delegate case-heavy mechanical proofs.** Lemmas closable by
  `destruct + cbn + lia` over a small inductive type are
  agent-tractable: dispatch them to subagents instead of grinding.
- **Don't delegate understanding.** Subagents are fine for
  searching, mechanical case work, and bench-running. They are not
  fine for deciding what the invariant should be or what the
  algorithm is doing. Synthesize the design yourself, then ask the
  subagent to execute.
- **Trust but verify subagent reports.** The summary returned by an
  agent describes what it intended to do, not what it did. Always
  inspect the diff before reporting completion to the user.

## What doesn't work

### Verification anti-patterns

- **Claiming "structural impossibility" without verification.** If a
  proof is hard or a benchmark fails, the answer is rarely "this
  representation cannot work". The answer is usually "the invariant
  isn't being maintained" or "the algorithm has a missing step".
  Look one level deeper before declaring impossibility.
- **Deriving color/regularity from buffer sizes alone.** In an
  algorithm like Kaplan-Tarjan that has *contextual* color (the
  same buffer shape can be tagged differently depending on history),
  buffer-derived color is wrong. Carry the explicit tag.
- **Falling back to amortized analysis to "fix" a worst-case bound
  failure.** If your worst-case op fails because cascade exceeded
  depth 1, the fix is to maintain the invariant that prevents that.
  Wrapping the broken op in a `Fixpoint` is *not* a fix — it is
  capitulation.
- **Trusting that hand-translated code matches the spec by
  inspection.** Even careful hand-translation produces subtle bugs
  (off-by-one in cascade, swapped buffer sides, wrong color
  computation). Differential fuzz against the extracted reference
  is the only reliable check.
- **Trusting `Admitted` as a placeholder.** Once a single `Admitted`
  is in the tree, downstream code treats it as a true theorem.
  Cleaning it up later requires walking back all dependent uses.
  Cheaper to leave a comment block than to admit.

### Process anti-patterns

- **Pre-commit hooks that auto-format the proof script.** Coq proofs
  are sensitive to whitespace inside tactics; auto-formatting reorders
  bullets and breaks the build. Disable formatters on `.v` files.
- **Optimizing before measuring against the reference.** Until you've
  benchmarked your impl against the existing reference (e.g.,
  Viennot's OCaml), you don't know whether a given optimization
  matters. Measure first.
- **Bench-driven validation without a "no-allocator" baseline.**
  Most "your-language is slower than mine" results are allocator
  differences. Subtract the allocator cost (e.g., per-op malloc
  count) before claiming an algorithmic gap.
- **Squashing bug-fixes into "miscellaneous cleanup" commits.** Every
  bug found and fixed is a learning opportunity. Tag the fix with
  the failing test or theorem so future-you can find it.
- **Treating PDF execution manuals as ground truth.** Manuals are
  one author's interpretation. Cross-reference against the primary
  paper and against any reference Coq dev. When they disagree, the
  primary paper wins (with the manual's deviations called out
  explicitly in an ADR).

### Refactoring anti-patterns

- **Refactoring the data layout before proving anything.** A clean
  layout that won't yield to the proof obligations isn't clean. Do
  the messy version, prove the lemma, then refactor — and re-prove.
- **Renaming modules without grepping consumers.** Coq's module
  aliasing makes this especially painful. A rename can pass `dune
  build` because the alias still resolves, then break a downstream
  proof's `rewrite` because the syntactic identity changed.
- **Removing the `_full` recursive variant once non-recursive lands.**
  The recursive variant is useful as a refinement target and as a
  sanity check ("the simple algorithm gives the same answer"). Mark
  it as a proof artifact; don't delete it.

### Performance anti-patterns

- **Optimizing one workload while regressing another.** A change that
  makes pure push faster by 10% but mixed-workload slower by 30% is
  almost always a loss in real use. Bench all workloads after every
  change.
- **Microbench in isolation from the production path.** A
  microbench that calls a hot loop with no surrounding allocation
  pressure overstates the speed. Either include realistic noise or
  cite the synthetic context explicitly.
- **Premature data-layout optimization.** Bit-packing buffer sizes
  into pointer tag bits looks great in isolation; in practice, the
  decode cost on every read can erase the savings. Profile before
  packing.

## Workflow patterns

- **End each work block with a short summary of what was completed,
  what's next, and what you learned.** Even (especially) for solo
  work. These summaries become the audit trail for understanding why
  a decision was made six months later.
- **The audit cycle: implement → audit → fix → re-audit.** Until
  the audit comes back GREEN, the work isn't done. Audits should
  cover provability gaps, simplicity (could this be smaller?),
  spec compliance, and test coverage.
- **One milestone, one summary.** When a milestone (a phase, a
  release, a paper deadline) is reached, write a single
  consolidating document. Discard the per-step minutiae once
  consolidated.
