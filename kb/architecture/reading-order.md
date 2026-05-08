---
id: architecture-reading-order
domain: architecture
related: [overview, spec/why-bounded-cascade, spec/algorithms]
---

# Reading order — a guided tour for new readers

This document is for someone seeing the codebase for the first time.
It walks you from "what is this?" to "I can read any file in the
project and know why it's there", in a single linear path.  Estimated
reading time: 90 minutes for the full tour, 20 minutes for stops 1-3
alone.

## The shape of the project

The repository proves and ships a Kaplan-Tarjan persistent real-time
deque — push, pop, inject, eject, all worst-case O(1).  There is one
artefact in three forms:

  - the **algorithm**, formalised in Rocq;
  - the **OCaml extraction**, distributed as the [ktdeque] opam
    package;
  - the **C port**, distributed as the [libktdeque] static library.

The Rocq is the source of truth.  The OCaml is a near-mechanical
projection.  The C is hand-written but mirrors the Rocq operationally
and is property-tested against the OCaml extraction.

## Stop 1 — The intuition (10 min)

**Read [`kb/spec/why-bounded-cascade.md`](../spec/why-bounded-cascade.md).**

This is the only document you need to read in full to understand the
algorithm.  It explains:

- why a *persistent* deque with WC O(1) is non-trivial (amortised
  schemes don't survive forking);
- the trick — colour every buffer Green / Yellow / Red and forbid two
  Reds adjacent (the *regularity invariant*);
- why this gives a constant repair cost — `ensure_green` fires
  `green_of_red` exactly once per public op, not log N times;
- why packets must aggregate yellow runs into a single allocation
  (else re-threading would be O(yellow-run-length));
- the proof-artefact-vs-production-code distinction (some Rocq
  functions are recursive O(log N) and exist only as proof targets).

Once this clicks, the names you see throughout the codebase
(`Green`, `Yellow`, `Red`, `Packet`, `Chain`, `make_small`,
`green_of_red`, `ensure_green`, `regular_kt`, `kt_packet`,
`color_from_bufs`) are no longer arbitrary; they are the obvious
vocabulary for the trick.

## Stop 2 — The public surface (10 min)

Pick the language you care about and skim its public-API file:

- **OCaml**: [`ocaml/extracted/kTDeque.mli`](../../ocaml/extracted/kTDeque.mli) —
  start at the `{1 KTDeque}` module-level docstring at the top.  It
  has a quick-start example, a "where to look" table pointing at the
  `kt2` family, and explains the foreign-looking `Coq_E.t` element
  type.  Then read the `(** *)` docs on `empty_kchain`, `push_kt2`,
  `pop_kt2`, `inject_kt2`, `eject_kt2`, `kchain_to_list`.  That is
  the public surface.

- **C**: [`c/include/ktdeque.h`](../../c/include/ktdeque.h) — start
  at the top file header (Quick Start, Element Model, Threading,
  Arena Management).  Then read `kt_empty`, `kt_push`, `kt_pop`,
  `kt_inject`, `kt_eject`.  The arena and region API below are for
  long-running programs; you can skip them on first read.

Either of those gives you a runnable example to anchor the
algorithm to concrete code.  Don't read the implementation yet.

## Stop 3 — A worked example (5 min)

Build and run one of the hello programs:

  - `cd ocaml/examples && dune exec ./hello.exe`
  - `cd c && make examples/hello && c/examples/hello`

Each is heavily commented and shows the four ops plus a persistence
demo.  This anchors the type signatures from Stop 2 to executable
behaviour.

## Stop 4 — The Rocq spec, top-down (30 min)

Now you can profitably read the formal spec.  In order:

1. **[`Common/Element.v`](../../rocq/KTDeque/Common/Element.v)** —
   what an "element" is (`E.t A` = level-l value).  The header has a
   worked example with `E.pair (E.base 1) (E.base 2)` flattening to
   `[1; 2]`.

2. **[`Common/Buf5.v`](../../rocq/KTDeque/Common/Buf5.v)** — the
   six-constructor buffer (`B0..B5`).  Skim the colour table.

3. **[`Common/Color.v`](../../rocq/KTDeque/Common/Color.v)** — the
   three-colour type.  The header points back at
   why-bounded-cascade.md §2.

4. **[`DequePtr/Model.v`](../../rocq/KTDeque/DequePtr/Model.v)** —
   the recursive shape: `Packet` (yellow run) and `Chain`
   (alternating coloured packets).  Read the file header, then
   skip the `[Inductive Packet]` / `[Inductive Chain]` definitions
   (they are exactly what the header describes).  Move on.

5. **[`DequePtr/OpsKT.v`](../../rocq/KTDeque/DequePtr/OpsKT.v)** —
   the production WC O(1) operations.  Read the file header (the
   "Three execution variants" subsection is essential).  Then read
   the `green_of_red` and `ensure_green` section banners — both
   have prose intros explaining the three Viennot cases.

6. **[`DequePtr/OpsKTSeq.v`](../../rocq/KTDeque/DequePtr/OpsKTSeq.v)**
   — sequence preservation.  Read the file header (the "## Proof
   method" subsection explains the recurring buffer-level recipe).
   Then skim the section banners; each one carries a "Method:"
   preface explaining its specific recipe.

7. **[`DequePtr/OpsKTRegular.v`](../../rocq/KTDeque/DequePtr/OpsKTRegular.v)**
   — the production regularity invariant `regular_kt`.  Read the
   header; skip the body unless you're working on the preservation
   theorems.

8. **[`DequePtr/Footprint.v`](../../rocq/KTDeque/DequePtr/Footprint.v)**
   — the cost bound.  Read the header (the "Cost accounting" section
   gives you `NF_PUSH_PKT_FULL = 9`).  Search for `Definition NF_PUSH_PKT`
   and read the cost-bound lemma for one op (e.g. `push_pkt_naive_C_cost`).
   This closes the loop on "WC O(1) means at most 9 heap ops per
   public call".

## Stop 5 — The C runtime (15 min)

Open [`c/src/ktdeque_dequeptr.c`](../../c/src/ktdeque_dequeptr.c).
The file is long (~2800 lines) but structured.  Read in order:

1. The file-level header — the "READ FIRST" pointer back at
   why-bounded-cascade.md.
2. The "Bump-pointer arena for chain links and pairs" section —
   why we don't `malloc` per op.
3. The "Chain link / packet (flat layout)" section — the C
   realisation of the Rocq `Packet`.  Note the FULL-vs-DIFF link
   distinction (the DIFF optimisation, ADR-0013).
4. The "make_small" section — the bottom of the cascade.
5. The "green_of_red" section — the three Viennot cases, exactly
   mirroring `OpsKT.v`'s `green_of_red`.
6. The "Public push / inject / pop / eject" section — the four
   user-facing ops.  Each is naive-update + maybe-`green_of_red`.

You can skip the compaction sections, the regions API, and the
debug helpers on first read.

## Stop 6 — The cross-checks (10 min, optional)

If you care that the C and OCaml *agree*:

- [`c/tests/diff_workload.c`](../../c/tests/diff_workload.c) and
  [`ocaml/extracted/diff_workload.ml`](../../ocaml/extracted/diff_workload.ml)
  — paired drivers that consume the same xorshift64-driven workload
  trace and assert the resulting deques flatten to identical lists.
- [`bench/adversarial.sh`](../../bench/adversarial.sh) — the
  empirical confirmation that KT/Vi/C are flat (WC O(1)) while D4
  rises (amortised O(log n)).

## Where to look next

If you want to extend / modify the codebase:

- **Add a public OCaml API alternative to `kt2`/`kt4`**: see
  ADR-0001 and the headers of `OpsKT.v` and `kTDeque.mli`.
- **Optimise the C runtime**: the C perf phases are documented in
  `c/src/ktdeque_dequeptr.c` (search for "Phase L" / "Phase N" /
  "Phase P" / etc., each commented in-place).
- **Close a remaining proof obligation**: see `OpsKTRegular.v`'s
  Status section.  The full preservation theorems are stated but
  not yet proved.
- **Rewrite the C in another language**: the Rust port is at
  `rust/`, work in progress.

## Where this document fits

This file is a *path*, not a spec.  The authoritative architectural
description is [`overview.md`](overview.md) (module shape, dependency
graph).  The authoritative algorithm description is
[`../spec/why-bounded-cascade.md`](../spec/why-bounded-cascade.md).
This file just tells you the order in which to read them.
