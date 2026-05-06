# kaplan2

> ⚠️ **Work in progress — not yet released.** APIs, file layout, and
> proof obligations may change without notice. Don't depend on this
> in downstream code yet. No semver, no versioned tags. The opam
> package `ktdeque` is buildable from a clone but not yet on
> the official opam-repository. See the [Status](#status) section
> for what's actually proven and what's still being built.

A **mechanically verified** persistent real-time deque, with faithful
ports across multiple languages and a microbenchmark suite.

This is the data structure from
[Kaplan & Tarjan, *Purely functional, real-time deques with catenation*
(JACM 1999)](https://doi.org/10.1145/324133.324139), in the modernized
encoding of
[Viennot, Wendling, Guéneau & Pottier, *Verified catenable deques*
(PLDI 2024)](https://dl.acm.org/doi/10.1145/3656430).

What makes it special: every operation — **`push`** (prepend),
**`pop`** (remove first), **`inject`** (append), **`eject`** (remove
last) — runs in **worst-case O(1)**: not amortized, not "usually
fast", not O(log n). And the whole thing is *purely functional*: you
can fork the deque, mutate one branch, and the other stays intact,
with no asymptotic penalty.

## What's in here

This repository is a **monorepo** with one self-contained tree per
language:

| Tree         | What you'll find                                                             | Build                |
| ------------ | ---------------------------------------------------------------------------- | -------------------- |
| [`rocq/`](rocq/) | Rocq 9.1 formalization: spec, abstract operations, sequence preservation. | `dune build rocq`    |
| [`ocaml/`](ocaml/) | Code extracted from Rocq, plus the benchmark harness that compares us against the original Viennot implementation. | `dune build ocaml` |
| [`c/`](c/)   | A hand-translated C port of the Rocq algorithm. Faster than Viennot's OCaml on every workload. | `cd c && make` |
| [`rust/`](rust/) | Rust port (work in progress).                                            | `cd rust && cargo build` |
| [`kb/`](kb/) | Knowledge base: design docs, ADRs, session notes, audits.                    | (text, no build)     |

## Why one tree per language?

Each tree is self-contained: it has its own README explaining how to
build, what's verified, and how it relates to the others. You can
`cd c/ && make` and never look at the Rocq code, or you can spend a
weekend in `rocq/` and ignore everything else.

The Rocq sources are the **source of truth**. The OCaml code in
`ocaml/extracted/` is generated directly from Rocq via the standard
extraction mechanism — it is not hand-edited. The C and Rust ports are
*hand-translated* and tested for behavioral equivalence with the
extracted reference; they are not extracted.

## Quick start

```sh
# Build the Rocq formalization (zero-admit invariant enforced)
make rocq

# Run the OCaml benchmarks against Viennot's reference implementation
make bench
_build/default/ocaml/bench/compare.exe

# Build and test the C port
cd c && make && ./test

# Or install the verified OCaml library locally (opam package
# ktdeque; ships only the extracted code from rocq/).
opam install .
```

The full correctness suite runs across all three layers (Rocq proofs,
QCheck on the verified extraction, and the C-side
sanitizer-and-fuzz-and-diff matrix):

```sh
dune build           # Rocq + OCaml
dune runtest         # QCheck on KTDeque (verified) and Deque4 (helper)
make check-all       # full C matrix incl. C↔OCaml differential (~45 s)
```

The two top-level benchmarks live in [`bench/`](bench/):

```sh
make bench-three-way   # C vs our OCaml vs Viennot OCaml at n=1M
make bench-canonical   # verified ktdeque vs canonical alternatives
                       # (Viennot, our handwritten, list reference)
```

Both write a Markdown report to `bench/results/` with kernel + gcc +
OCaml versions embedded for reproducibility.  See
[`bench/README.md`](bench/README.md) for the methodology.

See each tree's README for the full instructions and details.

## Status

- **Sequence preservation** (every operation produces the right list of
  elements): proved end-to-end for all four operations and three
  optimization variants. Zero admits.
- **Regularity invariant** (the colored-chain well-formedness that
  guarantees worst-case O(1)): foundation laid; preservation theorems
  in progress.
- **Performance**: the Rocq-extracted OCaml is roughly tied with
  Viennot's hand-written reference (within ~15% on every standard
  workload at n=1M), and the C port is **~1.5×–~2.9× faster than
  Viennot OCaml** on every workload at n=1M with arena compaction
  enabled.  Numbers in [`c/COMPARISON.md`](c/COMPARISON.md) and
  reproducible via `make bench-three-way`.

For details, see the per-tree READMEs and [`kb/`](kb/) for design
documents and session-by-session progress notes.

## License

MIT.
