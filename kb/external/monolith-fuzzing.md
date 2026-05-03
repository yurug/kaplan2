---
id: monolith-fuzzing
domain: external
related: [rocq-toolchain, ocaml-extraction, non-functional-properties]
---

# Monolith fuzzing — Runtime Behavior

## One-liner
François Pottier's `Monolith` library validates the OCaml side of the development by random model-based testing against a list reference.

## Scope
Covers: install, harness wiring, scenario generation semantics, expected output, what to do on a discrepancy. Does NOT cover: the data structure itself.

## What Monolith is

`Monolith` (`opam install monolith`) is a property-based / model-based fuzz testing library by F. Pottier ([Pot21], [gitlab.inria.fr/fpottier/monolith](https://gitlab.inria.fr/fpottier/monolith)). It:
- Generates random scenarios consisting of sequences of operations.
- Runs each scenario against a *candidate* implementation and a *reference* implementation.
- Reports a discrepancy with a reproducible scenario when the two diverge.

Used by VWGP to validate their hand-written OCaml deques against a list reference; **no discrepancy was ever found**. We re-use the same harness pattern.

## Install

```bash
opam install -y monolith
opam install -y parallel    # if using `make test` with parallelism
```

## Harness layout (mirrors VWGP `test_monolith/`)

```text
ocaml/test_monolith/
├── reference.ml        # list-based ground truth
├── candidate.ml        # KTDeque (extracted or hand-written)
├── spec.ml             # operation specs (push, pop, inject, eject)
├── support/dune
└── dune
```

`spec.ml` declares each operation's input/output types in Monolith's combinator language. `reference.ml` and `candidate.ml` provide concrete implementations matching the same signature.

## Reference implementation

```ocaml
type 'a t = 'a list
let empty = []
let is_empty = function [] -> true | _ -> false
let push x xs = x :: xs
let pop = function [] -> None | x :: xs -> Some (x, xs)
let inject xs x = xs @ [x]
let eject xs =
  match List.rev xs with [] -> None | x :: rs -> Some (List.rev rs, x)
let concat a b = a @ b
let to_list xs = xs
```

This is `O(n)`; we don't care, it is the spec.

## Candidate implementation

The candidate is **hand-written OCaml** in `ocaml/lib/`, mirroring VWGP's split. The extracted code can also be fuzzed to confirm extraction soundness (ADR-0005).

## Scenario generation

Monolith's combinators let us specify:
- Distribution over operations (we lower `concat` weight per VWGP §9.1).
- How long sequences should grow before being shrunken / discarded.
- Diversity of operands (multiple deques in flight at once, exercising persistence).

A modest scenario length of 100 operations per trial, with 50 trials per "size group" 0..40, matches VWGP's benchmark setup.

## Expected output

Successful fuzzing prints periodic "OK" indicators. On discrepancy, Monolith prints a *minimized* sequence of operations whose results diverge between reference and candidate.

## What to do on discrepancy

1. Capture the printed scenario.
2. Reproduce the discrepancy in a failing OCaml test case.
3. **DO NOT patch the OCaml code only.** Trace back to whether the bug is in:
   (a) the hand-written OCaml — fix, retest;
   (b) the extracted code (if fuzzing extracted) — examine the Rocq source; usually reveals a missing case in a `match` or wrong order in a transfer.
4. If the bug exists in the Rocq source, write a *Rocq-level test* (`Example` with concrete inputs from the scenario) before patching, so the regression is captured as a property.

## Lazy-loading / pagination / rate limits / batching

| Category    | Notes                                                                |
|-------------|----------------------------------------------------------------------|
| Lazy-loading | n/a — Monolith is a library; loads on first `Require`/`open`.       |
| Pagination  | n/a.                                                                 |
| Rate limits | n/a.                                                                 |
| Batching    | `make test parallel` uses GNU parallel to run multiple scenarios in parallel. |

## Request budget

For one fuzzing run:

| Step                                  | Cost                       |
|---------------------------------------|-----------------------------|
| Build harness                         | seconds                     |
| Run 60 s scenario                     | 60 s                        |
| Run "indefinite" with parallel        | bounded by patience         |
| Reproduction of a discrepancy         | seconds (Monolith provides minimum) |

## Architectural constraints

- **MUST** generate scenarios that exercise persistence (multiple deques in flight). Single-threaded scenarios miss bugs around shared structure.
- **MUST** keep the reference implementation tiny and obviously correct. If the reference has a bug, fuzzing is meaningless.
- **MUST NOT** assume Monolith's pseudo-randomness covers worst-case inputs. NF11 guarantees ≥ 60 s clean; for thorough validation, run for hours.
- **SHOULD** rerun fuzzing whenever a repair case changes; that's the most discrepancy-prone area.

## Agent notes
> When fuzzing surfaces a problem, the bug is almost always in a buffer-transfer rule or a repair sub-case. Look there first.
> Adding new operations to the public API requires also adding them to `reference.ml`, `spec.ml`, and `candidate.ml`. Monolith won't fuzz what isn't declared.

## Related files
- `INDEX.md` — `external/` routing.
- `ocaml-extraction.md` — when we fuzz the extracted code.
- `../properties/non-functional.md` — NF10, NF11.
- `../runbooks/audit-checklist.md` — fuzzing as part of audit.
