---
id: code-style
domain: conventions
related: [error-handling, proof-style, testing-strategy]
---

# Code Style

## One-liner
Naming, layout, comment, and idiom conventions for `rocq/KTDeque/` sources.

## Scope
Covers: file structure, naming, header comments, comment density, function/file size budgets, when to use sections vs. modules. Does NOT cover: proof tactic style (see `proof-style.md`) or testing (see `testing-strategy.md`).

## File header

Every `.v` file begins with a Coq comment block of this shape:

```coq
(** * Module: <Path/Name> -- <one-line purpose>

    This module is responsible for <what + why>.
    It implements §<manual section>: <topic>.

    Key design decisions:
    - <decision 1, with adr-XXXX reference>
    - <decision 2>

    Cross-references:
    - kb/spec/<file>#<id>
    - kb/properties/<file>#<P-entry>
*)
```

Manual section references use `§` (Unicode). ADR references use `ADR-NNNN`. Property references use `P<N>`, `NF<N>`, `T<N>`.

## Naming

| What                   | Style                                                   | Example                                  |
|------------------------|---------------------------------------------------------|------------------------------------------|
| File                    | `PascalCase.v`                                          | `Footprint.v`, `OpsAbstract.v`           |
| Directory               | `PascalCase`                                            | `DequePtr/`                              |
| Module type             | `ALL_CAPS`                                              | `REGULAR_PACKET_DEQUE`                   |
| Inductive type          | `PascalCase`                                            | `Color3`, `Buf5`, `Packet`               |
| Constructor             | `PascalCase`                                            | `Green3`, `B3`, `PNode`                  |
| Record / sigma type     | `PascalCase`                                            | `PCell`, `Heap`                          |
| Definition / function   | `snake_case`                                            | `buf_size`, `chain_to_list`, `push_chain` |
| Lemma / Theorem         | `<P-or-T-or-name>_<subject>_<property>`                 | `push_chain_seq`, `push_chain_full_regular` |
| Variable / parameter    | `snake_case` (preferred) or short letters where idiomatic | `H`, `H'`, `r`, `cell`, `child_loc`     |
| Module                  | `PascalCase`                                            | `DequePtr`                               |

`Theorem` is reserved for top-level public results; everything else is a `Lemma`.

## Section / module structure

- **Use `Section`** within a file when several declarations share the same `Variable` / `Hypothesis`.
- **Use `Module`** to namespace; do not nest more than two levels.
- **Open / Close** with `Section <name>. ... End <name>.` (matching). No anonymous sections.

## Implicit arguments

`Set Implicit Arguments.` at the top of each file. Use `@<name>` to disambiguate when needed.

## Function size

≤ 30 non-blank, non-comment lines per function (NF8). Exceptions:
- Mutual-recursion blocks: count as one definition, exempt.
- Repair-case proofs that are inherently long: split via `Lemma` decomposition, not by inflating the definition.

## File size

≤ 200 non-blank, non-comment lines per file (NF8). Exceptions:
- A mutual `Inductive ... with ...` block that spans multiple types may exceed 200.

When a file approaches 200 lines, split by topic or by property cluster.

## Comments

- ≥ 40% comment ratio in `Common/`, `DequePtr/` (NF7).
- Every public function has a `(** ... *)` doc comment with: purpose, params, return, invariants enforced (`@invariant P<N>`), and at least one example for non-trivial functions.
- Every conditional has a one-line comment explaining *why* (not *what*).
- Every magic value has a comment naming the manual section that justifies it. Better: replace with a `Params.v` constant.
- Comments explain *intent*; identifier names explain *meaning*. Never restate what the code says.

## Idioms

- Prefer `match` over nested `if`. Use `match` even for `option` (`match opt with | Some x => ... | None => ...`).
- Pattern destructuring in arguments where it clarifies (`fun '(a, b) => …`).
- Heap-monad code: bind via `let* x := op in ...` (notation defined in `Common/Monad.v`).
- For sequence proofs: use `simpl; rewrite_strat (innermost <eq>); reflexivity` patterns; don't `unfold` aggressively.
- Use `assert (H : ...)` for intermediate facts before `apply`.

## Anti-patterns

- ❌ `intuition.` followed by `congruence.` — opaque; use targeted tactics.
- ❌ `auto with *` — depends on global hint state; prefer specific hint dbs.
- ❌ One-line proofs in critical lemmas without an accompanying comment.
- ❌ `Admitted.` — forbidden in core (NF4).
- ❌ Deep mutual recursion across files — forces compile-time entanglement.
- ❌ Re-stating what the code does in a comment.
- ❌ Re-deriving constants that live in `Params.v` (NF9).

## Agent notes
> When you write a new file, first write the header block, the `Section` skeleton with comments, and only then fill in `Inductive` / `Definition` / `Lemma`. The structure forces you to think in chunks small enough to comment thoroughly.
> If you find yourself writing the same proof twice (e.g., a left-and-right pair), STOP and refactor through `Common/Symmetry.v` (ADR-0006).

## Related files
- `error-handling.md` — option-typed failures.
- `proof-style.md` — tactic conventions.
- `testing-strategy.md` — test naming.
- `../architecture/decisions/adr-0004-rocq-encoding-style.md` — global stylistic stance.
