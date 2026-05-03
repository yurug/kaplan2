---
id: error-handling
domain: conventions
related: [code-style, error-taxonomy, api-contracts]
---

# Error Handling

## One-liner
Conventions for partial functions, the heap monad, dead branches, and what we do/don't expose to the user.

## Scope
Covers: `option` vs. `M (option ...)`, dead-branch discharge, heap-monad failure semantics. Does NOT cover: the catalog of error classes (see `spec/error-taxonomy.md`) or runtime exceptions in OCaml (we don't use them).

## Public partiality

The only kind of partiality the public API exposes is "empty deque" → `None`. Implemented as `option (A * t A)` for `pop`/`eject`. No exceptions, no panics, no `Inductive Error := …`.

```rocq
Definition pop {A} (q : t A) : option (A * t A) := ... .

Theorem pop_seq : forall A (q : t A) x q',
  pop q = Some (x, q') → to_list q = x :: to_list q'.
Theorem pop_empty : forall A (q : t A), pop q = None ↔ to_list q = [].
```

## Internal partiality

Internal helpers (e.g., `buf_pop`, `buf_take_first2`) may return `option` when their precondition is statically un-enforced. Callers must verify the precondition before calling.

```rocq
Definition buf_pop {X} (b : Buf5 X) : option (X * Buf5 X).
(* Precondition: buf_size b > 0. *)
Lemma buf_pop_some : forall X (b : Buf5 X),
  buf_size b > 0 → exists x b', buf_pop b = Some (x, b').
```

Where the precondition is statically captured by a Coq type (e.g., `B3 a b c` clearly has size 3), the helper is total and returns its result directly without wrapping in `option`.

## The heap monad

`Common/Monad.v` defines:

```rocq
Definition M (X : Type) := Heap → option (Heap × X).
```

Bind:

```rocq
Definition bind {X Y} (m : M X) (f : X → M Y) : M Y :=
  fun H => match m H with
           | None => None
           | Some (H', x) => f x H'
           end.
Notation "let* x := m 'in' rest" := (bind m (fun x => rest)).
```

Atoms:
- `ret : X → M X` — never fails.
- `fail : M X` — `Some H => None`. Used **only** for un-recoverable internal preconditions.
- `alloc : Cell → M Loc` — never fails.
- `read  : Loc → M Cell` — fails if `Loc ∉ dom H`.

`fail` should be unreachable in well-formed code. The refinement theorems prove that `exec_op H args = Some (...)` for every input satisfying `repr*`.

## Dead branches

When a `match` has cases that are dead by virtue of the surrounding context (e.g., a `B0` case in a function whose argument has type `Buf5 X` with size ≥ 2):

- prefer to **eliminate them by typing**: change the input to `{ b : Buf5 X | size b ≥ 2 }` or use a more refined inductive.
- if elimination is impractical, **discharge them in code** with `(* dead: precondition guarantees size ≥ 2 *)` and a `False_rect`-style proof in the body (or `match _ in <eq>` trick).

```rocq
Definition buf_take_first2 {X} (b : Buf5 X) (h : buf_size b >= 2) : (X * X * Buf5 X) :=
  match b with
  | B2 a b' => (a, b', empty_buf)        (* size 2 *)
  | B3 a b' c => (a, b', B1 c)            (* size 3 *)
  | …
  | B0 | B1 _ => False_rect _ (size_lt_2 _ h)
  end.
```

(VWGP §3.2 illustrate this style with `green_push`. We don't follow their *intrinsic* style, but the dead-branch discharge pattern is the same.)

## When to use `option` vs. dependent types

| Situation                                                          | Use            |
|--------------------------------------------------------------------|-----------------|
| Public API empty failure                                            | `option`         |
| Internal helper, precondition statically captured by type           | direct return   |
| Internal helper, precondition is a `Prop`                           | `{x : T | P x}` or extra argument |
| Heap operation that may legitimately fail (e.g., bad `Loc`)         | `M (option …)` (rare) |

We **avoid** wrapping every helper in `option` defensively. Trust the type discipline.

## Logging / tracing

We do **not** log inside Rocq code. OCaml drivers may log discrepancies during fuzzing.

## Agent notes
> If you ever see yourself adding an `Error` ADT to the public API, stop. The §22 acceptance theorems are stated in terms of `option`, sequences, and refinement; introducing extra error types breaks them.
> A `fail` in the heap monad that the caller can't statically rule out is a design smell. Either tighten the type, or add a precondition on the call site.

## Related files
- `code-style.md` — naming and idioms.
- `../spec/error-taxonomy.md` — full enumeration of error classes.
- `../spec/api-contracts.md` — public failure semantics.
