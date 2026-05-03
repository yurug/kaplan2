---
id: proof-style
domain: conventions
related: [code-style, testing-strategy]
---

# Proof Style

## One-liner
Tactic conventions, proof structure, and rules for keeping proofs maintainable in plain Ltac without Equations/Hammer.

## Scope
Covers: tactic preferences, proof structure, hint database policy, naming of intermediate lemmas, formatting. Does NOT cover: code style (see `code-style.md`) or test counting (see `testing-strategy.md`).

## Tactic family

We use **plain Ltac** (not Ltac2, not ssreflect). Rationale: matches manual style; no extra plugin.

## Preferred tactics

For most routine work, prefer in this order:

1. `intros …; …` — name hypotheses immediately. Use `intros [a [b c] | x]` patterns to destructure.
2. `induction …` / `destruct …` — explicit structural cases.
3. `simpl in …` / `cbn` — controlled unfolding.
4. `rewrite …` — directional rewriting; specify direction (`rewrite ->` / `rewrite <-`) for clarity.
5. `apply …` / `eapply …` — over `auto` for traceability.
6. `lia` — closed Presburger arithmetic on `nat`/`Z`.
7. `discriminate` / `congruence` — boolean / equational closure on small contexts.
8. `inversion …` — for relations / contradictions; close immediately with `subst`.
9. `reflexivity` — when the goal is a definitional equality.

Only after these have failed:

- `auto with <db>` — with a *specific* hint database, never `*`.
- `eauto` — when `auto` is too weak; add a depth bound (`eauto 5`).
- Custom Ltac scripts in `Common/Tactics.v` — for repetitive patterns. Document each.

## Anti-patterns

- ❌ `auto with *` — depends on global state; brittle.
- ❌ `intuition` outside trivial subcases.
- ❌ `crush` (not available; mentioning it because some external libs ship it).
- ❌ `omega` — deprecated alias for `lia`. Use `lia`.
- ❌ Long chains of `;` without intermediate `assert` — hard to debug.
- ❌ `Admitted` — never in core (NF4).

## Proof structure

```rocq
Lemma push_chain_refines : forall H r d x H' r' cost,
  chain_repr_at H r d depth →
  exec_push_pkt_C H r x = Some (H', r', cost) →
  ∃ d',
    chain_repr_at H' r' d' depth ∧
    chain_to_list d' = x :: chain_to_list d ∧
    heap_ext H H'.
Proof.
  intros H r d x H' r' cost Hrepr Hexec.
  (* §1: unfold one step of exec_push_pkt_C *)
  unfold exec_push_pkt_C in Hexec.
  destruct (lookup H r) as [c|] eqn:Hlk.
  - (* §2: r resolves to a cell c; case-split on buffer size *)
    destruct (pcell_pre c) eqn:Hpre.
    + (* size 0: ... *) ...
    + ...
  - (* §3: r unresolvable; contradicts chain_repr_at *)
    inversion Hrepr; congruence.
Qed.
```

Use **explicit bullet points** (`- + *`) for case splits. **Never** rely on goal order.

## Reusable helpers

- `Common/Tactics.v` — tactic notations like `inv H` for `inversion H; subst; clear H`.
- `Common/ListFacts.v` — list lemmas (`app_assoc` repackaging, etc.).
- `Common/HeapExt.v` — `heap_ext` lemmas plus a `heap_ext_solver` Ltac that combines `apply heap_ext_alloc; auto with heap` into one step.

Resist the urge to scatter custom tactics across files; collect them in `Common/`.

## Hint databases

Define small, focused hint databases:

| DB name      | Purpose                                              |
|--------------|------------------------------------------------------|
| `ktdeque`    | `Params.v` constants and basic arithmetic facts.     |
| `seq`        | `chain_to_list`, `packet_seq`, `buf_seq` simplification rules. |
| `heap`       | `heap_ext` reflexivity / transitivity / alloc lemmas. |
| `regularity` | Color predicates and structural lemmas.               |

Use `auto with seq heap` rather than `auto`. Hints come from explicit `Hint Resolve` or `Hint Rewrite` lines, never `Hint Constructors`.

## Lemma sizing

A lemma whose proof exceeds ~30 lines should be either:
- decomposed into 2–3 helper lemmas (preferred), or
- refactored to use a stronger induction principle, or
- accompanied by inline section comments (`(* §A: induct on l *)`, `(* §B: case n=0 *)`).

A lemma whose proof exceeds ~60 lines triggers a "consider splitting" warning at audit time.

## Naming

Lemma names lead with the property they establish:

- `P22_repair_caseA_seq` — proves P22 for Case A.
- `P28_heap_ext_chain_repr` — heap-ext preserves `chain_repr_at`.
- `push_chain_refines` — refinement theorem (no P-prefix because it's already named in the manual).
- `push_chain_seq` — purely-abstract sequence lemma.

When a lemma is a building block, prefix `aux_`. When it's structural / about the heap, prefix `mem_` / `dom_` / `repr_`.

## Pencil-paper proofs

For repair-case proofs, write the multi-step proof outline as comments
before the Coq proof:

```coq
Lemma make_red_push_chain_seq : ...
Proof.
  (* Plan:
     1) sequence preservation by chain_to_list;
     2) regularity restored;
     3) inner packet adjusted;
     4) heap_ext preserved.
  *)
  intros …
  ...
Qed.
```

This makes the structure auditable even when the tactic body is dense.

## Agent notes
> Strive for proofs that read like the corresponding pencil-and-paper argument. If a tactic block doesn't map to a sentence in the proof outline, it's probably ad hoc and brittle.
> Whenever you find yourself copy-pasting a 5+ line tactic across two lemmas, lift it into `Common/Tactics.v`.

## Related files
- `code-style.md` — file/function-level conventions.
- `testing-strategy.md` — how proof obligations relate to test coverage.
- `../runbooks/audit-checklist.md` — proof audit gate.
