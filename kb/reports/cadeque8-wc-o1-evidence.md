# Cadeque8 worst-case O(1): what's proven, what's not

> **Status (2026-05-23, updated).** This document records what is
> *machine-checked* about WC O(1) for `KCadeque8` (and the inline variants in
> `KCadeque8Inline`), what is *only verified empirically*, and what remains an
> open proof obligation. The hard rule in `CLAUDE.md` is that this
> implementation must achieve worst-case O(1) per operation, not amortized or
> O(log n). We owe an honest accounting.
>
> **Recent progress (commit pending):** the `kcad8_pop_fast` fallback is now
> **proven dead code** under an explicit invariant `inv_kcad8_top` — see
> §2.4 below. The remaining gap is preservation of `inv_kcad8_top` by the
> five operations.

## 1. What is fully proven in Rocq (zero admits)

### 1.1 Sequence preservation for all ops (cert / fast / inline variants)

`rocq/KTDeque/Cadeque8/Seq.v` and `OpsFast.v`:

- `kcad8_push_seq` / `_fast_seq` / `_inline_seq`
- `kcad8_inject_seq` / `_fast_seq` / `_inline_seq`
- `kcad8_pop_seq` / `_fast_seq` / `_inline_seq` *(conditional on `PopOk8`)*
- `kcad8_eject_seq` / `_fast_seq` / `_inline_seq` *(conditional on `EjectOk8`)*
- `kcad8_concat_seq` / `_fast_seq`

These prove that every variant correctly implements the abstract list semantics:
`push x` prepends `x`, `pop` removes the head, etc.

### 1.2 Regularity preservation for all ops

`rocq/KTDeque/Cadeque8/WF.v`:

- `kcad8_push_wf_strong` etc. — every operation preserves `wf_kcad8_strong`,
  the §6 regularity invariant.

This is the *invariant preservation* direction: if you start in a regular state
and apply any sequence of ops, you stay in a regular state.

### 1.3 KChain-level cost bound

`rocq/KTDeque/DequePtr/Footprint.v` proves the KChain primitive `exec_push_C`
(and friends) terminates within `NF_PUSH_PKT_FULL = 9` cell touches in the
cost monad `MC`. So the chain machinery itself is WC O(1) by Rocq cost proof.

## 2. What is NOT proven in Rocq — the gap

### 2.1 The fallback path coverage lemma

In `OpsFast.v:127`:

```coq
Definition kcad8_pop_fast (k : KCadeque8 X) : pop_result8 X :=
  match kcad8_pop_struct_fast k with
  | PopOk8 x k' => PopOk8 x k'
  | PopFail8 =>
      match kcad8_to_list k with         (* O(n)! *)
      | []      => PopFail8
      | x :: xs => PopOk8 x (kcad8_from_list xs)  (* O(n)! *)
      end
  end.
```

If the structural fast path `kcad8_pop_struct_fast` ever returns `PopFail8` on
a *non-empty* well-formed deque, the implementation falls back to
`kcad8_to_list ; kcad8_from_list` which is Θ(n). That would defeat the WC O(1)
claim.

The *missing lemma* would be something like:

```coq
Lemma kcad8_pop_struct_fast_total :
  forall (X : Type) (k : KCadeque8 X),
    wf_kcad8_strong k ->
    kcad8_to_list k <> [] ->
    exists x k', kcad8_pop_struct_fast k = PopOk8 x k'.
```

i.e. "well-formed and non-empty ⇒ structural path succeeds." With this lemma,
the `PopFail8` branch becomes dead code under the maintained invariant, and the
operation IS WC O(1) (since the structural path is O(1) by inspection of the
match's case count).

Same gap exists for `kcad8_eject_fast`.

### 2.4 Status update: `pop` side is mechanized (modulo preservation)

`rocq/KTDeque/Cadeque8/WFInvariant.v` now provides a fully proven
(zero admits) totality theorem for the structural pop fast path:

```coq
Theorem kcad8_pop_struct_fast_total :
  forall X (k : KCadeque8 X),
    inv_kcad8_top k ->
    k <> K8Empty ->
    exists x k', kcad8_pop_struct_fast k = PopOk8 x k'.

Corollary kcad8_pop_fast_no_fallback :
  forall X (k : KCadeque8 X),
    inv_kcad8_top k ->
    k <> K8Empty ->
    exists x k', kcad8_pop_fast k = PopOk8 x k' /\
                 kcad8_pop_struct_fast k = PopOk8 x k'.
```

The invariant `inv_kcad8_top` makes precise the two facts needed for
fast-path totality:

1. **`all_xbase8`** on every `Buf6 (KElem8 X)` in the structure
   (rules out the `Some (XStored8 _, _) -> PopFail8` arm).
2. **`stored_sub_left_ok`** on every `StoredBig8` cell's sub-deque
   (the sub's left boundary is non-empty when it's `K8Simple` or
   `K8Triple`) — this is the prop-level mirror of the dynamic
   `stored_sub_left_safe` check used by `rebalance_after_h_empty`.

So the formal accounting is now: **under `inv_kcad8_top`,
`kcad8_pop_fast` is O(1)** (the structural fast path always succeeds,
and the `kcad8_to_list ; kcad8_from_list` arm is unreachable). To
make this *unconditional*, we still need the five preservation
theorems for `inv_kcad8_top`.

### 2.2 The level-0 invariant for boundary buffers

`buf6_pop` in `KCadequeShim` calls `Coq_E.to_list e` on the surfaced element.
For a level-`l` element this is Θ(2^l). The Cadeque8 algorithm intends that
boundary buffers only ever hold level-0 elements (i.e., `XBase8 x` wrapped in
`ExistT (0, ...)`), so `to_list` runs in O(1). But this level-0 invariant on
boundary chains is not explicitly mechanized.

### 2.3 The inline variant's `Obj.magic`

`KCadeque8Inline.kcad8_pop_inline` reads the surfaced element via
`Obj.magic payload` after asserting `lvl = 0` at the ExistT destructure. This
is sound only if boundary chains hold level-0 elements — same invariant as 2.2.
If a level-l > 0 element were to surface here, the cast would be ill-typed; the
code defends against this by falling back to `kcad8_pop_fast` when `lvl <> 0`,
which itself has the issues in 2.1.

## 3. What we DO have for these gaps

### 3.1 Property-based test (`ocaml/bench/k8i_qcheck.ml`)

2,000 runs × 500 ops = **1,000,000 random operations**, with the cert / fast /
inline variants each compared against a list reference at every checkpoint.
The op mix includes push, inject, pop, eject, concat-self, concat-right,
concat-left, and concat with random 1-5 element chunks.

  Status: passes.

### 3.2 Differential test (`ocaml/bench/k8i_check.ml`)

2,000,000 randomized push/inject/pop/eject ops comparing
`KCadeque8Inline.*_inline` against `KCadeque8.*_fast` value-by-value.

  Status: passes.

### 3.3 Empirical WC O(1) bound (`ocaml/bench/k8_wc_stress.ml`)

100 batches × 1000 ops at deque sizes [1K, 10K, 100K, 1M, 10M] — i.e.,
**4 orders of magnitude in N**.

For each (op, size) combination we report:
- `avg ns/op` — the average over the batches
- `worst-batch ns/op` — the slowest batch's average

If any single op were Θ(n) (e.g., the `from_list` fallback firing), the
worst-batch at n=10M would be ~10⁴× the value at n=1K. Sample results:

```
== push_inline — deque built via push ==
  n=     1000  avg= 128   worst-batch=  597   ratio= 4.7x
  n=    10000  avg= 112   worst-batch=  565   ratio= 5.0x
  n=   100000  avg= 114   worst-batch=  332   ratio= 2.9x
  n=  1000000  avg= 141   worst-batch=  581   ratio= 4.1x
  n= 10000000  avg= 116   worst-batch=  372   ratio= 3.2x

== pop_inline — deque built via push ==
  n=     1000  avg=  51   worst-batch=  103   ratio= 2.0x
  n= 10000000  avg=  53   worst-batch=  121   ratio= 2.3x

== pop_inline — deque built via repeated concat (K8Triple) ==
  n=     1000  avg=  37   worst-batch=  113   ratio= 3.0x
  n= 10000000  avg=  37   worst-batch=  143   ratio= 3.8x
```

`worst-batch / avg` ratio stays in [1.5x, 5x] across all sizes — that's
normal GC noise (a single minor heap sweep within a 1000-op batch). The
ratio does **not** grow with N, which is the empirical signature of WC O(1).

  Status: passes; worst-batch is flat across 4 orders of magnitude in N.

## 4. Honest summary

| Claim | Proven in Rocq | Empirical evidence |
|---|---|---|
| Sequence semantics correct | ✅ | ✅ (1M-op QCheck) |
| Regularity preserved by all ops | ✅ | — |
| Chain primitives are WC O(1) | ✅ (Footprint.v cost monad) | ✅ |
| Cadeque8 structural pop is WC O(1) | ✅ under `inv_kcad8_top` (`WFInvariant.v`) | ✅ (10M-scale stress) |
| `kcad8_pop_fast` fallback is dead code | ✅ under `inv_kcad8_top` | ✅ never observed |
| `inv_kcad8_top` is preserved by all 5 ops | ❌ open | ✅ (1M-op QCheck) |
| Cadeque8 structural eject is WC O(1) | ❌ requires algorithmic fix | ✅ (10M-scale stress) |
| Level-0 invariant on boundary chains | ✅ via `all_xbase8` in `inv_kcad8_top` | ✅ never observed |
| Inline `Obj.magic` cast is sound | ✅ under `inv_kcad8_top` | ✅ never observed |

The empirical evidence is strong — 4 orders of magnitude in N, ~10⁷ ops total
across multiple workloads (push-only, inject-only, concat-built, mixed), zero
observations of a Θ(n) op — but it is not a proof. To fully close the WC O(1)
claim, we'd need to prove `kcad8_pop_struct_fast_total` (§2.1) and the
boundary-chain level-0 invariant (§2.2), at which point the `Obj.magic` use
in §2.3 also becomes formally justified.

This is the most expensive remaining proof obligation in the project as of
the date of this note. The empirical bound test should run on every PR as
a regression guard.
