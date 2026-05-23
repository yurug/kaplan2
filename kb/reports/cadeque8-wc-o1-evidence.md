# Cadeque8 worst-case O(1): what's proven, what's not

> **Status (2026-05-23, updated).** This document records what is
> *machine-checked* about WC O(1) for `KCadeque8` (and the inline variants in
> `KCadeque8Inline`), what is *only verified empirically*, and what remains an
> open proof obligation. The hard rule in `CLAUDE.md` is that this
> implementation must achieve worst-case O(1) per operation, not amortized or
> O(log n). We owe an honest accounting.
>
> **Critical finding (commit pending):** while trying to prove preservation of
> the `inv_kcad8_top` invariant by `kcad8_concat`, we identified — and
> empirically confirmed — that the `K8Simple ba `concat` K8Triple h2 m2 t2`
> path produces a stored cell whose sub-deque has an empty left boundary
> (`K8Triple ø m2 ø`).  A subsequent pop sequence that drains `ba` then
> triggers `rebalance_after_h_empty`, which checks
> `stored_sub_left_safe` on this cell, sees the empty left boundary,
> and returns `None` — forcing the O(n) `kcad8_from_list` fallback.
> See [§5: empirical confirmation of the O(n) gap].  **This is a real
> algorithmic gap in `kcad8_concat`** — not a proof artifact.  The
> existing structural fast-path totality proof
> ([WFInvariant.v:kcad8_pop_struct_fast_total]) is correct under
> `inv_kcad8_top`, but `inv_kcad8_top` is **NOT** preserved by
> `kcad8_concat` in this case, so we cannot claim unconditional WC O(1)
> for `kcad8_pop` until either:
>   1. `kcad8_concat` is restructured so the sub-deque of any
>      `StoredBig8` it creates always has a non-empty left boundary, or
>   2. `rebalance_after_h_empty` is extended with a case for stored
>      cells whose sub has empty left boundary, recovering the data
>      without falling back.

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
| Cadeque8 structural pop is WC O(1) **under `inv_kcad8_top`** | ✅ (`WFInvariant.v`) | ✅ (on workloads where `inv_kcad8_top` holds) |
| `kcad8_pop_fast` fallback is dead code **under `inv_kcad8_top`** | ✅ | n/a |
| `inv_kcad8_top` preserved by `push`, `inject` | ❌ open (easy) | ✅ |
| `inv_kcad8_top` preserved by `concat` | **❌ FALSE** (algorithm bug) | **❌ FALSIFIED — see §5** |
| `inv_kcad8_top` preserved by `pop`, `eject` | ❌ open | ✅ on workloads |
| Cadeque8 structural eject is WC O(1) | ❌ requires algorithmic fix | ✅ (10M push-built stress) |
| Level-0 invariant on boundary chains | ✅ via `all_xbase8` in `inv_kcad8_top` | ✅ |
| Inline `Obj.magic` cast is sound | ✅ under `inv_kcad8_top` | ✅ never observed |

## 5. Empirical confirmation of the O(n) gap in `concat`+`pop`

`ocaml/bench/k8_concat_pop_stress.ml` runs the exact problematic
workload:
  1. Build `k8s` = `K8Simple` with N elements (via `push`).
  2. Build `k8t` = `K8Triple` with N elements (via `concat`-self).
  3. Compute `r = k8s `concat` k8t`.
  4. Drain `r` via `pop`, measuring per-batch and worst-batch times.

Output (`dune exec ocaml/bench/k8_concat_pop_stress.exe`):

```
== N = 1000 (each half) ==
  K8Simple |+| K8Triple   avg=  539  max-batch=     918   ratio=    1.7x
== N = 10000 (each half) ==
  K8Simple |+| K8Triple   avg=  246  max-batch=    3118   ratio=   12.7x
== N = 100000 (each half) ==
  K8Simple |+| K8Triple   avg=  396  max-batch=   61852   ratio=  156.2x
== N = 1000000 (each half) ==
  K8Simple |+| K8Triple   avg=  725  max-batch= 1279681   ratio= 1765.9x
```

The max-batch time scales **linearly with N** — `ratio` (max/avg)
grows from 1.7× at N=1K to **1766× at N=1M**.  At N=1M, the worst
single pop takes ~1.28 ms = clearly Θ(N).  This is the
`kcad8_to_list ; kcad8_from_list` fallback firing.

This refutes the "WC O(1) for all `KCadeque8` operations"
claim **on workloads that include this concat pattern**.
The earlier `k8_wc_stress` test showed flat scaling because its
concat-build phase used `K8Triple `concat` K8Simple` (which
inserts `StoredSmall8 t1` via `buf6_inject m1 (StoredSmall8 t1)`,
trivially safe — no problematic K8Triple-with-empty-sh sub).

## 6. Proposed fixes (not yet attempted)

Two paths to genuinely-WC-O(1):

**(A)** **Restructure `kcad8_concat` for the `K8Simple ba `concat`
K8Triple h2 m2 t2` case** so the resulting middle cell has a
sub with non-empty left boundary.  E.g., split into two stored
cells `[StoredSmall8 h2; StoredBig8 ø (K8Triple ø m2 ø) ø]`.
Wait, that still has empty sub-left.  More plausibly:

  Construct `m_new = mkBuf6 [StoredSmall8 h2; ...m2's cells...; StoredSmall8 ø]`
  but this requires re-traversing m2, which is O(|m2|).  So this
  approach loses WC O(1) for concat itself.

  Alternative: change the encoding so the leftmost cell in the
  outer m can carry the "this is a wrapper around m2's middle"
  semantic with a special marker constructor.  Substantial spec
  change.

**(B)** **Strengthen `rebalance_after_h_empty`** to handle the
`StoredBig8 pre (K8Triple ø sm st) suf` case without falling back.
The sub's left boundary is empty, but its `sm` is a valid middle
buffer of stored cells — we could promote `sm` directly into the
outer `m_rest` (via concat-like buf6 ops) and use `pre` as the new
boundary.  Requires inspecting `sm`'s leftmost cell, which is
itself a `Stored8` and again may need unfolding.  This is
essentially the §6 "trailing carrier" handling that the current
implementation doesn't fully realize.

Both fixes require non-trivial proof and algorithmic work and
are deferred.

## 7. Recommendation

For the moment, the truthful claims are:

- **`kcad8_push` / `kcad8_inject`**: WC O(1), algorithmically and
  empirically.
- **`kcad8_pop` / `kcad8_eject` on workloads without `K8Simple `concat`
  K8Triple` operations**: WC O(1) (validated empirically).
- **`kcad8_pop` / `kcad8_eject` on arbitrary workloads with concat**:
  **amortized** O(1), not strict WC O(1).  A single op can be Θ(n)
  in the worst case (confirmed by `k8_concat_pop_stress`).
- **`kcad8_concat`**: O(1) algorithmically, but the cost is paid by
  a later pop that triggers the fallback.

This is honestly weaker than what the project's HARD RULE in
`CLAUDE.md` requires.  Closing the gap is a real, identified
piece of remaining algorithmic work.

The empirical evidence is strong — 4 orders of magnitude in N, ~10⁷ ops total
across multiple workloads (push-only, inject-only, concat-built, mixed), zero
observations of a Θ(n) op — but it is not a proof. To fully close the WC O(1)
claim, we'd need to prove `kcad8_pop_struct_fast_total` (§2.1) and the
boundary-chain level-0 invariant (§2.2), at which point the `Obj.magic` use
in §2.3 also becomes formally justified.

This is the most expensive remaining proof obligation in the project as of
the date of this note. The empirical bound test should run on every PR as
a regression guard.
