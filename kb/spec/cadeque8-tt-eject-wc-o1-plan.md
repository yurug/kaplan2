# Cadeque8 — plan to close the (T+T) eject WC O(1) gap

> **Status:** drafted 2026-05-23, after the (S+T) pop fix (commit `71ac79f`)
> and the StoredSmall8 eject promote fix (commit `fe298c6`).  The remaining
> case — `K8Triple |+| K8Triple` followed by drain-eject — empirically
> shows Θ(n) per op (`k8_tt_concat_stress` reports avg 194 µs/op at
> N=10K, max-batch 1.94 ms; ratio 10× and growing with N).  This document
> proposes a concrete path to close it.

## 1. The problem, precisely

### 1.1 What `kcad8_concat` does in the (T+T) case

```coq
| K8Triple h1 m1 t1, K8Triple h2 m2 t2 =>
    let boundary :=
      StoredBig8 t1 (K8Triple h2 m2 (mkBuf6 [])) (mkBuf6 []) in
    let m_new := buf6_inject m1 boundary in
    K8Triple h1 m_new t2
```

The cell `boundary` injected at the right end of the new `m_new` has:

- `pre = t1` — non-empty (from `wf_kcad8_strong` of arg 1)
- `sub = K8Triple h2 m2 ø` — sub's left boundary `h2` is non-empty
  (from arg 2), but its right boundary is empty.
- `suf = ø` — empty.

### 1.2 Why eject fails on this cell

`rebalance_after_t_empty` checks `stored_sub_right_safe` on the
rightmost cell of `m`:

```coq
| StoredBig8 _ (K8Triple sh _ _) _ =>
    && (negb (buf6_is_empty sh))    (* sub.sh non-empty *)
       (negb (buf6_is_empty suf))    (* cell.suf non-empty *)
```

For our cell, `sub.sh = h2` is non-empty BUT `cell.suf = ø` is empty.
Safety = `false`, rebalance returns `None`, eject_fast falls back to
`kcad8_to_list ; kcad8_from_list` — Θ(n).

### 1.3 The information-theoretic constraint

The cell represents the data subsequence `t1 ++ h2 ++ m2` (where `m2`
is itself a buffer of stored cells, semantically a list of lists).

In a `StoredBig8 pre sub suf`, the flatten is `pre ++ flatten(sub) ++ suf`,
so the ordering forces:

- Either `sub` spans both `h2` and `m2` (which requires `K8Triple h2 m2 ø`,
  i.e. `sub.st = ø` — unsafe for eject), or
- `m2`'s content is split across multiple cells (which requires
  inspecting all of `m2` — O(|m2|), not O(1)), or
- `m2` is placed in `sub` only and `h2` goes elsewhere (but the
  ordering `t1 ++ h2 ++ m2` is wrong if `h2` follows `m2`).

The (S+T) pop fix succeeded because the symmetric pop case allows
`buf6_push (StoredSmall8 h2) m2` — `h2` goes to the FRONT of `m2`,
matching the desired ordering.  The (T+T) eject case has no symmetric
move because the "extra" data (`h2`) needs to come BETWEEN `t1` and
`m2`, not before `m2`.

## 2. Options for closing the gap

### Option A — Multi-cell encoding (rejected)

Distribute (t1, h2, m2) across two cells:

```
m_new = inject (inject m1 (StoredSmall8 t1))
               (StoredBig8 h2 (K8Triple ø m2 ø) ø)
```

The rightmost is `StoredBig8 h2 (K8Triple ø m2 ø) ø` — sub.sh = ø, sub.st = ø,
cell.suf = ø.  Still fails `stored_sub_right_safe`.  No improvement.

Verdict: **REJECTED** — doesn't change the fundamental issue.

### Option B — Borrow from `t2` to fill the empty suf

Idea: take one element from `t2`, use it as the cell's `suf`, and the
rest of `t2` becomes the result's tail.

```coq
| K8Triple h1 m1 t1, K8Triple h2 m2 t2 =>
    match buf6_pop t2 with
    | Some (x, t2_rest) when (buf6_is_empty t2_rest = false) =>
        let boundary :=
          StoredBig8 t1 (K8Triple h2 m2 ø) (mkBuf6 [x]) in
        K8Triple h1 (buf6_inject m1 boundary) t2_rest
    | _ =>
        (* t2 = singleton: fall back to old encoding or different path *)
        ...
    end
```

For `|t2| ≥ 2`:
- cell.suf = `mkBuf6 [x]` non-empty ✓
- sub = `K8Triple h2 m2 ø`: sub.sh = h2 non-empty ✓
- `stored_sub_right_safe` succeeds.

For `|t2| = 1`:
- can't borrow; need a different encoding.
- One approach: borrow from `h2` instead — symmetric to my (S+T) pop fix.
  `boundary = StoredBig8 t1 (K8Triple h2_rest m2 ø) (mkBuf6 [x])`
  where `h2 = first :: h2_rest`.  Cell.suf is the original first elt of h2.
- This requires `|h2| ≥ 2`.  If `|h2| = 1` AND `|t2| = 1`, we need yet
  another path.

**Edge case** (`|h2| = 1 AND |t2| = 1`): a very small input.  Two
options:
- **B.1** Use a different encoding when both are singletons.  Since both
  h2 and t2 contain just 1 element each, the total "extra" data being
  carried is just 2 elements + arbitrary m2.  We can encode this as:
  `m_new = inject m1 (StoredBig8 t1 (K8Triple (h2 ++ t2-merged) m2 ø) suf')`
  where suf' has a spare element... still stuck on suf'.

- **B.2** When both are singletons, fall back to a more permissive
  encoding *but* re-establish the boundary invariant by reading deeper.
  E.g. inspect h2 and t2's single elements and put them strategically.
  This is O(1) (peek at first element of each).

- **B.3** Establish a stronger algorithm-wide invariant that
  `|h2|, |t2| ≥ 2` always.  Requires changing every op that produces
  K8Triple to guarantee size ≥ 2 boundaries.

**Verdict**: this is the most promising direction.  The B.1/B.2 edge
case is irritating but tractable; B.3 is cleaner long-term but a much
bigger change.

### Option C — Add a `StoredCarrier` constructor to `Stored8`

```coq
Inductive Stored8 (X : Type) : Type :=
  | StoredSmall8   : Buf6 (KElem8 X) -> Stored8 X
  | StoredBig8     : Buf6 (KElem8 X) -> KCadeque8 X -> Buf6 (KElem8 X) -> Stored8 X
  | StoredCarrier  : Buf6 (KElem8 X) -> Buf6 (Stored8 X) -> Buf6 (KElem8 X) -> Stored8 X.
```

`StoredCarrier pre m suf` flattens to `pre ++ flatten(m) ++ suf` —
directly wraps a sub-middle buffer without going through the
`K8Triple ø m ø` indirection.

For (T+T) concat:
```
boundary = StoredCarrier t1 (* m = *) (buf6_push (StoredSmall8 h2) m2) (mkBuf6 [])
```

flatten = t1 ++ flatten(push (StoredSmall8 h2) m2) ++ ø
       = t1 ++ (h2 ++ flatten(m2)) = t1 ++ h2 ++ flatten(m2)  ✓

Define an eject-safety check for `StoredCarrier`:

```coq
| StoredCarrier pre _ suf => negb (buf6_is_empty suf)
```

Still requires suf non-empty.  And we set suf = ø in the boundary
construction.  Same problem!  Unless we set suf to something non-empty
via Option-B-style borrowing.

**Verdict**: same fundamental constraint as Option B — we still need a
non-empty suf.  Adding a new constructor doesn't help by itself; it
would need to be combined with Option B's borrowing.

### Option D — Recursive descent in `rebalance_after_t_empty`

When the rightmost cell is `StoredBig8 pre (K8Triple sh sm ø) ø`,
recursively rebalance into the structure:

```
let m_new := (* the "result middle" *) buf6_inject m_rest (StoredSmall8 pre) in
let m_new := (* + sm's cells *) ...iterate over sm... in
K8Triple h m_new sh   (* sh becomes the new tail *)
```

The "...iterate over sm..." part is O(|sm|), violating O(1).

UNLESS we keep `sm` wrapped: result middle ends with a *new* cell
that wraps sm.  But that new cell is again a `StoredCarrier`-style
indirection — back to square one.

**Verdict**: doesn't achieve O(1) without amortization.

### Option E — Stronger boundary-size invariant + structural concat

This is Option B.3 fleshed out.  Add an invariant `|h|, |t| ≥ 2` to
`wf_kcad8_strong` (or a stronger variant).  Then:

- Push, inject: trivially preserve ≥ 2 (they grow buffers).
- Pop: when boundary reaches size 1, EAGERLY rebalance to refill it
  (don't wait for it to hit 0).  Requires changing kcad8_pop_struct.
- Eject: symmetric.
- Concat: now guaranteed h2, t2 ≥ 2.  The (T+T) case can borrow safely.

This is the cleanest closure but requires touching:
- The invariant definition
- pop, eject, kcad8_pop_struct, kcad8_eject_struct (eager rebalance trigger)
- Possibly the inline ops (peek-then-skip pattern)
- All preservation theorems
- All inline-variant proofs

A multi-day refactor.

**Verdict**: this is the *correct* §6-style algorithm — KT99's original
invariants do require boundary sizes ≥ 2 (or more, for the
strict-WC version).  Our current formalization weakened the invariant
to ≥ 1, which is sufficient for sequence semantics but breaks the
strict WC O(1) guarantee at concat boundaries.

## 3. Recommended path: Option B (with B.2 fallback)

I recommend **Option B with B.2 (borrow from h2 if t2 is singleton;
edge case for both singletons handled by a small-buffer merge that
walks at most 2 elements)**.

**Why not E?**  E is the right long-term answer but requires changing
the invariant globally — every op proof needs updating.  ~3-5 days of
proof work.

**Why not C?**  Adding a constructor changes the type and forces all
matches on `Stored8` to be exhaustive across the new variant —
similar surface area to E but without solving the underlying issue.

**Why B is good enough:**
- The fix is localized to `kcad8_concat`'s (T+T) case.
- No new types, no new invariant, no global proof updates.
- The B.2 edge case is bounded: only triggered when both `h2` and `t2`
  are singletons, which is rare in practice and the per-call cost is
  still O(1).
- Sequence preservation is straightforward (one new equation).
- WF preservation needs only the (T+T) case re-proven.
- `inv_kcad8_top` preservation also becomes provable (the new cell
  satisfies `stored_sub_right_safe = true` and `stored_sub_left_safe = true`).

## 4. Step-by-step implementation plan for Option B

### Step 4.1: Define the new (T+T) concat case

```coq
(* Helpers *)
Definition buf6_size_ge_2 {X : Type} (b : Buf6 X) : bool :=
  match buf6_elems b with
  | _ :: _ :: _ => true
  | _ => false
  end.

(* (T+T) concat — three sub-cases. *)

| K8Triple h1 m1 t1, K8Triple h2 m2 t2 =>
    (* Try to borrow one element from t2's front to act as the
       boundary cell's suf, making the cell eject-safe. *)
    match buf6_pop t2 with
    | Some (x_borrow, t2_rest) =>
        if negb (buf6_is_empty t2_rest) then
          (* Case 1: |t2| ≥ 2 — borrow from t2. *)
          let boundary :=
            StoredBig8 t1 (K8Triple h2 m2 (mkBuf6 [])) (mkBuf6 [x_borrow]) in
          K8Triple h1 (buf6_inject m1 boundary) t2_rest
        else
          (* t2 was a singleton.  Try borrowing from h2 instead. *)
          match buf6_pop h2 with
          | Some (y_borrow, h2_rest) =>
              if negb (buf6_is_empty h2_rest) then
                (* Case 2: |h2| ≥ 2 (and |t2| = 1).
                   Borrow from h2's front; put y_borrow in cell.suf
                   AND keep t2's only element as new tail. *)
                let boundary :=
                  StoredBig8 t1 (K8Triple h2_rest m2 (mkBuf6 []))
                             (mkBuf6 [y_borrow]) in
                K8Triple h1 (buf6_inject m1 boundary) t2  (* t2 unchanged *)
              else
                (* Case 3: |h2| = |t2| = 1.  Both singletons.  We
                   carry h2 + m2 + t2's single elements
                   without a sub-K8Triple. *)
                (* New encoding: merge h2 and t2 into the cell's suf;
                   m2 goes in the sub as a degenerate cell. *)
                ... see Step 4.2 ...
          | None => (* h2 empty — impossible under wf *)
              kcad8_concat (* old encoding as defensive fallback *) ...
          end
    | None => (* t2 empty — impossible under wf *)
        ...
    end
```

### Step 4.2: Handle the (|h2| = |t2| = 1) edge case

Total "extra" data is `t1 ++ [y] ++ m2 ++ [x]` where y is h2's only
element and x is t2's only element.

One viable encoding:

```coq
let boundary :=
  StoredBig8 t1
             (K8Triple (mkBuf6 [y]) m2 (mkBuf6 []))
             (mkBuf6 [x]) in
K8Triple h1 (buf6_inject m1 boundary) (mkBuf6 [x])   (* WAIT — x is used twice! *)
```

That's wrong.  Let me re-think.

Actually if t2 = [x] is a singleton, we lose t2 if we borrow x.  We
need a non-empty result-t.  Options:
- Use h1 as the result-t?  No, h1 is the result's head.
- Pull the single x and have an empty result-t?  Violates wf.
- Use `mkBuf6 [last(t1)]` and shrink t1?  But then t1 needs ≥ 2.

So we also need `|t1| ≥ 2` in this nested case.  And if `|t1| = 1`
too, we're stuck.

**Alternative for the edge case**: encode the entire 4-element side
inline without a stored cell.  When `|h2|, |t2|, |t1| ≤ 1`, the
total "extra" beyond m2 is at most 3 elements (t1, h2, t2 each ≤ 1
elt).  We can:

1. Build a new `t_result` = `m_last_cell` from m2's last cell (if
   non-empty) + the 3 elements; otherwise just the 3 elements as a
   buf.  This is O(1) — peek at m2's last cell.
2. The result becomes `K8Triple h1 m1_or_combo new_t`.

Concretely: if `|h2| = |t2| = 1` (and possibly `|t1| = 1`):

```coq
(* Edge case: |h2| = |t2| = 1.
   The "extra" content is t1 ++ [y] ++ m2 ++ [x] where y, x are singletons.
   Goal: produce a wf K8Triple of this content concatenated with h1 ++ m1.

   Strategy: take m2's last stored cell (call it last_s), unfold it as
   needed, combine with [x] (t2's elt) to form the new tail.  The
   remaining m2 cells + [t1; y] go into m_new.  All in O(1) because
   we only peek at m2's last cell. *)

let boundary_left := StoredSmall8 t1 in
let boundary_right_carrier := StoredCarrier [y] m2 (mkBuf6 []) in
  ... etc ...
```

This is getting hairy.  I propose to **defer the edge case to a
documented `kcad8_from_list` fallback** within concat — only triggered
when ALL of `|t1|`, `|h2|`, `|t2|` are 1, and the cost is O(|m2|).
Empirically this is rare (requires a very specific input shape), and
we can either:
- Document it as a residual gap (still violates strict WC O(1) in this
  edge case), or
- Strengthen the invariant separately (Option E) so the case is
  unreachable.

### Step 4.3: Proof obligations

For Cases 1 and 2 of Option B:

**Sequence preservation** (Seq.v): Add a new lemma
`kcad8_concat_seq_tt_borrow` showing the new encoding flattens to
the same sequence as the old.

**WF preservation** (WF.v): Update `kcad8_concat_wf_strong` to handle
the new case.  Key facts:
- t2_rest non-empty (from the size_ge_2 check) — new result-t is wf.
- boundary cell: pre = t1 non-empty (wf arg1); sub = K8Triple h2 m2 ø with
  h2 non-empty (wf arg2), so wf_stored8 — for the wf side.
- m_new = inject m1 boundary: wf_middle from wf_middle_inject.

**`inv_kcad8_top` preservation** (WFInvariant.v, when extended): the
new boundary cell now satisfies `stored_sub_right_safe = true` AND
`stored_sub_left_safe = true` (sub.sh = h2 non-empty).  Cleanly closes
the preservation gap that motivated this entire investigation.

### Step 4.4: Mirror update to `kcad8_concat_fast` in OpsFast.v

The fast variant of concat must match.

### Step 4.5: Re-extract OCaml and re-run all tests

- `k8i_check` (2M-op differential)
- `k8i_qcheck` (1M-op cert/fast/inline + concat)
- `k8_concat_pop_stress` (already-fixed case — confirm still flat)
- `k8_concat_eject_stress` (already-fixed case — confirm still flat)
- `k8_tt_concat_stress` (the case being fixed — should now be flat)
- `k8_wc_stress` (broader workloads)

### Step 4.6: Update KB

- `kb/reports/cadeque8-wc-o1-evidence.md`: mark (T+T) as resolved with
  empirical evidence.
- This file: archive as "completed plan".

## 5. Estimated effort

- Algorithm code change: 1-2 hours (Cases 1 and 2 are mechanical;
  the edge case decision adds complexity).
- Sequence proof: 1 hour.
- WF proof: 1-2 hours.
- WFInvariant preservation: 1 hour.
- Re-extraction + test re-runs: 30 min.
- Edge case resolution decision (defer vs invariant strengthening):
  variable.

**Total estimate: 1 full session of focused work.**

## 6. Out-of-scope

The following are NOT addressed by this plan:

- **`inv_kcad8_top` preservation by `pop`/`eject`**.  These ops do a
  lot of stored-cell manipulation; proving preservation requires
  separate, similar-magnitude work.

- **The XBase8 erasure** for further perf (chasing the last column on
  push).  Orthogonal to WC O(1).

- **Cost-monad-style strict O(1) bounds in Rocq**.  Currently the WC
  O(1) claim is algorithmic-by-inspection plus empirical.  Cost-monad
  proofs would mechanize the per-op constant bound but require
  threading cost through every helper.

- **Option E (boundary size ≥ 2 invariant)**.  This is the long-term
  cleanest closure for ALL boundary-edge cases including the singleton
  problem above.  Deferred as a separate larger refactor.

## 7. Open design questions for future discussion

1. **Should we adopt Option E eventually?**  KT99's strict WC algorithm
   does require ≥ 2 element boundaries.  Our current "≥ 1" weakening
   is the root of the edge cases.  Lifting it is a 3-5 day refactor
   but yields a much cleaner formalization.

2. **Should the strict WC O(1) claim be re-stated for the
   non-pathological case?**  Even with all bugs fixed, the formal
   claim requires either invariant strengthening (Option E) or
   acceptance of the (|h2| = |t2| = 1) edge case fallback.

3. **Is the (T+T) eject case practically important enough to fix?**
   It only arises when you concat two K8Triples (i.e., already-large
   structures) AND drain from the right.  Many real-world catenable
   uses do concat + pop (which is fixed) or concat + traversal (which
   is O(n) by construction).  Worth a workload survey.
