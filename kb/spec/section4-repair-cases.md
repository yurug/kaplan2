---
id: section4-repair-cases
domain: spec
related: [data-model, algorithms, functional-properties]
---

# Section-4 repair cases — verbatim trace from KT99 §4.2

## One-liner
Authoritative line-by-line trace of the three Section-4 repair cases (Two-Buffer, One-Buffer, No-Buffer) reconstructed from KT99 §4.2 directly. Used because manual §7.5 has a corrupted Case-A description (precondition repeats many times in the source).

## Source

> Kaplan, H., Tarjan, R. E. *Purely Functional, Real-Time Deques with Catenation*. Journal of the ACM, 46(5), September 1999. Section 4.2 "Deque operations", pp. 586-587 (PDF pages 10-11).

The text of pages 10-11 is mirrored verbatim in `/tmp/pdf-extracts/kt/pages-001-020.txt` lines 488-555 (extracted via `pypdf`).

## Notation

For repair on a Section-4 deque, fix:

- `i` — the topmost red level (located via `jump4` in heap representation; manual §7.4).
- `P_i, S_i` — prefix and suffix buffers at level `i` (elements of type `A^i`).
- `P_{i+1}, S_{i+1}` — prefix and suffix buffers at level `i+1` (elements of type `A^{i+1}` = pairs of level-`i` elements).
- `|B|` — the number of elements in buffer `B`.
- "Pair an element from `P_{i+1}`" = peek into the level-`i+1` buffer and split the pair into two consecutive level-`i` elements.

The cell at level `i+1` exists iff level `i+1` is non-empty. The repair may delete level `i+1` ("eliminate" in KT99's wording) when both its buffers become empty and it is the bottommost level.

---

## Case Two-Buffer

### Precondition

```text
|P_{i+1}| + |S_{i+1}| >= 2
```

### Procedure (apply each step in order; each step is conditional on its `if`)

1. **If `P_{i+1}` is empty**: pop a pair from `S_{i+1}`, inject it into `P_{i+1}`.
2. **If `S_{i+1}` is empty**: eject a pair from `P_{i+1}`, push it onto `S_{i+1}`.

   *(After steps 1-2, both `P_{i+1}` and `S_{i+1}` are non-empty.)*

3. **If `|P_i| >= 4`**: eject two elements from `P_i`, pair them, push the pair onto `P_{i+1}`.
4. **If `|S_i| >= 4`**: pop two elements from `S_i`, pair them, inject the pair into `S_{i+1}`.
5. **If `|P_i| <= 1`**: pop a pair from `P_{i+1}`, inject its two elements individually into `P_i`.
6. **If `|S_i| <= 1`**: eject a pair from `S_{i+1}`, push its two elements onto `S_i`.
7. **If level `i+1` is the bottommost level and `P_{i+1}` and `S_{i+1}` are both now empty**: eliminate level `i+1`.

### Effect on sizes

After the case:

- `|P_i|` and `|S_i|` are each in `{2, 3}` (green): step 3 reduces a too-large `P_i`; step 5 raises a too-small `P_i`; analogously for `S_i`.
- `|P_{i+1}|` and `|S_{i+1}|` shift by at most ±1 each. Level `i+1` ends green or yellow (green ∈ {2, 3}, yellow ∈ {1, 4}).

### Sequence-preservation obligation

Each transfer is a pure rewriting on the level-element multiset:

- Pairing 2 level-`i` elements ↦ 1 level-`(i+1)` element preserves the flat element list since `flat_{i+1}(x, y) = flat_i(x) ++ flat_i(y)`.
- The reverse split is symmetric.
- Moving a pair between `P_{i+1}` and `S_{i+1}` preserves order because the central concatenation `… ++ S_{i+1} ++ flat_i(suf_{i+1}) ++ … ++ S_i ++ …` *(see `seq4_l` in `data-model.md` §3.3)* is unchanged.

### Color transition obligation

- Level `i` becomes green: `|P_i|, |S_i| ∈ {2, 3}` after the case.
- Level `i+1` is green or yellow after the case (since the changes to its sizes are bounded).
- Levels above `i` are untouched (manual §7.6 obligation 4).
- Levels below `i+1` are untouched (no operation reaches them).

---

## Case One-Buffer

### Precondition

```text
|P_{i+1}| + |S_{i+1}| <= 1   AND   ( |P_i| >= 2  OR  |S_i| >= 2 )
```

### Procedure

1. **If level `i` is the bottommost level**: create a new empty level `i+1`.
2. **If `|S_{i+1}| = 1`**: pop the pair from `S_{i+1}`, inject it into `P_{i+1}`.
3. **If `|P_i| >= 4`**: eject two elements from `P_i`, pair them, push the pair onto `P_{i+1}`.
4. **If `|S_i| >= 4`**: pop two elements from `S_i`, pair them, inject the pair into `P_{i+1}`.
5. **If `|P_i| <= 1`**: pop a pair from `P_{i+1}`, inject its two elements into `P_i`.
6. **If `|S_i| <= 1`**: eject a pair from `P_{i+1}`, push its two elements onto `S_i`.
7. **If `P_{i+1}` is now empty**: eliminate level `i+1`.

### Effect on sizes

After the case:

- `|P_i|, |S_i| ∈ {2, 3}` (green) — but note: by the precondition we may have started with `|S_i| ≤ 1`, in which case step 6 runs (one or two "split" operations) to bring `|S_i|` up.
- `P_{i+1}` is the only level-`(i+1)` buffer mentioned in this case; it ends with size 0 or 1 (yellow if non-zero, otherwise the level is eliminated).

### Sequence-preservation obligation

Same template as Case Two-Buffer. Each transfer is a pair/split or a buffer move.

### Color transition obligation

- Level `i` green.
- Level `i+1`: either eliminated, or green/yellow with `|P_{i+1}| ∈ {0, 1}` and `|S_{i+1}| = 0` (the case never touches `S_{i+1}` once it has been drained by step 2).

---

## Case No-Buffer

### Precondition

```text
|P_{i+1}| + |S_{i+1}| <= 1
AND  |P_i| <= 1
AND  |S_i| <= 1
```

### Observation (KT99)

> Among them, `P_i`, `P_{i+1}`, `S_{i+1}`, and `S_i` contain 2 or 3 level-`i` elements, two of which are paired in `P_{i+1}` or `S_{i+1}`.

So total count of level-`i` elements (after un-pairing one pair from `P_{i+1}` or `S_{i+1}` if present) is 2 or 3.

### Procedure

1. **Move all these elements to `P_i`**.
2. **Eliminate level `i+1` if it exists**.

### Effect on sizes

After the case:

- `|P_i| ∈ {2, 3}` (green).
- `|S_i| = 0` (red ... wait — this would make level `i` red again!).

**KT99 §4.1 special case**: when `child` is empty and one of the buffers is empty, the deque's color is the *non-empty* buffer's color. So with `S_i = 0` and level `i+1` eliminated, level `i`'s color is determined solely by `|P_i|` ∈ {2, 3} → green. ✓

### Sequence-preservation obligation

Splitting and concatenating buffer contents preserves order trivially.

### Color transition obligation

- Level `i` becomes green via the special-case color rule.
- Level `i+1` is eliminated.

---

## Why these three cases are exhaustive (KT99 Lemma D4-2)

When level `i` is the topmost red level and level `i+1` is green or yellow (by semiregularity), the size budget `|P_{i+1}| + |S_{i+1}|` is in `{0, 1, 2, 3, 4}`. Cases split it as:

- `≥ 2` → Two-Buffer.
- `≤ 1` and `(|P_i| ≥ 2 ∨ |S_i| ≥ 2)` → One-Buffer.
- `≤ 1` and `|P_i| ≤ 1` and `|S_i| ≤ 1` → No-Buffer.

The disjunction covers every value of `|P_{i+1}| + |S_{i+1}|` paired with every value of `(|P_i|, |S_i|)`.

## Proof obligations to discharge per case (manual §7.6)

For each case `K ∈ {Two-Buffer, One-Buffer, No-Buffer}`:

1. `seq4 (repair_K d) = seq4 d` (sequence preservation; P22).
2. `top_color (repair_K d) = Green3` (level `i` becomes green; P23).
3. Level `i+1` ends green / yellow / eliminated.
4. All levels above `i` are unchanged except for natural pointer rewiring in their `child4`/`jump4` fields.
5. The natural tree above level `i` carries an updated `jump4` shortcut consistent with the new color of level `i` (and therefore with the new repair-site target).

## Implementation

`rocq/KTDeque/DequePtr/` realizes these cases as the
overflow/underflow cascades `make_red_push_chain`,
`make_red_inject_chain`, `make_green_pop_chain`,
`make_green_eject_chain` in `OpsAbstract.v`, with cost-bounded
counterparts `exec_make_red_*_pkt_C` and `exec_make_green_*_pkt_C` in
`Footprint.v`.

Each operation takes a witness that the relevant top buffer is at the
extreme size (`B5` for overflow, `B0` for underflow) and returns a chain
whose top is green.

Each case is proved via a dedicated lemma whose statement matches
obligations (1)-(5) above.

## Agent notes
> The manual's §7.5 is corrupted at the source: the Case-A precondition `| P_{i+1} | + | S_{i+1} | >= 2` is repeated dozens of times. Use this trace, not the manual, for implementation reference.
> The KT99 paper text uses `|.|` for set-theoretic cardinality; in Rocq we use `buf_size`. Stick to that name in lemma statements.
> The "eliminate level `i+1`" step is *deallocation* in the abstract model but *no-op* in the allocation-only heap model — we just stop following the chain tail from the new top cell. The natural tree appears truncated; the heap retains the orphaned cells (persistence allows old roots to still see them).

## Related files
- `data-model.md` — type catalog.
- `algorithms.md` — high-level repair description (refers here for the verbatim trace).
- `../properties/functional.md` — sequence preservation and green-restoration P-entries.
- `../architecture/overview.md` — module dependency graph.
