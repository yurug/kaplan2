# Kaplan-Tarjan catenable deques: execution manual v3

Status: prescriptive implementation manual for a coding agent

Primary goal: build a Rocq development for a low-level heap implementation of Kaplan-Tarjan's persistent real-time catenable deque, with the heap layer close to the paper's pointer representations and with proofs against a pure sequence model.

Critical correction relative to the previous dossier:

- **Section 4 must be implemented first and must be a real verified module.**
- **Section 6 must use this module as its buffer implementation.**
- **Section 5 is pedagogical, not a dependency of the final artifact.**

This is not optional. Kaplan and Tarjan stage the construction as non-catenable deque, then steque, then full catenable deque. The final catenable deque uses the deque of Section 4 as a building block, and Viennot et al. explicitly restate this dependency. The steque stage is pedagogical and not required by the final runtime artifact. See [KT99, §§4,6] and [VWGPP, §1.1].

---

## 1. What is being built

### 1.1 Final public API

For a base element type `A`, the public API is:

```text
empty    : t A
is_empty : t A -> bool
push     : A -> t A -> t A
pop      : t A -> option (A * t A)
inject   : t A -> A -> t A
eject    : t A -> option (t A * A)
concat   : t A -> t A -> t A
to_list  : t A -> list A
to_seq   : t A -> Seq.t A
```

Proofs are stated against `to_list`.
`to_seq` is an extracted wrapper.

### 1.2 Semantics

Every public handle denotes a finite sequence.
The denotation function is written `⟦d⟧`.

Required laws:

```text
⟦empty⟧ = []

is_empty d = true  <->  ⟦d⟧ = []

⟦push x d⟧ = x :: ⟦d⟧

pop d = None           <->  ⟦d⟧ = []
pop d = Some (x, d')   ->   ⟦d⟧ = x :: ⟦d'⟧

⟦inject d x⟧ = ⟦d⟧ ++ [x]

eject d = None           <->  ⟦d⟧ = []
eject d = Some (d', x)   ->   ⟦d⟧ = ⟦d'⟧ ++ [x]

⟦concat d1 d2⟧ = ⟦d1⟧ ++ ⟦d2⟧
```

### 1.3 Persistence theorem

The heap implementation is persistent iff later operations do not change the denotation of old roots.
The theorem to prove is:

```text
If ExecPublic op H args = Some (H', out)
and r is an old public root already present in H,
then ⟦r⟧_H' = ⟦r⟧_H.
```

For the first artifact, persistence is obtained by **heap extension**:
operations allocate fresh cells and never overwrite old ones.

### 1.4 Dependency graph

```text
Warm-up RBR
      |
      v
Section-4 deque (real verified module)
      |
      +--> Buffer wrapper for Section 6
      |
      +--> optional Section-5 steque rehearsal
      |
      v
Section-6 catenable deque
      |
      v
public API + persistence + footprint theorems
      |
      v
optional explicit cost layer
      |
      v
optional Rust/C refinement
```

---

## 2. Deliberate design choices

### 2.1 What is kept close to Kaplan-Tarjan

The following must follow the paper closely:

- the staging: Section 4 first, then Section 6;
- the color disciplines;
- the tree-level regularity invariants;
- the Section 4 repair cases;
- the Section 6 `push`, `inject`, `concat`, `pop`, `eject` case structure;
- the need for shortcut pointers to the next repair site.

### 2.2 The one deliberate runtime deviation

The runtime heap stores the **natural child relation explicitly** and also stores the **shortcut pointer explicitly**.
This is slightly richer than the minimal pointer representation in the paper, but it is the right proof tradeoff.

For Section 4 this means:

- each level cell stores its natural child pointer;
- each top-level or non-yellow level cell also stores a shortcut to the nearest proper non-yellow descendant.

For Section 6 this means:

- each triple cell stores its natural child cadeque root;
- each triple that begins a preferred path of length at least 3 stores a shortcut to the tail of that preferred path.

This is the only structural simplification that is allowed by default.
It preserves the paper's algorithms and asymptotics, but makes the proofs modular because:

- denotation depends only on the natural tree;
- shortcut correctness is a separate invariant;
- operations can be justified as local edits to the natural tree plus local recomputation of shortcuts.

### 2.3 Why phase 1 is allocation-only

The first verified heap implementation is append-only:

- `alloc` yes,
- `read` yes,
- overwrite no.

This is still a low-level heap graph implementation.
It gives persistence for free and keeps the proof burden focused on the actual data-structure invariants.
Later, a mutable unique/frozen refinement can be added.

### 2.4 What must not happen

Do not:

- start from Rust or C;
- bypass Section 4 and implement only Section 6;
- encode the runtime heap using deep indexed families;
- genericize all constants immediately;
- introduce global mutation before correctness is stable;
- prove cost before proving footprint.

---

## 3. Mathematical preliminaries

### 3.1 Levels and flattening

For Section 4 and Section 6, the structure is recursive by level.
Define the level-indexed payload type:

```text
A^0     = A
A^(l+1) = A^l × A^l          for Section 4 only
```

For Section 4, define flattening to base elements:

```text
flat_0(x) = [x]
flat_(l+1)(x, y) = flat_l(x) ++ flat_l(y)
```

For a finite sequence `xs : list (A^l)`, define:

```text
Flat_l(xs) = concat (map flat_l xs)
```

For Section 6, the recursive payload is not `A^l` but `Stored_l(A)`.
Its denotation will be defined separately.

### 3.2 Three colors and four colors

Section 4 uses:

```text
Color3 = Green3 | Yellow3 | Red3
```

Section 6 uses:

```text
Color4 = Green4 | Yellow4 | Orange4 | Red4
```

The order is from bad to good:

```text
Red3 < Yellow3 < Green3
Red4 < Orange4 < Yellow4 < Green4
```

### 3.3 Arity and kind

For Section 6:

```text
Arity = 0 | 1 | 2
Kind  = only | left | right
```

A kind describes how a triple sits with respect to its parent.
An arity describes how many top-level triples a child cadeque contains.

### 3.4 Heaps and roots

Use explicit locations.

```text
Loc  : finite identifiers
Heap : finite map Loc -> Cell
```

Two root types are required.

```text
Root4 A  = empty4 | root4 loc
Root6 A  = empty6 | one6 loc | two6 loc loc
```

The exact Rocq encoding can use ordinary inductive types.

### 3.5 Heap extension

```text
heap_ext H H'  :=  every binding of H also appears unchanged in H'.
```

This is the key relation for persistence.

---

## 4. Phase 0 warm-up: redundant binary representation

This stage is short but mandatory because it teaches the proof pattern used later.

### 4.1 Purpose

Do **not** treat this as a side exercise.
Its purpose is to teach the agent these three ideas:

1. regularity is a local color discipline plus one top-level condition;
2. a public operation first creates a semiregular structure, then repairs it;
3. the repair preserves denotation and improves the top bad color.

### 4.2 Artifact

Implement the Clancy-Knuth style regular redundant binary representation from Kaplan-Tarjan Section 3.

Required proofs:

- regularity predicate is preserved by `succ`;
- denotation preserved by regularization;
- `succ` changes only constant many digits;
- pointer/packet representation gives O(1) access to the first non-`1` digit.

### 4.3 Exit criterion

Only continue to Section 4 when the agent can prove the following shape of theorem cleanly:

```text
regular n -> exists n', succ n = n' /\ regular n' /\ val n' = S (val n).
```

This stage should be tiny.
If it becomes large, the agent is already drifting.

---

## 5. Section 4: non-catenable deque, abstract model

This is the first real implementation stage.
The result of this stage is not a warm-up; it is the buffer module used later by Section 6.

### 5.1 Abstract tree representation

A Section-4 deque at level `l` is either:

```text
D4_l(A) ::= One(pre)
          | Two(pre, child, suf)
```

where:

- `pre` is a bounded buffer of elements of type `A^l`;
- `suf` is a bounded buffer of elements of type `A^l`;
- `child` is a deque `D4_(l+1)(A)`.

The buffer size bound is 5.
The bottommost level is represented by `One(pre)`.

### 5.2 Buffer model for Section 4

Use a small fixed-size buffer type:

```text
Buf5 X := vector X n, where 0 <= n <= 5
```

It is acceptable to implement this as six constructors `B0 .. B5`.
This is preferable to a generic vector because the proofs are easier and the runtime shape is explicit.

Define:

```text
buf5_size : Buf5 X -> nat
buf5_seq  : (X -> list A) -> Buf5 X -> list A
```

For Section 4 at level `l`, the element denotation is `flat_l`.
So `buf5_seq flat_l` gives the base-element sequence stored in a buffer.

### 5.3 Sequence semantics

Define `seq4_l : D4_l(A) -> list A` by:

```text
seq4_l(One b)        = buf5_seq flat_l b
seq4_l(Two p c s)    = buf5_seq flat_l p ++ seq4_(l+1)(c) ++ buf5_seq flat_l s
```

The public Section-4 module is `D4_0(A)`.

### 5.4 Buffer colors

Map sizes to colors exactly as in Kaplan-Tarjan Section 4:

```text
0,5 -> Red3
1,4 -> Yellow3
2,3 -> Green3
```

### 5.5 Level color

For a non-bottom level `Two(p,c,s)`:

```text
level_color = min(color(p), color(s))
```

except when `child` is empty and one of `p,s` is empty, in which case the color is the color of the nonempty buffer.

For `One b`, the level is treated as the final level.
You may either:

- treat it as syntactically terminal and define its color separately, or
- encode it as the special case above.

Pick one and stay consistent.

### 5.6 Descendants

Define the descendant chain:

```text
desc_0(d) = d
desc_(i+1)(d) = child(desc_i(d))      when child exists
```

### 5.7 Regularity predicates

A deque is **semiregular** if between any two red descendants there is a green descendant, ignoring yellows.
A deque is **regular** if it is semiregular and the first non-yellow descendant, if any, is green.

Formally:

```text
semireg4(d) :=
  forall i j,
    i < j -> color(desc_i d) = Red3 -> color(desc_j d) = Red3 ->
    exists k, i < k < j /\ color(desc_k d) = Green3.

reg4(d) :=
  semireg4(d) /\
  forall i,
    (forall j, j < i -> color(desc_j d) = Yellow3) ->
    color(desc_i d) <> Yellow3 ->
    color(desc_i d) = Green3.
```

### 5.8 Fundamental semantic fact

A regular deque has a top level that is green or yellow.
Therefore one end-operation can be performed on the top buffer without violating the size bound.
Only regularization may be needed afterwards.

This is the exact analogue of the RBR warm-up.

---

## 6. Section 4: runtime heap representation

### 6.1 Cell layout

Use one immutable heap cell per nonempty level.

```text
Record D4Cell X := {
  pre4   : Buf5 X;
  child4 : option loc;     // natural child pointer
  suf4   : Buf5 X;
  col4   : Color3;         // cached, checked by invariant
  jump4  : option loc      // nearest proper non-yellow descendant, if this cell is top-level or non-yellow
}
```

The root type is:

```text
Root4 X := empty4 | root4 loc
```

### 6.2 Representation invariant

`repr4 H r d` means:

1. `r` decodes in heap `H` to the natural tree `d` via `child4`;
2. every cell is well-formed with respect to `d`;
3. cached color `col4` equals the mathematical color of the represented level;
4. `jump4` is correct:
   - if the cell is yellow and not top-level then `jump4 = None`;
   - if the cell is top-level or non-yellow then `jump4` points to the nearest proper non-yellow descendant if one exists, else `None`.

### 6.3 Why this representation is enough

`child4` gives the natural tree semantics.
`jump4` gives O(1) access to the first proper non-yellow descendant.
This is exactly what regularization needs after a top-level operation.

This is very close to the Section-4 pointer representation in the paper, except that the natural child pointer is kept in every cell, which simplifies semantic proofs.

---

## 7. Section 4: operations and proofs

### 7.1 Public operations

Public operations are:

```text
empty4, is_empty4, push4, pop4, inject4, eject4, to_list4
```

All are implemented on the heap representation.

### 7.2 Naive top-level update

For `push4 x d`:

- if `d` is empty, allocate one level whose single buffer is `[x]`;
- else push onto the top prefix;
- except when top prefix and child are empty, in which case push onto the top suffix.

`inject4` is symmetric.
`pop4` and `eject4` remove from the symmetric end, failing only on the empty deque.

### 7.3 Post-update state

After the naive top-level update, the result is either regular already or only semiregular.
The only possible violation is that the first non-yellow descendant may have become red.
This is the theorem to prove first:

```text
Theorem d4_naive_step_semireg :
  reg4 d -> semireg4 (naive_step d).
```

### 7.4 Repair site

The repair site is:

- the top level if it is red;
- otherwise the node reached by `jump4` from the top cell, when that node is red.

Because of the invariant, this is O(1).

### 7.5 Repair cases

Repair must follow Kaplan-Tarjan Section 4 verbatim.
Let level `i` be the topmost red level.
Let `P_i`, `P_(i+1)`, `S_(i+1)`, `S_i` denote the prefix and suffix buffers of levels `i` and `i+1`.
Elements of level `i+1` are pairs of level-`i` elements.

#### Case A. Two-buffer case

Precondition:

```text
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |
| P_(i+1) | + | S_(i+1) | >= 2 |

Then the four buffers together contain exactly 2 or 3 level-`i` elements.
Move them all into `P_i` and delete level `i+1` if it exists.

### 7.6 Local proof obligations for each repair case

For every repair case, prove these four lemmas in this order:

1. **sequence preservation**;
2. **level `i` becomes green**;
3. **level `i+1` becomes green or yellow or disappears**;
4. **all levels above `i` are unchanged except for local rewiring of pointers**.

The key semantic fact is that a pair at level `i+1` denotes exactly two consecutive elements at level `i`.
Therefore every transfer is semantics-preserving.

### 7.7 Pencil-and-paper proof of Theorem 4.1 style result

Prove, on paper first, the following structure.

#### Lemma D4-1

`reg4 d -> semireg4 (naive_step d)`.

Reason:
A top-level operation can change the top color by at most one downward step.
Thus only the first non-yellow descendant can become a problem.
No deeper regularity pattern can be broken.

#### Lemma D4-2

If `semireg4 d` and the topmost bad descendant is red, then one of Cases A, B, C applies.

Reason:
The local neighborhood of the topmost red level has only finitely many size possibilities.
The case split is exhaustive.

#### Lemma D4-3

Each repair case preserves denotation.

Reason:
Only local moves between buffers happen, and each move is either:

- moving one pair between child buffers,
- converting two current-level elements into one child-level pair,
- converting one child-level pair into two current-level elements,
- deleting an empty level.

Each of these preserves left-to-right order.

#### Lemma D4-4

Each repair case restores regularity.

Reason:
Level `i` becomes green, and the only deeper color degradation is at level `i+1`, by at most one step.
Since `i` was the topmost red level, this exactly restores the redundant-binary style invariant.

#### Theorem D4

Every public operation on a regular Section-4 deque returns a regular deque and preserves denotation.

### 7.8 Heap refinement theorems

Required statements:

```text
Theorem push4_refines :
  exec_push4 H r x = Some (H', r') ->
  repr4 H r d ->
  exists d', repr4 H' r' d' /\ seq4 d' = x :: seq4 d /\ heap_ext H H'.
```

Analogous theorems are required for `pop4`, `inject4`, `eject4`.

### 7.9 Bounded footprint theorem for Section 4

First prove footprint, not cost.

```text
exists K4_alloc K4_reads,
  every Section-4 operation allocates at most K4_alloc cells
  and reads at most K4_reads cells.
```

Only after this module is complete may it be used as a buffer layer for Section 6.

---

## 8. Section 6 needs a buffer wrapper over Section 4

The final catenable deque uses the Section-4 deque as its buffer module.
This stage makes that dependency explicit.

### 8.1 Buffer wrapper

A Section-6 buffer is:

```text
Record Buf6 X := {
  root6_buf : Root4 X;
  len6_buf  : nat
}
```

The runtime stores `root6_buf` and `len6_buf`.
The proof relation ensures that `len6_buf` is the exact number of level-elements stored in `root6_buf`.

### 8.2 Why the exact cached size is mandatory

Section 6 colors depend on thresholds 5, 6, 7, 8.
Section 6 algorithms branch on exact comparisons such as:

- `< 8`,
- `<= 8`,
- exactly 2,
- at least 3,
- at least 5.

Therefore a cached exact size is the cleanest design.
Kaplan-Tarjan explicitly allow storing sizes with buffers as an efficiency aid.

### 8.3 Required buffer operations for Section 6

Do not expose only the public Section-4 API.
Add these verified internal helpers over `Buf6`:

```text
buf_size
buf_push
buf_inject
buf_pop
buf_eject
buf_take_first2
buf_take_last2
buf_take_first3
buf_take_last3
buf_move_all_when_lt8
buf_concat_small
```

Each helper must have both:

- a sequence law, and
- an exact size law.

This is crucial because almost every Section-6 proof reduces to a sequence equation plus a size arithmetic fact.

---

## 9. Optional Section 5 steque rehearsal

Section 5 is not a dependency of the final artifact.
Still, it is a good optional rehearsal if the agent struggles with catenation proofs.

Recommendation:

- implement Section 5 only at the logical layer;
- do not build a separate heap refinement unless Section 6 stalls badly;
- use it to rehearse the pattern `naive step -> semiregular -> repair -> regular` in the presence of `concat`.

If time is short, skip this stage.

---

## 10. Section 6: abstract tree model of catenable deques

### 10.1 Recursive payloads by level

For Section 6 the recursive slowdown is not based on pairs.
Instead it is based on **stored triples**.
The level-indexed payload type is:

```text
Elt_0(A)     = A
Elt_(l+1)(A) = Stored(Elt_l(A))
```

So:

- level 0 buffers contain elements of type `A`;
- level 1 buffers contain stored triples over `A`;
- level 2 buffers contain stored triples over stored triples over `A`;
- and so on.

This is the crucial dependency that makes Section 6 use Section 4 as a buffer layer.
A Section-6 buffer is still a Section-4 deque, but its element type changes with the level.

### 10.2 Stored triples and ordinary triples

A catenable deque is built from triples.
There are two categories.

#### Stored triples over an element type `X`

A stored triple lives inside a buffer.
Its buffers contain elements of type `X`.
Its child cadeque contains **stored triples over `X`**.

```text
Stored(X) ::= Small(buf : Buf6 X)
            | Big(pre : Buf6 X,
                  child : Root6 (Stored X),
                  suf : Buf6 X)
```

#### Ordinary triples over an element type `X`

An ordinary triple appears on the boundary of a cadeque.
It has kind `only`, `left`, or `right`.
Its buffers contain elements of type `X`.
Its child cadeque contains stored triples over `X`.

```text
Ord(X) ::= Only(pre : Buf6 X, child : Root6 (Stored X), suf : Buf6 X)
         | Left(pre : Buf6 X, child : Root6 (Stored X), suf : Buf6 X)
         | Right(pre : Buf6 X, child : Root6 (Stored X), suf : Buf6 X)
```

The difference between the three forms is not semantic order but size constraints.
Semantics is always:

```text
seq(pre) ++ seq(child) ++ seq(suf)
```

### 10.3 Root shape

A root over payload type `X` is:

```text
Root6 X ::= empty6 | one6 loc | two6 loc loc
```

At the top level, `X = A`.
Inside a child cadeque, `X = Stored A`.
And deeper still, the pattern repeats.

### 10.4 Generalized sequence semantics

Denotation is defined by mutual recursion and must be **parameterized by the denotation of buffer elements**.
This mirrors the generalized model-function pattern from the Rocq paper.

For an arbitrary `E : X -> list A`, define:

```text
BSeq(E, b) : list A
```

as the sequence denoted by the Section-4 buffer `b` when its elements are interpreted by `E`.
Then define:

```text
StoredSeq(E, Small b)     = BSeq(E, b)
StoredSeq(E, Big p c s)   = BSeq(E, p) ++ RootSeq(StoredSeq(E), c) ++ BSeq(E, s)

OrdSeq(E, Only p c s)     = BSeq(E, p) ++ RootSeq(StoredSeq(E), c) ++ BSeq(E, s)
OrdSeq(E, Left p c s)     = BSeq(E, p) ++ RootSeq(StoredSeq(E), c) ++ BSeq(E, s)
OrdSeq(E, Right p c s)    = BSeq(E, p) ++ RootSeq(StoredSeq(E), c) ++ BSeq(E, s)

RootSeq(F, empty6)        = []
RootSeq(F, one6 t)        = OrdSeq(F, t)
RootSeq(F, two6 l r)      = OrdSeq(F, l) ++ OrdSeq(F, r)
```

The public denotation is:

```text
⟦q⟧ = RootSeq((fun x => [x]), q)
```

where the base element type is `A`.

### 10.5 Size constraints on triples

These are exactly the paper's constraints.

#### Stored triples

```text
(ST1) both buffers have size at least 3
(ST2) unless child is empty and one of the buffers is empty,
      in which case the other buffer has size at least 3
```

#### Ordinary triples

```text
(OT1) only triple: both buffers have size at least 5
(OT2) unless child is empty and one buffer is empty,
      in which case the other buffer has positive size
(OT3) left triple:  prefix size at least 5, suffix size exactly 2
(OT4) right triple: prefix size exactly 2, suffix size at least 5
```

### 10.6 Color assignment

Stored triples are always green.
Ordinary triples use the Section-6 four-color thresholds:

```text
5 -> Red4
6 -> Orange4
7 -> Yellow4
8 and above -> Green4
```

For an ordinary triple `t = (pre, child, suf)`:

- if `child` is empty then `t` is green;
- if `t` is `Only`, its color is the worse of the prefix and suffix colors;
- if `t` is `Left`, its color is the prefix color;
- if `t` is `Right`, its color is the suffix color.

### 10.7 Preferred child and preferred path

A green or red triple has no preferred child.
A yellow or orange triple behaves as follows:

- arity 1: the only child is preferred;
- arity 2 and yellow: the left child is preferred;
- arity 2 and orange: the right child is preferred.

A preferred path is the maximal downward path obtained by repeatedly following the preferred child.
Its tail is the first green or red triple on that path.
Its color is the color of that tail, so every preferred path is green or red.

### 10.8 Regularity

A cadeque is **semiregular** when both hold:

```text
(RC2) every preferred path that starts at a child of a red triple is green
(RC3) every preferred path that starts at a nonpreferred child of an orange triple is green
```

A cadeque is **regular** if it is semiregular and additionally:

```text
(RC4) every preferred path that starts at a top-level triple is green
```

This is the exact invariant that drives the Section-6 proofs.

### 10.9 Structural lemmas needed immediately

Before any operation is implemented, prove these purely structural facts:

1. if a cadeque is semiregular, every child cadeque inside every triple is semiregular;
2. if a top-level preferred path is red, its tail is unique;
3. if a triple is red, its child cadeque is regular;
4. if a triple is orange, its nonpreferred child, if any, begins a green preferred path.

These are the lemmas the operational proofs repeatedly use.

---

## 11. Section 6: runtime heap representation

### 11.1 Triple cell layout

Use one immutable heap cell per triple.
The same cell type is used for stored and ordinary triples.

```text
Record T6Cell X := {
  role6   : stored | only | left | right;
  pre6    : Buf6 X;
  child6  : Root6 (Stored X);  // natural child cadeque
  suf6    : Buf6 X;
  col6    : Color4;        // cached, checked by invariant
  adopt6  : option loc     // tail of preferred path starting here, if path length >= 3
}
```

The root type is:

```text
Root6 X := empty6 | one6 loc | two6 loc loc
```

### 11.2 Why one extra shortcut is enough

`child6` keeps the natural tree explicit.
`adopt6` is the only shortcut needed.

If a preferred path has length:

- 1: tail is the node itself;
- 2: tail is the natural preferred child;
- 3 or more: tail is `adopt6`.

Thus the tail of any preferred path is found in O(1).
That is all `pop` and `eject` need.

### 11.3 Representation invariant

`repr6 H r q` means:

1. `r` decodes in `H` to the natural tree `q` via `child6`;
2. all local size constraints hold;
3. all cached colors `col6` equal the mathematical colors of triples;
4. `adopt6` is correct:
   - `None` when the preferred path has length 1 or 2,
   - `Some u` when the preferred path has length at least 3 and `u` is its tail;
5. the decoded natural tree is regular at public entry points.

### 11.4 This is close enough to the compressed forest

The paper compresses preferred paths by changing one parent relation.
This plan instead caches the path tail while leaving natural child pointers untouched.
That is the single planned deviation.
It preserves the same constant-time navigation property while making denotation and refinement proofs much cleaner.

---

## 12. Section 6: operations

Implement all operations first on the natural tree model, then on the heap, then prove refinement.
Never prove list equations directly on raw heap cells.

### 12.1 `push`

Let `t` be the left top-level triple if it exists, otherwise the only top-level triple.

- if the root is empty, allocate one only triple whose nonempty buffer holds `x`;
- else, if the prefix of `t` is nonempty, push `x` into that prefix;
- otherwise push `x` into the suffix.

Then recompute local color and local shortcut(s).

Proof target:

```text
regular q -> regular (push x q)
```

Sequence law:

```text
⟦push x q⟧ = x :: ⟦q⟧
```

### 12.2 `inject`

Symmetric to `push` using the right top-level triple or the only triple.

### 12.3 `concat`

`concat` must follow the paper's four-case top-level normalization.
Do not improvise a different algorithm.

Let the arguments be `d` and `e`.
Assume both nonempty.

#### Case 1. All top-level buffers of `d` and `e` are nonempty

Normalize `d` to one triple `t` and normalize `e` symmetrically to one triple `u`.
Result root is `two6 t u`.

Subcases for `d`:

1. `d = two6 t1 t2`, and the left triple `t1` has nonempty child.
   Merge `suffix(t1)` with `prefix(t2)` into one middle prefix.
   Remove the last two elements of `suffix(t2)` to create the new outer suffix.
   Inject one stored triple into `child(t1)`.

2. `d = two6 t1 t2`, and `child(t1)` is empty.
   Fold `suffix(t1)` into `prefix(t2)`.
   This turns `d` into an only triple.
   Continue with subcase 3 or 4.

3. `d = one6 t1`, and `child(t1)` is nonempty.
   Remove the last two elements of `suffix(t1)` to create the new outer suffix.
   Convert the remainder of the suffix into a stored triple and inject it into `child(t1)`.

4. `d = one6 t1`, and `child(t1)` is empty.
   If the suffix size is at most 8, move all but the last two elements of the suffix into the prefix.
   Otherwise split the suffix into first 3, middle, last 2; create a one-element child cadeque holding the middle part as a stored triple.

Do the symmetric transformation on `e`.

#### Case 2. `d` is an only triple with a single nonempty buffer, `e` has all top-level buffers nonempty

Let `p3` be the unique nonempty buffer of `d`.
Let `t2` be the left or only top-level triple of `e`.

- if `|p3| < 8`, push all of `p3` into `prefix(t2)`;
- else create one stored triple from `prefix(t2)` and push it into `child(t2)`.

The right top-level triple of `e`, if any, is preserved.

#### Case 3

Symmetric to Case 2.

#### Case 4. both roots are only triples with a single nonempty buffer

- if either buffer has size less than 8, combine both into one nonempty buffer of an only triple;
- otherwise form an only triple with one buffer on each side.

Proof target:

```text
semireg d -> semireg e -> semireg (concat d e)
regular d -> regular e -> regular (concat d e)
```

Sequence law:

```text
⟦concat d e⟧ = ⟦d⟧ ++ ⟦e⟧
```

### 12.4 `pop`: remove then repair

`pop` has two phases.

#### Phase 1. remove

Let `t` be the left top-level triple if it exists, otherwise the only top-level triple.

- pop from the prefix of `t` if nonempty;
- otherwise pop from its suffix.

This creates a semiregular structure whose only possible violation is that the preferred path beginning at the left top-level triple may now be red.

#### Phase 2. locate the red tail

If that preferred path is green, stop.
Otherwise let `u` be its red tail.
Use `adopt6` and at most one natural preferred-child step to find `u` in O(1).

#### Phase 3. repair

Repair must follow the paper's cases.
Let `u = (p1, d1, s1)`.
Because `u` is red, `d1` is nonempty.

##### Case 1. `u` is a left triple

Pop the first triple `(p2, d2, s2)` from `d1`, without repairing `d1` yet.
Let the remainder be `d1'`.

- **Case 1a.** `p2` and `s2` are both nonempty.
  Create a stored triple from `s2` and push it onto `d1'`.
  Push all elements of `p1` onto `p2`.
  Concatenate `d2` with the modified `d1'`.
  Result is the left triple `(p2', d3, s1)`.

- **Case 1b.** one of `p2`, `s2` is empty.
  Merge `p1`, `p2`, `s2` into one prefix buffer.
  Result is `(p3, d1', s1)`.

##### Case 2. `u` is an only triple

- **Case 2a.** `s1` has size at least 8.
  Perform the same repair as Case 1, obtaining a result with a large prefix.

- **Case 2b.** `p1` has size at least 8.
  Symmetric to Case 2a, obtaining a result with a large suffix.

- **Case 2c.** both `p1` and `s1` have size at most 7.
  Pop the first triple `(p2, d2, s2)` from `d1`.
  Let the remainder be `d1'`.

  - if `d1'` is empty, merge `p1` with `p2` and merge `s2` with `s1`, result `(p4, d2, s4)`;
  - otherwise also eject the last triple `(p3, d3, s3)` from `d1'`, leaving `d1''`;
    then repair the left side and the right side independently:
    - if one of `p2, s2` is empty, collapse `p1, p2, s2` into one prefix and keep `d1''`;
      else push a stored triple for `s2` into `d1''`, move `p1` into `p2`, and concatenate with `d2`;
    - symmetrically for the right side using `p3, s3, s1` and `d3`.

This produces a green root `v` that replaces `u`.

### 12.5 `eject`

Exact mirror of `pop`.
Do not attempt to prove it by raw duplication.
Abstract the left/right symmetry early.

---

## 13. Section 6: pencil-and-paper proofs

This section is the proof driver.
The coding agent should implement in this order because the proofs match the paper's internal logic.

### 13.1 Preliminary lemma: child regularity under a red triple

```text
If q is semiregular and u is a red triple of q,
then child(u) is regular.
```

Reason:
A child path below a red triple must start green by semiregularity.

### 13.2 Lemma C6-1: push/inject preserve regularity

`push` and `inject` change only the color of one top-level triple.
Possible changes are:

```text
Yellow4 -> Green4
Orange4 -> Yellow4
Red4    -> Orange4
```

The first change clearly helps.
The second and third changes only modify which child is preferred or nonpreferred, and semiregularity gives exactly the needed green-path side condition.

### 13.3 Lemma C6-2: concat preserves regularity

Every concat case must be proved by the same template:

1. prove every newly created child cadeque is semiregular using already proved `push`, `inject`, and `concat` facts at smaller depth;
2. prove the new outer triple has the same color as, or a better color than, the source triple from which it was formed;
3. conclude semiregularity, and if the source root was top-level green-path clean, conclude regularity.

The crucial point is that concat only rearranges the top constant-size neighborhood.
No deep repair is needed.

### 13.4 Lemma C6-3: remove-first and remove-last only create a top-path defect

After phase 1 of `pop`:

```text
regular q -> semiregular q'
```

and the only possible regularity defect is:

```text
the preferred path beginning at the left or only top-level triple may be red.
```

After both ends are removed from an only triple, the result is still semiregular.

Reason:
Removing one element can degrade the color of one outer triple by at most one step.
All deeper packet colors are unchanged.

### 13.5 Lemma C6-4: repair creates a green root

In each repair case, the replacement subtree rooted at `v` must satisfy:

1. `triple_seq(v) = triple_seq(u)` minus the popped front element;
2. `color(v) = Green4`;
3. `child(v)` is semiregular;
4. any newly created side packet begins green when the regularity rules require it.

Then the whole deque is regular.

### 13.6 Final theorem

```text
Theorem C6 :
  every public operation on a regular cadeque returns a regular cadeque
  and satisfies the public sequence law.
```

---

## 14. Heap refinement and persistence

### 14.1 Heap execution style

Use a shallow state-and-error monad for phase 1:

```text
M X := Heap -> option (Heap * X)
```

This is enough.
A deep syntax of commands can be added later for explicit cost accounting.

### 14.2 Refinement theorem schema

Every public operation needs one theorem of this shape:

```text
Theorem exec_op_refines :
  exec_op H args = Some (H', out) ->
  repr6 H root q ->
  exists q' out',
    repr6 H' root' q' /\
    out' matches the abstract result /\
    abstract_spec q q' out' /\
    heap_ext H H'.
```

### 14.3 Persistence theorem

Because of heap extension and immutable cells, persistence is almost immediate.
The only nontrivial work is proving that denotation depends only on the natural child relation and not on any newly allocated unrelated cells.

Required lemma:

```text
heap_ext H H' -> repr6 H r q -> repr6 H' r q.
```

Then persistence follows.

### 14.4 Memory safety theorem

For every operation prove:

- every read location is present in the input heap;
- every newly allocated location is fresh;
- output roots only point to allocated cells.

These are simple but must be explicit.

---

## 15. Footprint first, cost second

### 15.1 Footprint theorem

Before an explicit cost semantics exists, prove bounded structural footprint.

For each public operation prove constants `R_op` and `A_op` such that:

```text
reads(op)  <= R_op
allocs(op) <= A_op
```

and also bound the number of internal buffer calls to the Section-4 module.

### 15.2 Why footprint is the right first theorem

It is compositional.
Once Section 4 has its own bounds, Section 6 can import them.
Then a later explicit small-step cost model can be layered on top almost mechanically.

### 15.3 Cost layer

Only after all correctness and footprint theorems are done:

1. reify monadic heap code into a command syntax;
2. assign unit or weighted costs to `read`, `alloc`, branch, and buffer calls;
3. derive worst-case constant bounds for all public operations.

Do not do this earlier.

---

## 16. Repo structure

```text
KTDeque/
  Common/
    Prelude.v
    FinMapHeap.v
    ListFacts.v
    Params.v
    Monad.v
    Symmetry.v

  RBR/
    Model.v
    Pointer.v
    Succ.v
    Proofs.v

  Deque4/
    Buf5.v
    Model.v
    HeapCells.v
    Repr.v
    OpsNaive.v
    Repair.v
    Correctness.v
    Footprint.v

  Buffer6/
    SizedBuffer.v
    SmallMoves.v
    Correctness.v

  Steque5/              // optional
    Model.v
    Correctness.v

  Cadeque6/
    TreeModel.v
    Colors.v
    PreferredPaths.v
    HeapCells.v
    Repr.v
    OpsPushInject.v
    OpsConcat.v
    OpsPopEject.v
    Correctness.v
    Persistence.v
    Footprint.v

  Public/
    API.v
    ToSeq.v
    Summary.v

  Cost/                 // optional later
    Syntax.v
    Semantics.v
    Bounds.v

  Extract/
    OCaml.v
```

---

## 17. Ticket plan with hard gates

### Ticket 00. Common infrastructure

Output:

- heap finite map,
- heap extension,
- monad,
- list lemmas,
- named constants in `Params.v`.

Gate:
No deque code yet.

### Ticket 01. RBR warm-up

Output:

- regular RBR model,
- `succ`,
- proofs.

Gate:
`make` succeeds, no admits.

### Ticket 02. `Buf5`

Output:

- six-constructor fixed-size buffer,
- size and sequence laws.

Gate:
All buffer lemmas automated.

### Ticket 03. Section-4 abstract model

Output:

- `D4_l`,
- `seq4`,
- `semireg4`, `reg4`.

Gate:
Pure lemmas about descendants and regularity proved.

### Ticket 04. Section-4 heap cells and representation

Output:

- `D4Cell`, `Root4`, `repr4`.

Gate:
Proof that `repr4` determines `seq4`.

### Ticket 05. Section-4 operations

Output:

- naive update,
- repair cases A/B/C,
- public ops.

Gate:
Theorem D4 plus heap refinement theorems complete.

### Ticket 06. `Buf6` wrapper

Output:

- exact cached size,
- small constant transfer helpers,
- sequence and size laws.

Gate:
No direct raw manipulation of Section-4 roots remains inside Section-6 code.

### Ticket 07. Section-6 abstract tree model

Output:

- stored triples,
- ordinary triples,
- root shape,
- preferred paths,
- regularity.

Gate:
All structural lemmas in §10.8 proved.

### Ticket 08. Section-6 heap cells and representation

Output:

- `T6Cell`, `Root6`, `repr6`.

Gate:
Proof that denotation uses only natural child roots and shortcuts are sound.

### Ticket 09. Section-6 `push` and `inject`

Gate:
Lemma C6-1 and refinement theorems.

### Ticket 10. Section-6 `concat`

Gate:
Lemma C6-2 and refinement theorem.

### Ticket 11. Section-6 `pop` and `eject`

Gate:
Lemmas C6-3, C6-4 and refinement theorems.

### Ticket 12. Public API summary

Output:

- one theorem bundling all sequence laws,
- persistence theorem,
- memory safety theorem.

Gate:
`Public/Summary.v` compiles with no admits.

### Ticket 13. Footprint

Gate:
bounded reads and allocs for Section 4 and Section 6.

### Ticket 14. Optional cost layer

Gate:
explicit worst-case constant bound theorems.

### Ticket 15. Optional Rust/C refinement

Output:

- low-level implementation with same cell layout,
- simulation proof to Rocq heap model.

---

## 18. Symmetry policy

Do not prove left and right cases twice.
Abstract left/right symmetry early.

Mandatory mirrored pairs:

- `push` / `inject`
- `pop` / `eject`
- left triple / right triple
- first-two / last-two buffer helpers

Introduce a generic "side" parameter where it actually decreases proof duplication.
Do not over-generalize everything else.

---

## 19. Parameterization policy for future buffer retuning

Your future goal is to tune constants.
The correct compromise is:

- centralize constants now,
- prove only the Kaplan-Tarjan instance now.

Required constants in `Params.v`:

```text
buf4_cap      = 5
stored_min    = 3
only_min      = 5
c6_red        = 5
c6_orange     = 6
c6_yellow     = 7
c6_green_min  = 8
```

Every arithmetic lemma must depend on named constants, not raw literals sprinkled through the code.
But do not attempt a fully generic theorem over arbitrary parameter records in phase 1.
That is phase 3 work, not phase 1 work.

---

## 20. Allowed simplifications if the agent stalls

These are ordered from best to worst.

1. keep the natural child pointers and also keep shortcuts, as specified here;
2. postpone Section-5 steque entirely;
3. postpone explicit cost and keep only footprint;
4. keep all buffer sizes cached explicitly;
5. if the compressed-path shortcut proofs still stall, replace `adopt6` with a cached direct pointer to the current repair site at the root only, but document the deviation clearly.

Do **not** simplify by replacing Section 6 with a completely different data structure.

---

## 21. Forbidden shortcuts

The following are not allowed in the core correctness layer:

- axiomatizing sequence semantics;
- axiomatizing regularity preservation;
- using `Admitted` in Section 4 or Section 6 correctness files;
- replacing the Section-4 buffer implementation with plain lists;
- dropping persistence from the heap model;
- proving only logical operations and skipping the heap refinement.

An admit is tolerated only in the optional cost layer, and only if isolated in `Cost/`.

---

## 22. Final acceptance checklist

The project is complete only if all are true:

1. `Deque4` exists as a separately usable verified module.
2. `Buffer6` is implemented by wrapping `Deque4`, not by lists.
3. `Cadeque6` uses `Buffer6` everywhere.
4. Public sequence laws are proved.
5. Persistence is proved by heap extension.
6. Memory safety is proved.
7. Bounded footprint is proved.
8. The root summary theorem compiles with no admits.
9. The only representation deviation from the paper is the explicit retention of natural child pointers plus shortcut caches.
10. Every constant used in size/color reasoning is centralized in `Params.v`.

---

## 23. One-page summary for the coding agent

If the agent ignores everything else, it must still obey this:

1. Implement **Section 4 first**.
2. Make it a real verified module with heap refinement.
3. Wrap it as `Buffer6` with exact cached sizes.
4. Implement Section 6 over that wrapper.
5. Use the **natural tree for semantics** and **shortcut pointers only for O(1) navigation**.
6. Follow Kaplan-Tarjan's cases literally for Section 4 repair and Section 6 `concat` and `pop/eject` repair.
7. Prove **correctness and persistence first**, **footprint second**, **cost third**.

That is the intended execution path.

---

## 24. References to follow while implementing

Primary references:

- Kaplan and Tarjan, *Purely Functional, Real-Time Deques with Catenation*:
  - Section 4 for the non-catenable deque
  - Section 5 for the optional steque rehearsal
  - Section 6 for the final catenable deque
- Viennot, Wendling, Guéneau, Pottier, *Verified Purely Functional Catenable Real-Time Deques*:
  - Section 1.1 for the dependency graph and tree vs pointer representation
  - Section 4 for the bufferless tree explanation of preferred paths
  - Sections 7 and 8 for the role of level/size indexing on the logical side

This document intentionally keeps the runtime layer lower-level and less typed than Viennot et al., but the logical explanations in that paper are excellent and should be mined aggressively.
