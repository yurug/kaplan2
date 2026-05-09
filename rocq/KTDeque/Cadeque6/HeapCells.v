(** * Module: KTDeque.Cadeque6.HeapCells -- heap-cell layout for the
      Phase 4b imperative DSL.

    First-time reader: read [kb/spec/phase-4b-imperative-dsl.md] and
    [DequePtr/HeapCells.v]'s analogue (vendored historically) before
    this file.

    ## Why this exists

    Phase 4b of the catenable plan delivers the heap-based
    imperative DSL needed for WC O(1) catenation (the headline KT99
    §6 result).  The DSL operates on a [Heap (CadCell A)] of
    constant-sized cells linked by [Loc] pointers; this file
    introduces that cell type plus the basic sequence-semantics
    interpretation.

    What's deferred to subsequent Phase 4b chunks (per
    [kb/spec/phase-4b-imperative-dsl.md]):

    - The embed/extract pair connecting [Cadeque6/Model.v]'s
      abstract [Cadeque A] to [Heap (CadCell A)].
    - The non-recursive [cad_*_imp] operations in the cost monad.
    - The five repair cases for [cad_concat_imp] (1a / 1b / 2a /
      2b / 2c per manual §12.4) plus the [adopt6] shortcut.
    - Per-op refinement theorems linking the imperative ops to the
      abstract spec, with closed-form constant cost bounds.

    ## What this file provides

    The [CadCell A] inductive (8 constructors, one per shape kind in
    the abstract model) plus the cell-level sequence interpretation.
    Each [Loc] payload in a [CadCell] is a heap pointer; the cell
    layout enables structural sharing — crucial for persistent
    catenation where the inputs A and B share their cells with the
    output A++B.

    The [adopt6] shortcut field on cadeque cells is a pre-cooked
    pointer to the preferred-path tail's triple, allowing O(1)
    dispatch to the relevant repair case.

    ## Cross-references

    - [kb/spec/phase-4b-imperative-dsl.md]   -- the design doc.
    - [Cadeque6/Model.v]                     -- the abstract types
                                                being mirrored.
    - [Common/FinMapHeap.v]                  -- the [Loc] / [Heap]
                                                machinery.
    - [Common/HeapExt.v]                     -- well-formed heap.
    - [DequePtr/Model.v]                     -- the analogous
                                                Section-4 cell
                                                layout.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Common Require Import FinMapHeap HeapExt.
From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model.

(** ** [CadCell A]: the heap-cell type.

    Eight constructors, mirroring [Cadeque6/Model.v]'s [Triple],
    [Cadeque], and [Stored] inductives.  Each constructor that
    references a child or sibling cell uses a [Loc] pointer instead
    of a recursive type — this enables structural sharing.

    Triple cells:
    - [CC_TripleOnly  pre child suf]
    - [CC_TripleLeft  pre child suf]
    - [CC_TripleRight pre child suf]

    Cadeque cells:
    - [CC_CadEmpty]
    - [CC_CadSingle  triple_loc]
    - [CC_CadDouble  left_triple_loc right_triple_loc]

    Stored cells (live inside Buf6 X of a parent triple's buffers
    when those buffers are flattened to the heap):
    - [CC_StoredSmall buf]
    - [CC_StoredBig   pre child_cad suf]

    The [adopt6] shortcut is encoded as an optional companion [Loc]
    on the cadeque cells; we'll add that in a follow-up chunk once
    the basic cell type compiles. *)

Inductive CadCell (A : Type) : Type :=
| CC_TripleOnly  : Buf6 A -> Loc -> Buf6 A -> CadCell A
| CC_TripleLeft  : Buf6 A -> Loc -> Buf6 A -> CadCell A
| CC_TripleRight : Buf6 A -> Loc -> Buf6 A -> CadCell A
| CC_CadEmpty    : CadCell A
| CC_CadSingle   : Loc -> CadCell A
| CC_CadDouble   : Loc -> Loc -> CadCell A
| CC_StoredSmall : Buf6 A -> CadCell A
| CC_StoredBig   : Buf6 A -> Loc -> Buf6 A -> CadCell A.

Arguments CC_TripleOnly  {A} _ _ _.
Arguments CC_TripleLeft  {A} _ _ _.
Arguments CC_TripleRight {A} _ _ _.
Arguments CC_CadEmpty    {A}.
Arguments CC_CadSingle   {A} _.
Arguments CC_CadDouble   {A} _ _.
Arguments CC_StoredSmall {A} _.
Arguments CC_StoredBig   {A} _ _ _.

(** ** Cell-kind classification.

    Three disjoint categories: [TripleCell], [CadequeCell], and
    [StoredCell].  Used by the embed/extract pair and the regularity
    invariant on heaps. *)

Inductive CellKind : Type :=
| KCellTriple  : CellKind
| KCellCadeque : CellKind
| KCellStored  : CellKind.

Definition cell_kind {A : Type} (c : CadCell A) : CellKind :=
  match c with
  | CC_TripleOnly  _ _ _
  | CC_TripleLeft  _ _ _
  | CC_TripleRight _ _ _ => KCellTriple
  | CC_CadEmpty
  | CC_CadSingle   _
  | CC_CadDouble   _ _   => KCellCadeque
  | CC_StoredSmall _
  | CC_StoredBig   _ _ _ => KCellStored
  end.

(** ** Sub-pointer projection.

    Returns the list of [Loc]s a cell directly references.  Used to
    state the well-formedness predicate "every [Loc] in a cell is a
    valid key in the heap". *)

Definition cell_subpointers {A : Type} (c : CadCell A) : list Loc :=
  match c with
  | CC_TripleOnly  _ child _
  | CC_TripleLeft  _ child _
  | CC_TripleRight _ child _ => [child]
  | CC_CadEmpty              => []
  | CC_CadSingle   l         => [l]
  | CC_CadDouble   lL lR     => [lL; lR]
  | CC_StoredSmall _         => []
  | CC_StoredBig   _ child _ => [child]
  end.

(** ** Buffer projection.

    Returns the list of [Buf6 A] payloads a cell carries (one for
    Stored Small / Cadeque cells, two for Triple / StoredBig cells). *)

Definition cell_buffers {A : Type} (c : CadCell A) : list (Buf6 A) :=
  match c with
  | CC_TripleOnly  pre _ suf
  | CC_TripleLeft  pre _ suf
  | CC_TripleRight pre _ suf => [pre; suf]
  | CC_CadEmpty
  | CC_CadSingle   _
  | CC_CadDouble   _ _       => []
  | CC_StoredSmall b         => [b]
  | CC_StoredBig   pre _ suf => [pre; suf]
  end.

(** ** Smart-constructor sanity examples. *)

Example cell_kind_TOnly :
  cell_kind (CC_TripleOnly (@buf6_empty nat) 1%positive buf6_empty)
  = KCellTriple.
Proof. reflexivity. Qed.

Example cell_kind_CSingle :
  cell_kind (@CC_CadSingle nat 7%positive) = KCellCadeque.
Proof. reflexivity. Qed.

Example cell_kind_StoredSmall :
  cell_kind (CC_StoredSmall (@buf6_empty nat)) = KCellStored.
Proof. reflexivity. Qed.

Example subpointers_TOnly :
  cell_subpointers (CC_TripleOnly (@buf6_empty nat) 7%positive buf6_empty)
  = [7%positive].
Proof. reflexivity. Qed.

Example subpointers_CDouble :
  cell_subpointers (@CC_CadDouble nat 3%positive 5%positive)
  = [3%positive; 5%positive].
Proof. reflexivity. Qed.

Example subpointers_CEmpty :
  cell_subpointers (@CC_CadEmpty nat) = [].
Proof. reflexivity. Qed.

(** ** Cost note.

    The cell type is fixed-size (ignoring the Buf6 payloads, which
    are themselves bounded at size 6).  An imperative op that
    allocates a constant number of cells therefore does a constant
    amount of work.  This is the structural prerequisite for the WC
    O(1) cost-bound proofs that will land in subsequent Phase 4b
    chunks. *)

(** ** Embed: lay out an abstract [Cadeque A] in the heap.

    Recursively allocates cells bottom-up, returning the [Loc] of
    the root cell and the extended heap.  Termination is structural
    on the [Cadeque] / [Triple] tree.  Allocates one cell per
    [Triple] / [Cadeque] / [Stored] node in the input.

    Note: this version does not yet carry the [adopt6] shortcut and
    does not unfold [Stored] inside [Buf6] payloads (the buffers are
    stored in the parent triple's cell as opaque [Buf6 A] values).
    Both refinements come in subsequent chunks. *)

Fixpoint embed_triple {A : Type} (t : Triple A) (H : Heap (CadCell A))
                    : Loc * Heap (CadCell A) :=
  match t with
  | TOnly  pre c suf =>
      let (lc, H1) := embed_cadeque c H in
      alloc (CC_TripleOnly pre lc suf) H1
  | TLeft  pre c suf =>
      let (lc, H1) := embed_cadeque c H in
      alloc (CC_TripleLeft pre lc suf) H1
  | TRight pre c suf =>
      let (lc, H1) := embed_cadeque c H in
      alloc (CC_TripleRight pre lc suf) H1
  end

with embed_cadeque {A : Type} (q : Cadeque A) (H : Heap (CadCell A))
                 : Loc * Heap (CadCell A) :=
  match q with
  | CEmpty       => alloc CC_CadEmpty H
  | CSingle t    =>
      let (lt, H1) := embed_triple t H in
      alloc (CC_CadSingle lt) H1
  | CDouble tL tR =>
      let (lL, H1) := embed_triple tL H in
      let (lR, H2) := embed_triple tR H1 in
      alloc (CC_CadDouble lL lR) H2
  end.

(** ** Extract: reconstruct an abstract [Cadeque A] by following
    pointers from a root [Loc].

    Termination is non-trivial: the heap is finite but the cell
    graph need not be acyclic in general.  We use a fuel parameter
    [n : nat] that bounds the recursion depth; for any well-formed
    embedding produced by [embed_*], a fuel of [size_of_cad] suffices
    (this is left for a follow-up chunk).

    Returns [None] on out-of-fuel or on a structural mismatch (e.g.
    a Loc that points to a Stored cell where a Cadeque cell was
    expected). *)

Fixpoint extract_cadeque {A : Type} (n : nat) (H : Heap (CadCell A))
                         (l : Loc) : option (Cadeque A) :=
  match n with
  | O => None
  | S n' =>
      match lookup H l with
      | None => None
      | Some CC_CadEmpty       => Some CEmpty
      | Some (CC_CadSingle lt) =>
          match extract_triple n' H lt with
          | Some t => Some (CSingle t)
          | None   => None
          end
      | Some (CC_CadDouble lL lR) =>
          match extract_triple n' H lL with
          | Some tL =>
              match extract_triple n' H lR with
              | Some tR => Some (CDouble tL tR)
              | None    => None
              end
          | None    => None
          end
      | _ => None  (* Triple or Stored cell where Cadeque expected *)
      end
  end

with extract_triple {A : Type} (n : nat) (H : Heap (CadCell A))
                    (l : Loc) : option (Triple A) :=
  match n with
  | O => None
  | S n' =>
      match lookup H l with
      | Some (CC_TripleOnly pre lc suf) =>
          match extract_cadeque n' H lc with
          | Some c => Some (TOnly pre c suf)
          | None   => None
          end
      | Some (CC_TripleLeft pre lc suf) =>
          match extract_cadeque n' H lc with
          | Some c => Some (TLeft pre c suf)
          | None   => None
          end
      | Some (CC_TripleRight pre lc suf) =>
          match extract_cadeque n' H lc with
          | Some c => Some (TRight pre c suf)
          | None   => None
          end
      | _ => None
      end
  end.

(** ** Embed/extract round-trip on the empty cadeque.

    Trivial sanity check: embedding [CEmpty] then extracting from
    the returned root [Loc] in the resulting heap recovers [CEmpty].
    This validates the cell layout for the simplest case; the general
    round-trip theorem is a follow-up chunk (requires alloc /
    persistence machinery). *)

Theorem embed_extract_empty :
  forall (A : Type),
    let (l, H) := embed_cadeque (@CEmpty A) empty_heap in
    extract_cadeque 1 H l = Some CEmpty.
Proof.
  intros A. cbn [embed_cadeque alloc empty_heap].
  cbn [extract_cadeque lookup bindings empty_heap loc_eqb].
  reflexivity.
Qed.
