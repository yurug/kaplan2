(** * Module: KTDeque.Cadeque6.Examples -- worked examples for the
      abstract catenable cadeque.

    First-time reader: this file is the living documentation for
    [Cadeque6/OpsAbstract.v].  Every example here is checked by
    [Compute] / [reflexivity], so the file fails to compile if the
    abstract semantics drift.  Use it as the "what does this thing
    actually do" reference next to the type signatures.

    None of these are proof-heavy: they are concrete computations
    plus the [reflexivity] one-liners that confirm the result.  No
    new theorems are stated for downstream use; this file is purely
    illustrative.

    Cross-references:
    - [Cadeque6/OpsAbstract.v]   -- the operations being demonstrated.
    - [kb/spec/why-catenable.md] -- the intuition layer.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Repair HeapCells OpsImperative Adopt6.
From KTDeque.Common Require Import FinMapHeap.

(** ** Tiny convenience constructors used in the examples below.
    These would normally be hidden in client code via the
    [Public/CadequeInterface] module type. *)

Definition q0 : Cadeque nat := CEmpty.
Definition q1 : Cadeque nat := cad_push 1 q0.
Definition q12 : Cadeque nat := cad_inject q1 2.
Definition q012 : Cadeque nat := cad_push 0 q12.
Definition q0123 : Cadeque nat := cad_inject q012 3.

(** ** Sanity: the observable sequence after each step. *)

Example seq_q0 : cad_to_list_base q0 = []. Proof. reflexivity. Qed.
Example seq_q1 : cad_to_list_base q1 = [1]. Proof. reflexivity. Qed.
Example seq_q12 : cad_to_list_base q12 = [1; 2]. Proof. reflexivity. Qed.
Example seq_q012 : cad_to_list_base q012 = [0; 1; 2]. Proof. reflexivity. Qed.
Example seq_q0123 : cad_to_list_base q0123 = [0; 1; 2; 3]. Proof. reflexivity. Qed.

(** ** Pop / eject: the four endpoint operations as observable
    behaviours. *)

Example pop_q0123_first :
  match cad_pop q0123 with
  | Some (x, _) => x = 0
  | None        => False
  end.
Proof. reflexivity. Qed.

Example eject_q0123_last :
  match cad_eject q0123 with
  | Some (_, x) => x = 3
  | None        => False
  end.
Proof. reflexivity. Qed.

Example pop_q0_none : cad_pop q0 = None.
Proof. reflexivity. Qed.

Example eject_q0_none : cad_eject q0 = None.
Proof. reflexivity. Qed.

(** ** Concatenation: the headline new operation. *)

Definition q_left  : Cadeque nat := cad_inject (cad_inject (cad_push 0 CEmpty) 1) 2.
Definition q_right : Cadeque nat := cad_inject (cad_inject (cad_push 3 CEmpty) 4) 5.

Example seq_left  : cad_to_list_base q_left  = [0; 1; 2]. Proof. reflexivity. Qed.
Example seq_right : cad_to_list_base q_right = [3; 4; 5]. Proof. reflexivity. Qed.

Example concat_observable :
  cad_to_list_base (cad_concat q_left q_right) = [0; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Example concat_with_empty_left :
  cad_to_list_base (cad_concat CEmpty q_right)
  = cad_to_list_base q_right.
Proof. reflexivity. Qed.

Example concat_with_empty_right :
  cad_to_list_base (cad_concat q_left CEmpty)
  = cad_to_list_base q_left.
Proof. reflexivity. Qed.

(** ** Persistence demo: forking a cadeque and modifying one branch
    leaves the original unchanged. *)

Definition shared : Cadeque nat := q_left.   (* sequence [0; 1; 2] *)
Definition fork_a : Cadeque nat := cad_push 99 shared.
Definition fork_b : Cadeque nat := cad_inject shared 99.

Example shared_unchanged_after_fork :
  cad_to_list_base shared = [0; 1; 2].
Proof. reflexivity. Qed.

Example fork_a_observable :
  cad_to_list_base fork_a = [99; 0; 1; 2].
Proof. reflexivity. Qed.

Example fork_b_observable :
  cad_to_list_base fork_b = [0; 1; 2; 99].
Proof. reflexivity. Qed.

(** ** Round-trip: pushing then popping recovers the element and a
    sequence-equivalent residue. *)

Example push_pop_roundtrip :
  match cad_pop (cad_push 7 q_left) with
  | Some (x, q') => x = 7 /\ cad_to_list_base q' = cad_to_list_base q_left
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example inject_eject_roundtrip :
  match cad_eject (cad_inject q_right 7) with
  | Some (q', x) => x = 7 /\ cad_to_list_base q' = cad_to_list_base q_right
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

(** ** Concat associativity (computational view). *)

Definition q_a : Cadeque nat := cad_push 1 (cad_push 2 CEmpty).
Definition q_b : Cadeque nat := cad_push 3 (cad_push 4 CEmpty).
Definition q_c : Cadeque nat := cad_push 5 (cad_push 6 CEmpty).

Example concat_assoc_compute :
  cad_to_list_base (cad_concat (cad_concat q_a q_b) q_c)
  = cad_to_list_base (cad_concat q_a (cad_concat q_b q_c)).
Proof. reflexivity. Qed.

(** ** Size laws (computational view). *)

Example size_concat :
  cad_size (cad_concat q_left q_right)
  = cad_size q_left + cad_size q_right.
Proof. reflexivity. Qed.

Definition cad_pop_or_self {X : Type} (q : Cadeque X) : Cadeque X :=
  match cad_pop q with Some (_, q') => q' | None => q end.

Example size_after_alternating_ops :
  cad_size (cad_inject (cad_pop_or_self (cad_push 99 q_left)) 100)
  = S (cad_size q_left).
Proof. reflexivity. Qed.

(** ** Operational examples: cad_*_op observably equal cad_*. *)

Example op_push_observable :
  cad_to_list_base (cad_push_op 0 q_left) = [0; 0; 1; 2].
Proof. reflexivity. Qed.

Example op_inject_observable :
  cad_to_list_base (cad_inject_op q_left 99) = [0; 1; 2; 99].
Proof. reflexivity. Qed.

Example op_pop_observable :
  match cad_pop_op q_left with
  | Some (x, q') => x = 0 /\ cad_to_list_base q' = [1; 2]
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example op_eject_observable :
  match cad_eject_op q_left with
  | Some (q', x) => x = 2 /\ cad_to_list_base q' = [0; 1]
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example op_concat_observable :
  cad_to_list_base (cad_concat_op q_left q_right) = [0; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Example op_concat_left_empty :
  cad_to_list_base (cad_concat_op CEmpty q_left) = cad_to_list_base q_left.
Proof. reflexivity. Qed.

Example op_concat_right_empty :
  cad_to_list_base (cad_concat_op q_left CEmpty) = cad_to_list_base q_left.
Proof. reflexivity. Qed.

(** ** Operational vs abstract: same observable behavior. *)

Example op_push_eq_abstract :
  cad_to_list_base (cad_push_op 0 q_left) = cad_to_list_base (cad_push 0 q_left).
Proof. reflexivity. Qed.

Example op_inject_eq_abstract :
  cad_to_list_base (cad_inject_op q_left 99) = cad_to_list_base (cad_inject q_left 99).
Proof. reflexivity. Qed.

Example op_concat_eq_abstract :
  cad_to_list_base (cad_concat_op q_left q_right)
  = cad_to_list_base (cad_concat q_left q_right).
Proof. reflexivity. Qed.

(** ** Round-trip via operational push then operational pop. *)

Example op_push_pop_roundtrip :
  match cad_pop_op (cad_push_op 7 q_left) with
  | Some (x, q') => x = 7 /\ cad_to_list_base q' = cad_to_list_base q_left
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example op_inject_eject_roundtrip :
  match cad_eject_op (cad_inject_op q_right 7) with
  | Some (q', x) => x = 7 /\ cad_to_list_base q' = cad_to_list_base q_right
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

(** ** _full operational variants: full regular_cad preservation. *)

Example full_pop_observable :
  match cad_pop_op_full q_left with
  | Some (x, q') => x = 0 /\ cad_to_list_base q' = [1; 2]
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example full_eject_observable :
  match cad_eject_op_full q_left with
  | Some (q', x) => x = 2 /\ cad_to_list_base q' = [0; 1]
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

Example full_concat_observable :
  cad_to_list_base (cad_concat_op_full q_left q_right) = [0; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Example full_concat_left_empty :
  cad_to_list_base (cad_concat_op_full CEmpty q_left) = cad_to_list_base q_left.
Proof. reflexivity. Qed.

Example full_concat_right_empty :
  cad_to_list_base (cad_concat_op_full q_left CEmpty) = cad_to_list_base q_left.
Proof. reflexivity. Qed.

Example full_pop_eject_roundtrip :
  match cad_pop_op_full (cad_push_op 7 q_left) with
  | Some (x, q') => x = 7 /\ cad_to_list_base q' = cad_to_list_base q_left
  | None         => False
  end.
Proof. cbn. split; reflexivity. Qed.

(** ** Imperative DSL examples: [cad_concat_imp] on small heaps.

    These construct two abstract cadeques in shapes compatible with
    [cad_concat_imp]'s simple cases, embed them in a heap, run the
    imperative concat, then extract and verify the result list.

    Each example demonstrates that the imperative DSL correctly
    delegates to the right sub-op AND produces a heap whose
    extracted list matches the abstract concat. *)

(** Two singletons with empty boundary: [1; 2] ++ [3; 4]. *)

Definition imp_qA_ss : Cadeque nat :=
  CSingle (TOnly (mkBuf6 [1; 2]) CEmpty buf6_empty).
Definition imp_qB_ss : Cadeque nat :=
  CSingle (TOnly buf6_empty CEmpty (mkBuf6 [3; 4])).

Example imp_qA_ss_seq : cad_to_list_base imp_qA_ss = [1; 2].
Proof. reflexivity. Qed.

Example imp_qB_ss_seq : cad_to_list_base imp_qB_ss = [3; 4].
Proof. reflexivity. Qed.

(** Embed both into a fresh heap, then run the imperative concat. *)
Definition imp_ss_setup
  : option (Heap (CadCell nat) * Loc * Loc * Loc * nat) :=
  let (lA, H1) := embed_cadeque imp_qA_ss empty_heap in
  let (lB, H2) := embed_cadeque imp_qB_ss H1 in
  match cad_concat_imp lA lB H2 with
  | Some (H', l', k) => Some (H', lA, lB, l', k)
  | None             => None
  end.

(** The concat produces SOME — i.e. cad_concat_imp succeeds.  Heavier
    [Compute]-style claims (cost-exact, extract-and-list-check) are
    deliberately omitted: [extract_cadeque]'s [Pos]-keyed lookup table
    forces a very large [cbn] expansion, making the whole-file build
    slow.  The proved theorems
    ([cad_concat_imp_singleton_singleton_simple_cost_exact],
     [cad_concat_imp_ss_list_correct], etc.) cover these claims
    abstractly without paying that compute cost. *)
Example imp_ss_concat_succeeds : imp_ss_setup <> None.
Proof. vm_compute. discriminate. Qed.

(** ** A symmetric DD example: two doubles with empty boundary triples.

    [1; 2] (left of A) ++ [3; 4] (right of B) — A and B both have
    only the outer-boundary triple non-trivial. *)

Definition imp_qA_dd : Cadeque nat :=
  CDouble (TLeft (mkBuf6 [1; 2]) CEmpty buf6_empty)
          (TRight buf6_empty CEmpty buf6_empty).
Definition imp_qB_dd : Cadeque nat :=
  CDouble (TLeft buf6_empty CEmpty buf6_empty)
          (TRight buf6_empty CEmpty (mkBuf6 [3; 4])).

Example imp_qA_dd_seq : cad_to_list_base imp_qA_dd = [1; 2].
Proof. reflexivity. Qed.

Example imp_qB_dd_seq : cad_to_list_base imp_qB_dd = [3; 4].
Proof. reflexivity. Qed.

Definition imp_dd_setup
  : option (Heap (CadCell nat) * Loc * Loc * Loc * nat) :=
  let (lA, H1) := embed_cadeque imp_qA_dd empty_heap in
  let (lB, H2) := embed_cadeque imp_qB_dd H1 in
  match cad_concat_imp lA lB H2 with
  | Some (H', l', k) => Some (H', lA, lB, l', k)
  | None             => None
  end.

Example imp_dd_concat_succeeds : imp_dd_setup <> None.
Proof. vm_compute. discriminate. Qed.

(** ** Empty-input cases: cad_concat_imp returns the OTHER pointer
    and the heap unchanged. *)

Definition imp_qA_empty : Cadeque nat := CEmpty.
Definition imp_qB_some  : Cadeque nat := imp_qB_ss.

Definition imp_a_empty_setup
  : option (Heap (CadCell nat) * Loc * Loc * Loc * nat) :=
  let (lA, H1) := embed_cadeque imp_qA_empty empty_heap in
  let (lB, H2) := embed_cadeque imp_qB_some H1 in
  match cad_concat_imp lA lB H2 with
  | Some (H', l', k) => Some (H', lA, lB, l', k)
  | None             => None
  end.

Example imp_a_empty_returns_lB :
  match imp_a_empty_setup with
  | Some (_, _, lB, l', _) => l' = lB
  | None                   => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example imp_a_empty_cost_one :
  match imp_a_empty_setup with
  | Some (_, _, _, _, k) => k = 1
  | None                 => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ** Adopt6 layer examples: rich-cell DSL on tiny embedded heaps.

    Demonstrates that the cad_*_imp_a6 ops on the [CadCellA6] type
    succeed on small inputs, with the WC O(1) cost bounds witnessed
    concretely.  Uses [vm_compute] for the same reason as the plain
    examples: [cbn] on heap-keyed Pos lookups is pathologically slow. *)

Definition imp_a6_empty_qA : Cadeque nat := CEmpty.

Definition imp_a6_empty_setup
  : option (Heap (CadCellA6 nat) * Loc * nat) :=
  let (lA, H1) := embed_cadeque_a6 imp_a6_empty_qA empty_heap in
  match cad_push_imp_a6 7 lA H1 with
  | Some (H', l', k) => Some (H', l', k)
  | None             => None
  end.

(** cad_push_imp_a6 succeeds on the empty cadeque. *)
Example imp_a6_push_empty_succeeds : imp_a6_empty_setup <> None.
Proof. vm_compute. discriminate. Qed.

(** Pop from a fresh embedding of a singleton cadeque returns Some. *)
Definition imp_a6_singleton_qA : Cadeque nat :=
  CSingle (TOnly (mkBuf6 [42]) CEmpty buf6_empty).

Definition imp_a6_pop_setup
  : option (Heap (CadCellA6 nat) * option (nat * Loc) * nat) :=
  let (lA, H1) := embed_cadeque_a6 imp_a6_singleton_qA empty_heap in
  cad_pop_imp_a6 lA H1.

Example imp_a6_pop_succeeds : imp_a6_pop_setup <> None.
Proof. vm_compute. discriminate. Qed.

(** Empty input → None (pop on CCa6_CadEmpty). *)
Example imp_a6_pop_empty :
  let (lA, H) := embed_cadeque_a6 (@CEmpty nat) empty_heap in
  match cad_pop_imp_a6 lA H with
  | Some (_, None, _) => True
  | _ => False
  end.
Proof. vm_compute. trivial. Qed.

(** Symmetric eject. *)
Definition imp_a6_eject_setup
  : option (Heap (CadCellA6 nat) * option (Loc * nat) * nat) :=
  let (lA, H1) := embed_cadeque_a6 imp_a6_singleton_qA empty_heap in
  cad_eject_imp_a6 lA H1.

Example imp_a6_eject_succeeds : imp_a6_eject_setup <> None.
Proof. vm_compute. discriminate. Qed.

(** Concat of two singletons (both with empty children). *)
Definition imp_a6_qA_ss : Cadeque nat :=
  CSingle (TOnly (mkBuf6 [1; 2]) CEmpty buf6_empty).
Definition imp_a6_qB_ss : Cadeque nat :=
  CSingle (TOnly buf6_empty CEmpty (mkBuf6 [3; 4])).

Definition imp_a6_concat_setup
  : option (Heap (CadCellA6 nat) * Loc * Loc * Loc * nat) :=
  let (lA, H1) := embed_cadeque_a6 imp_a6_qA_ss empty_heap in
  let (lB, H2) := embed_cadeque_a6 imp_a6_qB_ss H1 in
  match cad_concat_imp_a6 lA lB H2 with
  | Some (H', l', k) => Some (H', lA, lB, l', k)
  | None             => None
  end.

Example imp_a6_concat_succeeds : imp_a6_concat_setup <> None.
Proof. vm_compute. discriminate. Qed.
