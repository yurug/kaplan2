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
From KTDeque.Cadeque6 Require Import Model OpsAbstract.

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
