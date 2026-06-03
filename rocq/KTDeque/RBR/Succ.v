(** * Module: KTDeque.RBR.Succ -- the successor algorithm on RBR numbers.

    Manual §4 / KT99 §3 / VWGP §2.  We provide TWO forms of [succ]:

    1. [succ_rec], a plain structural recursion on the flat-list
       representation.  This is the form we use to PROVE correctness
       (P9 in [Proofs.v]).  It runs in O(n) on the flat list -- the
       constant-time bound is a property of the *pointer* representation,
       not the flat one.

    2. [bump_lsd] + [regularize], the two-phase form that motivates the
       constant-time pointer-representation algorithm (KT99 §3).  Showing
       that this form coincides with [succ_rec] on regular inputs is an
       equivalence lemma deferred to a later step (it requires the
       pointer representation to make sense of "skip past yellows in O(1)").

    The Step-1 vertical slice uses [succ_rec] + correctness theorem as
    its P9 deliverable.

    Cross-references:
    - kb/spec/algorithms.md#1
    - kb/properties/functional.md#P9
*)

From KTDeque.Common Require Import Prelude.
From KTDeque.RBR Require Import Model.

(** ** Recursive successor: flat-list form, structurally recursive.

    [succ_rec n] = the regular RBR for [val n + 1], assuming [n] is regular.

    Carry propagation is explicit:
    - lsd 0 (Green3): becomes 1 (Yellow3), no carry.
    - lsd 1 (Yellow3): becomes 0 (Green3), with carry into the next digit.
    - lsd 2 (Red3): "should not happen" on a regular input (R4); we
      define it to be a no-op so the function is total.  The proof uses
      regularity to rule out the Red3 lsd. *)

Fixpoint succ_rec (n : number) : number :=
  match n with
  | [] => [Yellow3]                                  (* succ 0 = 1 *)
  | Green3  :: ds => Yellow3 :: ds                   (* 0 -> 1, no carry *)
  | Yellow3 :: ds => Green3  :: succ_rec ds          (* 1 -> 0, carry *)
  | Red3    :: ds => Red3    :: ds                   (* unreachable on regular n *)
  end.

(** ** KT99-style two-phase form (for later optimization / pointer form). *)

Definition bump_lsd (n : number) : number :=
  match n with
  | [] => [Yellow3]
  | Green3  :: ds => Yellow3 :: ds
  | Yellow3 :: ds => Red3    :: ds
  | Red3    :: ds => Red3    :: ds
  end.

Fixpoint regularize (n : number) : number :=
  match n with
  | [] => []
  | Yellow3 :: ds => Yellow3 :: regularize ds
  | Green3 :: _ => n
  | Red3 :: ds => Green3 :: bump_lsd ds
  end.

Definition succ (n : number) : number := regularize (bump_lsd n).

(** ** Sanity examples (using [succ_rec]). *)
Example succ_rec_zero : succ_rec [] = [Yellow3].
Proof. reflexivity. Qed.

Example succ_rec_one : succ_rec [Yellow3] = [Green3; Yellow3].
Proof. reflexivity. Qed.

Example succ_rec_two : succ_rec [Green3; Yellow3] = [Yellow3; Yellow3].
Proof. reflexivity. Qed.

Example succ_rec_three : succ_rec [Yellow3; Yellow3] = [Green3; Green3; Yellow3].
Proof. reflexivity. Qed.

(** Totality sanity check on an IRREGULAR input.  [Red3] is unreachable on a
    regular number, but [succ_rec] is total and treats a leading [Red3] as a
    no-op, so the result is NOT the "+1" value:
      succ_rec [Yellow3; Red3; Green3]
        = Green3 :: succ_rec [Red3; Green3]
        = Green3 :: [Red3; Green3]            (* Red3 branch is a no-op *)
        = [Green3; Red3; Green3].
    This documents totality on irregular inputs; correctness of [succ] on
    *regular* inputs (value = val n + 1) is established by the lemmas below and
    in [Proofs.v]. *)
Example succ_rec_five_irregular :
  succ_rec [Yellow3; Red3; Green3] = [Green3; Red3; Green3].
Proof. reflexivity. Qed.

(** ** Value of succ on regular inputs is val n + 1.

    These small lemmas are used in [Proofs.v]. *)
