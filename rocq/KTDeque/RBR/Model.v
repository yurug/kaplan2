(** * Module: KTDeque.RBR.Model -- Redundant Binary Representation, abstract model.

    Manual §4 / KT99 §3 / VWGP §2.  Digits are 0, 1, 2 (encoded as a [Color3]
    plus the implicit fact that head digits also include 0).  A number is a
    list of digits, least-significant first.  Regularity restricts the
    placement of "2"s (manual §4.1; VWGP Fig. 1).

    This file defines:
    - [Digit3] (alias for [Color3]),
    - [number] = [list Digit3],
    - [val] (mathematical value),
    - [regular] (regularity predicate),
    - decidability via [regular_b].

    The pointer representation (chains of packets) lives in [Pointer.v].

    Cross-references:
    - kb/spec/data-model.md#2.2
    - kb/properties/functional.md#P9
*)

From KTDeque.Common Require Import Prelude.

(** ** Three colors / digits. *)
Inductive Color3 : Type :=
| Green3  : Color3   (* digit 0 *)
| Yellow3 : Color3   (* digit 1 *)
| Red3    : Color3.  (* digit 2 *)

Definition Digit3 : Type := Color3.

Definition digit_value (d : Digit3) : nat :=
  match d with
  | Green3  => 0
  | Yellow3 => 1
  | Red3    => 2
  end.

(** A [number] is a list of digits, *least significant first*.
    VWGP Fig. 1 convention. *)
Definition number : Type := list Digit3.

(** ** Mathematical value: standard base-2 evaluation. *)
Fixpoint val (n : number) : nat :=
  match n with
  | [] => 0
  | d :: ds => digit_value d + 2 * val ds
  end.

(** ** Regularity (KT99 §3 / manual §4 / VWGP §2.1).

    The auxiliary relation tracks whether a [Red3] is "pending" -- meaning a
    [Green3] still owes the carry it started.  Reading least-significant
    first, [Red3] sets pending=true; [Green3] resets pending=false; [Yellow3]
    leaves pending unchanged.  The list is regular iff scanning ends with
    pending=false.

    The empty list is regular only with pending=false.  No constructor for
    [regular_aux true []] exists -- "ended with unresolved Red3" is invalid. *)

Inductive regular_aux : bool -> number -> Prop :=
| reg_nil :
    regular_aux false []
| reg_green :
    forall (p : bool) (ds : number),
      regular_aux false ds -> regular_aux p (Green3 :: ds)
| reg_yellow :
    forall (p : bool) (ds : number),
      regular_aux p ds -> regular_aux p (Yellow3 :: ds)
| reg_red :
    forall (ds : number),
      regular_aux true ds -> regular_aux false (Red3 :: ds).

(** [leading_not_red n]: the leading (least significant) digit, if any,
    is not [Red3].  This encodes VWGP Fig. 1 (R4) / KT99: "the leftmost
    digit of a regular representation cannot be 2." *)
Definition leading_not_red (n : number) : Prop :=
  match n with
  | Red3 :: _ => False
  | _ => True
  end.

(** A number is [regular] iff it satisfies the body invariant (R1-R3 via
    [regular_aux false]) AND the leading-digit invariant (R4). *)
Definition regular (n : number) : Prop :=
  regular_aux false n /\ leading_not_red n.

(** ** Decidable check. *)
Fixpoint regular_aux_b (pending : bool) (n : number) : bool :=
  match n with
  | [] => negb pending
  | Green3  :: ds => regular_aux_b false ds
  | Yellow3 :: ds => regular_aux_b pending ds
  | Red3    :: ds => negb pending && regular_aux_b true ds
  end.

Definition leading_not_red_b (n : number) : bool :=
  match n with
  | Red3 :: _ => false
  | _ => true
  end.

Definition regular_b (n : number) : bool :=
  regular_aux_b false n && leading_not_red_b n.

Lemma regular_aux_b_correct : forall n p,
    regular_aux_b p n = true <-> regular_aux p n.
Proof.
  induction n as [|d ds IH]; intros p; simpl; split.
  - (* [] case, → *)
    destruct p; simpl; intros H; [discriminate | constructor].
  - (* [] case, ← *)
    intros H. inversion H; subst. reflexivity.
  - (* d :: ds, → *)
    destruct d; intros H.
    + (* Green3 *) constructor. apply IH. exact H.
    + (* Yellow3 *) constructor. apply IH. exact H.
    + (* Red3 *) destruct p; simpl in H; [discriminate|].
      constructor. apply IH. exact H.
  - (* d :: ds, ← *)
    destruct d; intros H.
    + (* Green3 *)
      inversion H as [| p' ds' Hrec | |]; subst. apply IH. exact Hrec.
    + (* Yellow3 *)
      inversion H as [| | p' ds' Hrec |]; subst. apply IH. exact Hrec.
    + (* Red3 *)
      inversion H as [| | | ds' Hrec]; subst. simpl.
      apply IH. exact Hrec.
Qed.

Lemma leading_not_red_b_correct : forall n,
    leading_not_red_b n = true <-> leading_not_red n.
Proof.
  intros n. unfold leading_not_red_b, leading_not_red.
  destruct n as [| d ds]; [intuition congruence|].
  destruct d; simpl; intuition congruence.
Qed.

Theorem regular_b_correct : forall n,
    regular_b n = true <-> regular n.
Proof.
  intros n. unfold regular_b, regular. rewrite andb_true_iff.
  rewrite regular_aux_b_correct, leading_not_red_b_correct. reflexivity.
Qed.

(** ** Sanity examples. *)
Example empty_is_regular : regular [].
Proof. split; [constructor | exact I]. Qed.

Example single_green : regular [Green3].
Proof. split; [apply reg_green; constructor | exact I]. Qed.

Example single_yellow : regular [Yellow3].
Proof. split; [apply reg_yellow; constructor | exact I]. Qed.

Example trailing_red_irregular : ~ regular [Red3].
Proof. intros [_ HR4]. exact HR4. Qed.

Example red_then_green_irregular : ~ regular [Red3; Green3].
Proof. intros [_ HR4]. exact HR4. Qed.

Example green_then_red_then_green : regular [Green3; Red3; Green3].
Proof.
  split; [|exact I].
  apply reg_green.
  apply reg_red.
  apply reg_green. constructor.
Qed.

#[export] Hint Constructors Color3 regular_aux : ktdeque.
