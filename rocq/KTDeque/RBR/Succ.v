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

(** ** The deferred equivalence/correctness theorem for the two-phase form.

    [Model.v]'s [regular_aux] encodes "every red is discharged by a LATER
    green" (the VWGP Fig. 1 reading).  That invariant admits numbers like
    [Yellow3; Red3; Green3] on which BOTH [succ_rec] and the two-phase
    [succ] mis-carry, and it is NOT preserved by the two-phase form
    (succ [1;1] = [0;2], whose trailing red has no later green).

    KT99 §3's counter discipline is the mirror: a green occurs BEFORE each
    red (scanning from the least significant digit, you must have seen a
    green since the last red before meeting a red).  Under THIS invariant
    the two-phase [succ] is total, value-correct and invariant-preserving —
    the deferred RBR-1 statement for the pointer-motivated form.  The
    full-carry [succ_v2] of [Proofs.v] is correct under both readings. *)

Fixpoint kt_aux (seen_green : bool) (n : number) : Prop :=
  match n with
  | [] => True
  | Green3 :: ds => kt_aux true ds
  | Yellow3 :: ds => kt_aux seen_green ds
  | Red3 :: ds => seen_green = true /\ kt_aux false ds
  end.

Definition kt_regular (n : number) : Prop := kt_aux false n.

Lemma bump_lsd_value :
  forall n, leading_not_red n -> val (bump_lsd n) = val n + 1.
Proof.
  intros [|d ds] Hl; [reflexivity |].
  destruct d; cbn in *; [lia | lia | contradiction].
Qed.

(** Bumping a kt-regular number yields a number that is kt-regular FOR a
    reader who has already seen a green: the freshly-created red (1 -> 2)
    is licensed by the green the carry will deposit in front of it. *)
Lemma bump_kt :
  forall n, kt_regular n -> kt_aux true (bump_lsd n).
Proof.
  intros [|d ds] HJ; [exact I |].
  destruct d; cbn in *.
  - exact HJ.
  - split; [reflexivity | exact HJ].
  - destruct HJ as [Hcontra _]. discriminate.
Qed.

Lemma kt_aux_false_not_red :
  forall n, kt_aux false n -> leading_not_red n.
Proof.
  intros [|d ds] H; [exact I |].
  destruct d; cbn in *; [exact I | exact I |].
  destruct H as [Hcontra _]. discriminate.
Qed.

Lemma regularize_value :
  forall n (b : bool), kt_aux b n -> val (regularize n) = val n.
Proof.
  intros n. induction n as [|d ds IH]; intros b H; [reflexivity |].
  destruct d; cbn in *.
  - reflexivity.
  - rewrite (IH _ H). reflexivity.
  - destruct H as [_ Hds].
    rewrite (bump_lsd_value (kt_aux_false_not_red Hds)). lia.
Qed.

Lemma regularize_regular :
  forall n, kt_aux true n -> kt_regular (regularize n).
Proof.
  intros n. induction n as [|d ds IH]; intros H; [exact I |].
  destruct d; cbn in *.
  - exact H.
  - exact (IH H).
  - destruct H as [_ Hds].
    exact (bump_kt Hds).
Qed.

(** RBR-1 for the two-phase form (kb/spec/algorithms.md §1). *)
Theorem succ_pointer_correct :
  forall n,
    kt_regular n ->
    kt_regular (succ n) /\ val (succ n) = val n + 1.
Proof.
  intros n HJ.
  unfold succ.
  pose proof (bump_kt HJ) as Hb.
  split.
  - exact (regularize_regular Hb).
  - rewrite (regularize_value Hb).
    apply bump_lsd_value.
    apply kt_aux_false_not_red. exact HJ.
Qed.

(** Sanity: the [Y;Y] cascade that distinguishes the invariants. *)
Example succ_three_pointer : succ [Yellow3; Yellow3] = [Green3; Red3].
Proof. reflexivity. Qed.

Example succ_three_pointer_value : val (succ [Yellow3; Yellow3]) = 4.
Proof. reflexivity. Qed.

Example succ_four_pointer :
  succ [Green3; Red3] = [Yellow3; Green3; Yellow3].
Proof. reflexivity. Qed.

Print Assumptions succ_pointer_correct.
