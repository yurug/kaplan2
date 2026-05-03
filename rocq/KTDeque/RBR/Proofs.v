(** * Module: KTDeque.RBR.Proofs -- P9: succ correctness.

    Proves [Theorem RBR_1] (manual ticket-01 gate / functional.md P9):

      regular n -> regular (succ_v2 n) /\ val (succ_v2 n) = val n + 1.

    Strategy:
    - prove [succ_v2_value]: value increments by 1 unconditionally;
    - prove [succ_v2_body]: body invariant [regular_aux false] preserved
      (lifting [regular_aux true] to [regular_aux false] for the Red3 case);
    - prove [succ_v2_leading_not_red]: output never starts with Red3;
    - bundle as [succ_correct].

    The two-phase [bump_lsd] / [regularize] form in [Succ.v] is an
    optimization equivalence; its correspondence with [succ_v2] is
    deferred to a later step (it depends on the pointer representation
    to make sense of "skip yellows in O(1)").

    Cross-references:
    - kb/spec/algorithms.md#1
    - kb/properties/functional.md#P9
*)

From KTDeque.Common Require Import Prelude.
From KTDeque.RBR Require Import Model Succ.

(** ** [succ_v2]: a recursive successor for proof.

    Carry rules:
    - [] -> [Yellow3]: 0 + 1 = 1.
    - Green3 (digit 0) :: ds -> Yellow3 :: ds: 0 + 2X + 1 = 1 + 2X.
    - Yellow3 (digit 1) :: ds -> Green3 :: succ_v2 ds: 1 + 2X + 1 = 0 + 2(X+1).
    - Red3 (digit 2) :: ds -> Yellow3 :: succ_v2 ds: 2 + 2X + 1 = 1 + 2(X+1).

    The Red3 case is reachable on any input but irrelevant for [regular n]
    (where R4 forbids leading Red3).  Defining it correctly anyway keeps
    [succ_v2] total and the proofs uniform. *)

Fixpoint succ_v2 (n : number) : number :=
  match n with
  | [] => [Yellow3]
  | Green3  :: ds => Yellow3 :: ds
  | Yellow3 :: ds => Green3  :: succ_v2 ds
  | Red3    :: ds => Yellow3 :: succ_v2 ds
  end.

(** ** Step 1: value increments by 1 (unconditionally). *)
Lemma succ_v2_value : forall n,
    val (succ_v2 n) = val n + 1.
Proof.
  induction n as [|d ds IH]; cbn; [reflexivity|].
  destruct d; cbn; rewrite ?IH; lia.
Qed.

(** ** Step 2: lifting between pending states.

    [regular_aux true ds] implies [regular_aux false ds].  The reverse is
    false in general (e.g., [regular_aux false []] holds via [reg_nil] but
    [regular_aux true []] has no constructor; or [regular_aux false (Red3 :: ds)]
    holds via [reg_red] but [regular_aux true (Red3 :: ds)] doesn't).

    The forward direction holds because the only constructors that produce
    [regular_aux true ...] are [reg_green] and [reg_yellow], both of which
    have a [reg_aux false] counterpart with the same recursive premise. *)

Lemma regular_aux_pending_to_clean : forall ds,
    regular_aux true ds -> regular_aux false ds.
Proof.
  intros ds H.
  remember true as p eqn:Hp.
  induction H as [|p' ds' Hbody IH'|p' ds' Hbody IH'|ds' Hbody IH'];
    try discriminate Hp.
  - apply reg_green. exact Hbody.
  - apply reg_yellow. apply IH'. exact Hp.
Qed.

(** ** Step 3: body invariant preserved by [succ_v2].

    For each constructor of [regular_aux false n], show that [succ_v2 n]
    is also [regular_aux false]. *)

Lemma succ_v2_body : forall n,
    regular_aux false n -> regular_aux false (succ_v2 n).
Proof.
  induction n as [|d ds IH]; intros Hbody.
  - cbn. apply reg_yellow. constructor.
  - destruct d; cbn.
    + (* Green3 :: ds -> Yellow3 :: ds *)
      inversion Hbody as [| p' ds' Hrec | |]; subst.
      apply reg_yellow. exact Hrec.
    + (* Yellow3 :: ds -> Green3 :: succ_v2 ds *)
      inversion Hbody as [| | p' ds' Hrec |]; subst.
      apply reg_green. apply IH. exact Hrec.
    + (* Red3 :: ds -> Yellow3 :: succ_v2 ds *)
      inversion Hbody as [| | | ds' Hrec]; subst.
      apply reg_yellow. apply IH.
      apply regular_aux_pending_to_clean. exact Hrec.
Qed.

(** ** Step 4: output is leading-not-red. *)
Lemma succ_v2_leading_not_red : forall n,
    leading_not_red (succ_v2 n).
Proof.
  intros n.
  destruct n as [|d ds]; [cbn; exact I|].
  destruct d; cbn; exact I.
Qed.

(** ** Step 5: regularity preserved. *)
Lemma succ_v2_regular : forall n,
    regular n -> regular (succ_v2 n).
Proof.
  intros n [Hbody _].
  split.
  - apply succ_v2_body. exact Hbody.
  - apply succ_v2_leading_not_red.
Qed.

(** ** Main theorem (P9). *)
Theorem succ_correct : forall n,
    regular n ->
    regular (succ_v2 n) /\ val (succ_v2 n) = val n + 1.
Proof.
  intros n Hreg. split.
  - apply succ_v2_regular. exact Hreg.
  - apply succ_v2_value.
Qed.

(** ** Sanity. *)
Example succ_v2_zero_value : val (succ_v2 []) = 1.
Proof. reflexivity. Qed.

Example succ_v2_three_value : val (succ_v2 [Yellow3; Yellow3]) = 4.
Proof. reflexivity. Qed.

Example succ_v2_three_regular : regular (succ_v2 [Yellow3; Yellow3]).
Proof.
  apply succ_v2_regular. split.
  - apply reg_yellow, reg_yellow, reg_nil.
  - exact I.
Qed.

(** ** Alignment of succ_v2 with the pointer-form succ in [Succ.v].

    [Succ.v] also defines [succ := regularize ∘ bump_lsd] for the
    constant-time pointer-representation algorithm.  Showing that the two
    coincide on [regular] inputs is a separate equivalence theorem,
    deferred until the pointer representation is fully exercised in the
    Section-4 / Section-6 layers (Step 2+).  For Step 1 (P9), the
    recursive [succ_v2] is sufficient. *)
