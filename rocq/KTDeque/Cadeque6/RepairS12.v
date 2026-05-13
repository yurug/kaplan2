(** * Module: KTDeque.Cadeque6.RepairS12 — §12.4 repair cases (abstract).

    The five repair cases (1a, 1b, 2a, 2b, 2c) from execution manual
    §12.4 / KT99 §6.2, applied after [cad_pop_op] / [cad_eject_op]
    has produced a structure whose preferred-path tail is red.

    This file gives the **abstract** rewriting functions and their
    sequence-preservation laws.  The operational/heap variant on the
    rich [CadCellA6] type lives in [Cadeque6/Adopt6.v].

    ## Notation

    - [u = TLeft  p1 d1 s1] (Case 1) or [u = TOnly p1 d1 s1] (Case 2).
    - [(p2, d2, s2)] is the first stored triple popped from [d1],
      with [d1'] the residue.  In Case 2c's two-sided sub-case the
      last stored triple [(p3, d3, s3)] is also ejected from [d1'],
      with [d1''] the residue.

    Because the extrinsic typed model collapses the "child has
    [Stored X] elements" discipline (see [Model.v] design note 1),
    the repair-case functions here take the popped/ejected pieces'
    **concrete buffer contents** as auxiliary list arguments rather
    than as destructured [Stored] values.  This keeps the abstract
    layer typecheckable while preserving the sequence semantics.

    The operational layer on [CadCellA6] does the real destructuring
    via [CCa6_StoredSmall] / [CCa6_StoredBig].

    ## Cross-references

    - [kb/spec/section12.4-repair-cases.md] — verbatim spec.
    - [Cadeque6/Repair.v]                   — abstract pop/eject_op.
    - [Cadeque6/Adopt6.v]                   — operational §12.4.
    - [kb/execution-manual-v3.md] §12.4     — paper text.
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Repair Color.

(** ** Helper: [cad_to_list] of [cad_from_list] is identity. *)

Lemma cad_from_list_to_list :
  forall (X : Type) (xs : list X),
    cad_to_list (fun y : X => [y]) (cad_from_list xs) = xs.
Proof.
  intros X xs.
  change (cad_to_list (fun y : X => [y]) (cad_from_list xs))
    with (cad_to_list_base (cad_from_list xs)).
  apply cad_from_list_seq.
Qed.

(** Helper: TLeft / TOnly / TRight flattening, with explicit buffer
    forms and an empty child. *)

Lemma triple_left_flatten :
  forall (X : Type) (xs : list X) (d : Cadeque X) (ys : list X),
    triple_to_list (fun y => [y]) (TLeft (mkBuf6 xs) d (mkBuf6 ys))
    = xs ++ cad_to_list (fun y => [y]) d ++ ys.
Proof.
  intros X xs d ys.
  rewrite triple_to_list_left.
  unfold buf6_flatten, buf6_elems.
  rewrite !flat_concat_singleton_id.
  reflexivity.
Qed.

Lemma triple_right_flatten :
  forall (X : Type) (xs : list X) (d : Cadeque X) (ys : list X),
    triple_to_list (fun y => [y]) (TRight (mkBuf6 xs) d (mkBuf6 ys))
    = xs ++ cad_to_list (fun y => [y]) d ++ ys.
Proof.
  intros X xs d ys.
  rewrite triple_to_list_right.
  unfold buf6_flatten, buf6_elems.
  rewrite !flat_concat_singleton_id.
  reflexivity.
Qed.

Lemma triple_only_flatten :
  forall (X : Type) (xs : list X) (d : Cadeque X) (ys : list X),
    triple_to_list (fun y => [y]) (TOnly (mkBuf6 xs) d (mkBuf6 ys))
    = xs ++ cad_to_list (fun y => [y]) d ++ ys.
Proof.
  intros X xs d ys.
  rewrite triple_to_list_only.
  unfold buf6_flatten, buf6_elems.
  rewrite !flat_concat_singleton_id.
  reflexivity.
Qed.

(** Helper: rewrite [Buf6 X] as [mkBuf6 (buf6_elems _)]. *)

Lemma buf6_eta :
  forall (X : Type) (b : Buf6 X), b = mkBuf6 (buf6_elems b).
Proof.
  intros X [xs]. reflexivity.
Qed.

(** ** Case 1a: u = TLeft p1 d1 s1, p2 ≠ ∅ ∧ s2 ≠ ∅.

    Result triple: [TLeft p2' d3 s1] where
    - [p2' = buf6_concat p1 (mkBuf6 p2)] (concatenate p1 and p2)
    - [d3] is the (level-deeper) cadeque [cad_concat d2 d1''],
      where d1'' is d1' with the stored s2 pushed onto it.

    At the abstract layer we represent [d3] as a [Cadeque X] passed
    in by the caller, with its element list [d3_xs] required to
    equal [d2_xs ++ s2 ++ d1'_xs] (the contents the operational
    repair would assemble).  The seq lemma then witnesses the
    sequence correctness.
*)

Definition repair_case_1a_left {X : Type}
    (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X)
    : Triple X :=
  TLeft (mkBuf6 (buf6_elems p1 ++ p2)) d3 s1.

Lemma repair_case_1a_left_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_1a_left p1 s1 p2 d3)
    = buf6_to_list p1 ++ p2 ++ cad_to_list (fun y => [y]) d3
      ++ buf6_to_list s1.
Proof.
  intros X p1 s1 p2 d3.
  unfold repair_case_1a_left.
  rewrite (buf6_eta X s1) at 1.
  rewrite triple_left_flatten.
  unfold buf6_to_list at 1.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Case 1b: u = TLeft p1 d1 s1, one of p2 / s2 empty.

    The popped stored is small.  Merge all of p1, popped, into one
    prefix buffer.  Result: [TLeft p3 d1' s1]. *)

Definition repair_case_1b_left {X : Type}
    (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X)
    : Triple X :=
  TLeft (mkBuf6 (buf6_elems p1 ++ popped_xs)) d1' s1.

Lemma repair_case_1b_left_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_1b_left p1 s1 popped_xs d1')
    = buf6_to_list p1 ++ popped_xs ++ cad_to_list (fun y => [y]) d1'
      ++ buf6_to_list s1.
Proof.
  intros X p1 s1 popped_xs d1'.
  unfold repair_case_1b_left.
  rewrite (buf6_eta X s1) at 1.
  rewrite triple_left_flatten.
  unfold buf6_to_list at 1.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Case 2a: u = TOnly p1 d1 s1, |s1| ≥ 8.

    Same machinery as Case 1a but result is [TOnly]. *)

Definition repair_case_2a_only {X : Type}
    (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X)
    : Triple X :=
  TOnly (mkBuf6 (buf6_elems p1 ++ p2)) d3 s1.

Lemma repair_case_2a_only_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_2a_only p1 s1 p2 d3)
    = buf6_to_list p1 ++ p2 ++ cad_to_list (fun y => [y]) d3
      ++ buf6_to_list s1.
Proof.
  intros X p1 s1 p2 d3.
  unfold repair_case_2a_only.
  rewrite (buf6_eta X s1) at 1.
  rewrite triple_only_flatten.
  unfold buf6_to_list at 1.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Case 2b: u = TOnly p1 d1 s1, |p1| ≥ 8.

    Symmetric to 2a; the result has the merged buffer on the right. *)

Definition repair_case_2b_only {X : Type}
    (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X)
    : Triple X :=
  TOnly p1 d3 (mkBuf6 (s3 ++ buf6_elems s1)).

Lemma repair_case_2b_only_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_2b_only p1 s1 s3 d3)
    = buf6_to_list p1 ++ cad_to_list (fun y => [y]) d3
      ++ s3 ++ buf6_to_list s1.
Proof.
  intros X p1 s1 s3 d3.
  unfold repair_case_2b_only.
  rewrite (buf6_eta X p1) at 1.
  rewrite triple_only_flatten.
  unfold buf6_to_list at 2.
  reflexivity.
Qed.

(** ** Case 2c-empty: u = TOnly p1 d1 s1, |p1|≤7 ∧ |s1|≤7, d1' empty.

    Merge p1 with p2 and s2 with s1; child becomes d2. *)

Definition repair_case_2c_only_empty {X : Type}
    (p1 s1 : Buf6 X) (p2 s2 : list X) (d2 : Cadeque X)
    : Triple X :=
  TOnly (mkBuf6 (buf6_elems p1 ++ p2))
        d2
        (mkBuf6 (s2 ++ buf6_elems s1)).

Lemma repair_case_2c_only_empty_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 s2 : list X) (d2 : Cadeque X),
    triple_to_list (fun y => [y])
      (repair_case_2c_only_empty p1 s1 p2 s2 d2)
    = buf6_to_list p1 ++ p2
      ++ cad_to_list (fun y => [y]) d2
      ++ s2 ++ buf6_to_list s1.
Proof.
  intros X p1 s1 p2 s2 d2.
  unfold repair_case_2c_only_empty.
  rewrite triple_only_flatten.
  unfold buf6_to_list.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Case 2c-twosided: u = TOnly p1 d1 s1, |p1|≤7 ∧ |s1|≤7, d1' non-empty.

    Pop head (p2,d2,s2) AND eject tail (p3,d3,s3) from d1.  Repair
    both sides independently.  Each side independently picks
    "merge" (buffer collapse when one side is empty) or "stored"
    (push/inject a stored, leave the outer buffers).

    At the abstract layer we expose the result as a TOnly with the
    caller's chosen [p_left] / [s_right] / [child] composition. *)

Definition repair_case_2c_only_twosided {X : Type}
    (p1 s1 : Buf6 X) (p_left : list X) (s_right : list X) (child : Cadeque X)
    : Triple X :=
  TOnly (mkBuf6 (buf6_elems p1 ++ p_left))
        child
        (mkBuf6 (s_right ++ buf6_elems s1)).

Lemma repair_case_2c_only_twosided_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (p_left s_right : list X) (child : Cadeque X),
    triple_to_list (fun y => [y])
      (repair_case_2c_only_twosided p1 s1 p_left s_right child)
    = buf6_to_list p1 ++ p_left
      ++ cad_to_list (fun y => [y]) child
      ++ s_right ++ buf6_to_list s1.
Proof.
  intros X p1 s1 p_left s_right child.
  unfold repair_case_2c_only_twosided.
  rewrite triple_only_flatten.
  unfold buf6_to_list.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Symmetric eject (right-side) cases.

    Each pop case has a mirror eject case obtained by swapping
    left ↔ right.  Below: 1a-right, 1b-right, 2a-right, 2b-right,
    2c-right-empty, 2c-right-twosided.
*)

Definition repair_case_1a_right {X : Type}
    (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X)
    : Triple X :=
  TRight p1 d3 (mkBuf6 (s3 ++ buf6_elems s1)).

Lemma repair_case_1a_right_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_1a_right p1 s1 s3 d3)
    = buf6_to_list p1 ++ cad_to_list (fun y => [y]) d3
      ++ s3 ++ buf6_to_list s1.
Proof.
  intros X p1 s1 s3 d3.
  unfold repair_case_1a_right.
  rewrite (buf6_eta X p1) at 1.
  rewrite triple_right_flatten.
  unfold buf6_to_list at 2.
  reflexivity.
Qed.

Definition repair_case_1b_right {X : Type}
    (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X)
    : Triple X :=
  TRight p1 d1' (mkBuf6 (popped_xs ++ buf6_elems s1)).

Lemma repair_case_1b_right_seq :
  forall (X : Type) (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X),
    triple_to_list (fun y => [y]) (repair_case_1b_right p1 s1 popped_xs d1')
    = buf6_to_list p1 ++ cad_to_list (fun y => [y]) d1'
      ++ popped_xs ++ buf6_to_list s1.
Proof.
  intros X p1 s1 popped_xs d1'.
  unfold repair_case_1b_right.
  rewrite (buf6_eta X p1) at 1.
  rewrite triple_right_flatten.
  unfold buf6_to_list at 2.
  reflexivity.
Qed.

(** ** Dispatch tag for the abstract repair. *)

Inductive repair_case_tag : Type :=
| RC_1a
| RC_1b
| RC_2a
| RC_2b
| RC_2c_empty
| RC_2c_twosided.

(** ** Regularity preservation: §12.4 cases produce Green4 triples.

    Each repair case is *designed* to produce a green replacement
    for the red tail.  Formally: under per-case size hypotheses on
    the merged buffers, the result has [triple_color = Green4].

    The size hypotheses encode the KT99 invariant: when §12.4
    applies, the buffers being merged are large enough that the
    result lands in the "green" size range (≥ 8 or = 0..4). *)

(** Helper: when a buffer has 8+ elements, its colour is Green4. *)

Lemma buf6_color_green_of_large :
  forall (X : Type) (b : Buf6 X),
    buf6_size b >= 8 ->
    buf6_color b = Green4.
Proof.
  intros X b H8.
  unfold buf6_color.
  destruct (buf6_size b) as [|n] eqn:Hsize; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [lia|].
  destruct n; [lia|].
  destruct n; [lia|].
  reflexivity.
Qed.

(** Helper: when a buffer has 0..4 elements, its colour is also Green4
    (the "very small" range — outside Red/Orange/Yellow). *)

Lemma buf6_color_green_of_small :
  forall (X : Type) (b : Buf6 X),
    buf6_size b <= 4 ->
    buf6_color b = Green4.
Proof.
  intros X b H4.
  unfold buf6_color.
  destruct (buf6_size b) as [|n] eqn:Hsize; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  destruct n; [reflexivity|].
  lia.
Qed.

(** Case 1b-left: result is Green4 if either the child is empty
    or the merged prefix is large (≥ 8). *)

Theorem repair_case_1b_left_green :
  forall (X : Type) (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X),
    (d1' = CEmpty \/ length (buf6_elems p1 ++ popped_xs) >= 8) ->
    triple_color (repair_case_1b_left p1 s1 popped_xs d1') = Green4.
Proof.
  intros X p1 s1 popped_xs d1' Hcase.
  unfold repair_case_1b_left, triple_color.
  destruct Hcase as [Hempty|Hlarge].
  - subst d1'. reflexivity.
  - destruct d1' as [|t|tL tR]; [reflexivity| |];
    rewrite buf6_color_green_of_large;
      [reflexivity|unfold buf6_size, buf6_elems; exact Hlarge
       |reflexivity|unfold buf6_size, buf6_elems; exact Hlarge].
Qed.

(** Case 1b-right: symmetric, Green4 if child is empty or merged suffix is large. *)

Theorem repair_case_1b_right_green :
  forall (X : Type) (p1 s1 : Buf6 X) (popped_xs : list X) (d1' : Cadeque X),
    (d1' = CEmpty \/ length (popped_xs ++ buf6_elems s1) >= 8) ->
    triple_color (repair_case_1b_right p1 s1 popped_xs d1') = Green4.
Proof.
  intros X p1 s1 popped_xs d1' Hcase.
  unfold repair_case_1b_right, triple_color.
  destruct Hcase as [Hempty|Hlarge].
  - subst d1'. reflexivity.
  - destruct d1' as [|t|tL tR]; [reflexivity| |];
    rewrite buf6_color_green_of_large;
      [reflexivity|unfold buf6_size, buf6_elems; exact Hlarge
       |reflexivity|unfold buf6_size, buf6_elems; exact Hlarge].
Qed.

(** Case 1a-left: result is TLeft.  Green4 under same conditions. *)

Theorem repair_case_1a_left_green :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X),
    (d3 = CEmpty \/ length (buf6_elems p1 ++ p2) >= 8) ->
    triple_color (repair_case_1a_left p1 s1 p2 d3) = Green4.
Proof.
  intros X p1 s1 p2 d3 Hcase.
  unfold repair_case_1a_left, triple_color.
  destruct Hcase as [Hempty|Hlarge].
  - subst d3. reflexivity.
  - destruct d3 as [|t|tL tR]; [reflexivity| |];
    rewrite buf6_color_green_of_large;
      [reflexivity|unfold buf6_size, buf6_elems; exact Hlarge
       |reflexivity|unfold buf6_size, buf6_elems; exact Hlarge].
Qed.

Theorem repair_case_1a_right_green :
  forall (X : Type) (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X),
    (d3 = CEmpty \/ length (s3 ++ buf6_elems s1) >= 8) ->
    triple_color (repair_case_1a_right p1 s1 s3 d3) = Green4.
Proof.
  intros X p1 s1 s3 d3 Hcase.
  unfold repair_case_1a_right, triple_color.
  destruct Hcase as [Hempty|Hlarge].
  - subst d3. reflexivity.
  - destruct d3 as [|t|tL tR]; [reflexivity| |];
    rewrite buf6_color_green_of_large;
      [reflexivity|unfold buf6_size, buf6_elems; exact Hlarge
       |reflexivity|unfold buf6_size, buf6_elems; exact Hlarge].
Qed.

(** Case 2a-only: TOnly with new prefix.  Green4 if child empty OR both
    merged buffers (the new pre and existing s1) are out of Red/Orange/Yellow
    sizes. *)

Theorem repair_case_2a_only_green :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 : list X) (d3 : Cadeque X),
    (d3 = CEmpty \/
     (length (buf6_elems p1 ++ p2) >= 8 /\ buf6_size s1 >= 8)) ->
    triple_color (repair_case_2a_only p1 s1 p2 d3) = Green4.
Proof.
  intros X p1 s1 p2 d3 Hcase.
  unfold repair_case_2a_only, triple_color.
  destruct Hcase as [Hempty|[Hpre Hsuf]].
  - subst d3. reflexivity.
  - destruct d3 as [|t|tL tR]; [reflexivity| |];
      (rewrite buf6_color_green_of_large; [|unfold buf6_size, buf6_elems; exact Hpre]);
      (rewrite buf6_color_green_of_large; [reflexivity|exact Hsuf]).
Qed.

Theorem repair_case_2b_only_green :
  forall (X : Type) (p1 s1 : Buf6 X) (s3 : list X) (d3 : Cadeque X),
    (d3 = CEmpty \/
     (buf6_size p1 >= 8 /\ length (s3 ++ buf6_elems s1) >= 8)) ->
    triple_color (repair_case_2b_only p1 s1 s3 d3) = Green4.
Proof.
  intros X p1 s1 s3 d3 Hcase.
  unfold repair_case_2b_only, triple_color.
  destruct Hcase as [Hempty|[Hpre Hsuf]].
  - subst d3. reflexivity.
  - destruct d3 as [|t|tL tR]; [reflexivity| |];
      (rewrite buf6_color_green_of_large; [|exact Hpre]);
      (rewrite buf6_color_green_of_large; [reflexivity|unfold buf6_size, buf6_elems; exact Hsuf]).
Qed.

Theorem repair_case_2c_only_empty_green :
  forall (X : Type) (p1 s1 : Buf6 X) (p2 s2 : list X) (d2 : Cadeque X),
    (d2 = CEmpty \/
     (length (buf6_elems p1 ++ p2) >= 8 /\
      length (s2 ++ buf6_elems s1) >= 8)) ->
    triple_color (repair_case_2c_only_empty p1 s1 p2 s2 d2) = Green4.
Proof.
  intros X p1 s1 p2 s2 d2 Hcase.
  unfold repair_case_2c_only_empty, triple_color.
  destruct Hcase as [Hempty|[Hpre Hsuf]].
  - subst d2. reflexivity.
  - destruct d2 as [|t|tL tR]; [reflexivity| |];
      (rewrite buf6_color_green_of_large; [|unfold buf6_size, buf6_elems; exact Hpre]);
      (rewrite buf6_color_green_of_large; [reflexivity|unfold buf6_size, buf6_elems; exact Hsuf]).
Qed.

Theorem repair_case_2c_only_twosided_green :
  forall (X : Type) (p1 s1 : Buf6 X) (p_left s_right : list X) (child : Cadeque X),
    (child = CEmpty \/
     (length (buf6_elems p1 ++ p_left) >= 8 /\
      length (s_right ++ buf6_elems s1) >= 8)) ->
    triple_color (repair_case_2c_only_twosided p1 s1 p_left s_right child) = Green4.
Proof.
  intros X p1 s1 p_left s_right child Hcase.
  unfold repair_case_2c_only_twosided, triple_color.
  destruct Hcase as [Hempty|[Hpre Hsuf]].
  - subst child. reflexivity.
  - destruct child as [|t|tL tR]; [reflexivity| |];
      (rewrite buf6_color_green_of_large; [|unfold buf6_size, buf6_elems; exact Hpre]);
      (rewrite buf6_color_green_of_large; [reflexivity|unfold buf6_size, buf6_elems; exact Hsuf]).
Qed.
