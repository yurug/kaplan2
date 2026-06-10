(** * KTDeque.Catenable.CatKeystone — the catenable keystone (Phase 4b).

    CLOSED 2026-06-11: zero admits; all six [cat_keystone_*] theorems report
    "Closed under the global context".  Built top-down per rebuild-plan
    methodology rule 6, exactly as the deque keystone
    (DequePtr/DequeKeystone.v): the per-operation obligations started as
    [Admitted] scaffolding and were discharged through ConcatLemmas (regular
    concat), SRLemmas (semiregular concat, Lemma 6.2's weak half), PopLemmas
    (raw removals) and RepairLemmas (§6 red-terminal repair), under the
    three-clause invariant J = chain_wf /\ chain_ends_green /\
    chain_leveled 0 grown in place in Color.v.

    This v1 states the FUNCTIONAL keystone — KT99 §6 Theorem 6.1's content:
    every operation is total on regular ([J]) inputs, preserves [J], and has
    exact sequence semantics — INCLUDING [cad_concat] of two arbitrary [J]
    deques (the clause the archived Cadeque9 could not state).

    The COST half of [cat_wc_o1] (the buffer-primitive-count bound per the
    design memo, Decision 4) is added during discharge, once the functional
    proofs have frozen the op shapes: the counters mirror the op code, so
    defining them against still-moving code would double the rework.  The
    structural argument is already on record (every element movement in
    Ops.v is constant-bounded; buffers instantiate to the proven kt4 deque).

    Discharge notes (as built):
    - push/inject sequence correctness uses [J]'s sizes (pushing onto the
      suffix of an empty-prefix node is front-correct only when childless);
    - pop/eject totality needs the popped element to be [SGround] — the
      level-0 fact delivered by [chain_leveled]'s stratification, which
      also forces the repair-level cells to be [SSmall]/[SBig]. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas
  ConcatLemmas PopLemmas SRLemmas RepairLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Per-operation obligations (Admitted scaffolding — the to-do list).          *)
(* ========================================================================== *)

Lemma cad_push_preserves_J :
  forall A (x : A) (d : cadeque A),
    J d -> J (cad_push x d).
Proof.
  intros A x d [Hwf [Hg Hl]].
  unfold cad_push.
  destruct (@push_chain_preserves A (SGround x) d KOnly
              ltac:(congruence) ltac:(intros _; reflexivity) I Hwf Hg)
    as [Hwf' Hg'].
  split; [exact Hwf' |]. split; [exact Hg' |].
  apply push_chain_leveled; [reflexivity | exact Hl].
Qed.

Lemma cad_push_seq :
  forall A (x : A) (d : cadeque A),
    J d -> cad_to_list (cad_push x d) = x :: cad_to_list d.
Proof.
  intros A x d [Hwf _].
  unfold cad_push, cad_to_list.
  rewrite (push_chain_seq (SGround x) Hwf).
  reflexivity.
Qed.

Lemma cad_inject_preserves_J :
  forall A (d : cadeque A) (x : A),
    J d -> J (cad_inject d x).
Proof.
  intros A d x [Hwf [Hg Hl]].
  unfold cad_inject.
  destruct (@inject_chain_preserves A (SGround x) d KOnly
              ltac:(congruence) ltac:(intros _; reflexivity) I Hwf Hg)
    as [Hwf' Hg'].
  split; [exact Hwf' |]. split; [exact Hg' |].
  apply inject_chain_leveled; [exact Hl | reflexivity].
Qed.

Lemma cad_inject_seq :
  forall A (d : cadeque A) (x : A),
    J d -> cad_to_list (cad_inject d x) = cad_to_list d ++ [x].
Proof.
  intros A d x [Hwf _].
  unfold cad_inject, cad_to_list.
  rewrite (inject_chain_seq (SGround x) Hwf).
  reflexivity.
Qed.

Lemma cad_concat_total_J_seq :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof.
  intros A d e [Hwfd [Hgd Hld]] [Hwfe [Hge Hle]].
  destruct (cad_concat_total Hwfd Hgd Hwfe Hge)
    as [f [Hmk [[Hwf Hg] Hseq]]].
  exists f.
  split; [exact Hmk |].
  split; [| exact Hseq].
  split; [exact Hwf |]. split; [exact Hg |].
  exact (cad_concat_leveled Hld Hle Hmk).
Qed.

Lemma cad_pop_total_J_seq :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists x d',
      cad_pop d = Some (x, d') /\
      J d' /\
      cad_to_list d = x :: cad_to_list d'.
Proof.
  intros A d [Hwf [Hg Hl]] Hne.
  unfold cad_pop.
  destruct d as [|p r|l r]; [exfalso; apply Hne; reflexivity | |].
  - destruct (pop_raw_only_total Hwf Hg Hl)
      as [x [c' [Hpop [Hxw [Hxl [Hwc' [Hlc' [Hseq Hnp]]]]]]]].
    rewrite Hpop.
    destruct x as [a|b|p2 d2 s2];
      [| cbn [stored_leveled] in Hxl; contradiction
       | cbn [stored_leveled] in Hxl; contradiction].
    destruct (repair_pop_side_total Hwc' Hlc'
                ltac:(intros l2 r2 Heq; rewrite Heq in Hnp;
                      contradiction))
      as [f [Hrep [Hw [Hg' [Hl' Hs']]]]].
    rewrite Hrep.
    exists a, f.
    split; [reflexivity |].
    split.
    + split; [exact Hw |]. split; [exact Hg' | exact Hl'].
    + unfold cad_to_list. rewrite Hseq, Hs'. reflexivity.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hlw Hrw]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    cbn [chain_leveled] in Hl. destruct Hl as [Hll Hlr].
    destruct (pop_raw_pair_total Hls Hrs Hlw Hrw Hgl Hgr Hll Hlr)
      as [x [c' [Hpop [Hxw [Hxl [Hwc' [Hlc' [Hseq Hsib]]]]]]]].
    rewrite Hpop.
    destruct x as [a|b|p2 d2 s2];
      [| cbn [stored_leveled] in Hxl; contradiction
       | cbn [stored_leveled] in Hxl; contradiction].
    destruct (repair_pop_side_total Hwc' Hlc' Hsib)
      as [f [Hrep [Hw [Hg' [Hl' Hs']]]]].
    rewrite Hrep.
    exists a, f.
    split; [reflexivity |].
    split.
    + split; [exact Hw |]. split; [exact Hg' | exact Hl'].
    + unfold cad_to_list. rewrite Hseq, Hs'. reflexivity.
Qed.

Lemma cad_eject_total_J_seq :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists d' x,
      cad_eject d = Some (d', x) /\
      J d' /\
      cad_to_list d = cad_to_list d' ++ [x].
Proof.
  intros A d [Hwf [Hg Hl]] Hne.
  unfold cad_eject.
  destruct d as [|p r|l r]; [exfalso; apply Hne; reflexivity | |].
  - destruct (eject_raw_only_total Hwf Hg Hl)
      as [c' [x [Hpop [Hxw [Hxl [Hwc' [Hlc' [Hseq Hnp]]]]]]]].
    rewrite Hpop.
    destruct x as [a|b|p2 d2 s2];
      [| cbn [stored_leveled] in Hxl; contradiction
       | cbn [stored_leveled] in Hxl; contradiction].
    destruct (repair_eject_side_total Hwc' Hlc'
                ltac:(intros l2 r2 Heq; rewrite Heq in Hnp;
                      contradiction))
      as [f [Hrep [Hw [Hg' [Hl' Hs']]]]].
    rewrite Hrep.
    exists f, a.
    split; [reflexivity |].
    split.
    + split; [exact Hw |]. split; [exact Hg' | exact Hl'].
    + unfold cad_to_list. rewrite Hseq, Hs'. reflexivity.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hlw Hrw]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    cbn [chain_leveled] in Hl. destruct Hl as [Hll Hlr].
    destruct (eject_raw_pair_total Hls Hrs Hlw Hrw Hgl Hgr Hll Hlr)
      as [c' [x [Hpop [Hxw [Hxl [Hwc' [Hlc' [Hseq Hsib]]]]]]]].
    rewrite Hpop.
    destruct x as [a|b|p2 d2 s2];
      [| cbn [stored_leveled] in Hxl; contradiction
       | cbn [stored_leveled] in Hxl; contradiction].
    destruct (repair_eject_side_total Hwc' Hlc' Hsib)
      as [f [Hrep [Hw [Hg' [Hl' Hs']]]]].
    rewrite Hrep.
    exists f, a.
    split; [reflexivity |].
    split.
    + split; [exact Hw |]. split; [exact Hg' | exact Hl'].
    + unfold cad_to_list. rewrite Hseq, Hs'. reflexivity.
Qed.

(* ========================================================================== *)
(* The functional keystone: §6 Theorem 6.1 for this implementation.            *)
(* ========================================================================== *)

Theorem cat_keystone_empty :
  forall A, J (@cad_empty A) /\ cad_to_list (@cad_empty A) = [].
Proof. intros A. split; [apply empty_J | reflexivity]. Qed.

Theorem cat_keystone_push :
  forall A (x : A) (d : cadeque A),
    J d ->
    J (cad_push x d) /\
    cad_to_list (cad_push x d) = x :: cad_to_list d.
Proof.
  intros A x d HJ.
  split; [apply cad_push_preserves_J; exact HJ | apply cad_push_seq; exact HJ].
Qed.

Theorem cat_keystone_inject :
  forall A (d : cadeque A) (x : A),
    J d ->
    J (cad_inject d x) /\
    cad_to_list (cad_inject d x) = cad_to_list d ++ [x].
Proof.
  intros A d x HJ.
  split;
    [apply cad_inject_preserves_J; exact HJ | apply cad_inject_seq; exact HJ].
Qed.

(** The clause the archived Cadeque9 could not state: concat of two
    ARBITRARY regular catenable deques. *)
Theorem cat_keystone_concat :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof. intros A d e HJd HJe. apply cad_concat_total_J_seq; assumption. Qed.

Theorem cat_keystone_pop :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists x d',
      cad_pop d = Some (x, d') /\
      J d' /\
      cad_to_list d = x :: cad_to_list d'.
Proof. intros A d HJ Hne. apply cad_pop_total_J_seq; assumption. Qed.

Theorem cat_keystone_eject :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists d' x,
      cad_eject d = Some (d', x) /\
      J d' /\
      cad_to_list d = cad_to_list d' ++ [x].
Proof. intros A d HJ Hne. apply cad_eject_total_J_seq; assumption. Qed.

(* The admit list IS the to-do list.  Closure = these report "Closed under
   the global context". *)
Print Assumptions cat_keystone_empty.
Print Assumptions cat_keystone_push.
Print Assumptions cat_keystone_inject.
Print Assumptions cat_keystone_concat.
Print Assumptions cat_keystone_pop.
Print Assumptions cat_keystone_eject.
