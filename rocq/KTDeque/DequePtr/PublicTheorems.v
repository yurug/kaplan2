(** * Module: KTDeque.DequePtr.PublicTheorems --
      Gate-B theorem bundle for the extracted non-catenable deque.

    Purpose: a single import-able file giving the canonical theorem
    bundle for the [push_kt4 / inject_kt4 / pop_kt4 / eject_kt4] family,
    which is what [rocq/KTDeque/Extract/Extraction.v] actually extracts.
    A reviewer should be able to read just this file (plus its imports)
    and see, per public op, exactly what is mechanically proved and what
    is still open.

    See [kb/runbooks/minimum-release-gate.md] §"Gate B" and
    [kb/reports/wc-o1-verification-audit-2026-05-24.md] §F11 for the
    motivation: the lemmas in [OpsKTSeq.v], [OpsKTRegular.v], and
    [Footprint.v] together capture the correctness story, but they were
    scattered across files and stated against [kt2] / [kt3] / packet-
    level ops.  Here we package what fits cleanly against [kt4] (the
    extracted family) and explicitly mark what does not.

    ## What is proved here (per public op)

    For each [op ∈ { push_kt4 ; inject_kt4 ; pop_kt4 ; eject_kt4 }]:

    1. **Sequence correctness** (conditional on success).
       Statement: if [op] returns [PushOk c'] / [PopOk x c'] then the
       abstract sequence [kchain_to_list] commutes with the operation.
       These re-export the existing [*_kt4_seq] lemmas under canonical
       bundle names.

    2. **Regularity preservation** (conditional on success).
       New here: if [c] satisfies [regular_kt_top] and [op] returns
       [PushOk c'] / [PopOk x c'] then [c'] also satisfies
       [regular_kt_top].

    3. Initial state: [empty_kchain] satisfies [regular_kt_top]
       (re-exported from [OpsKTRegular]).

    ## What is open (Gate B follow-up)

    - **Totality under [regular_kt_top].**  [regular_kt] constrains
      [pkt_is_pnode] and the top-color sequence (no two adjacent Reds,
      Yellow's tail top ≠ Red).  It does *not* constrain that a Green-
      tagged packet's prefix is buf-coloured Green (sizes 2 or 3).
      Therefore a [KChain] satisfying [regular_kt_top] can still cause
      [push_kt4] to return [PushFail] (e.g., [KCons Green (PNode B1 _ _) _]).
      The reachable-state subset that actually arises from
      [empty_kchain] plus public ops is total, but proving that needs
      an additional invariant tying packet tags to buffer colours.

    - **Chain-level worst-case cost.**  [Footprint.v] proves a constant
      cost bound for the *packet-level* imperative DSL
      ([exec_push_pkt_C], [exec_inject_pkt_C], [exec_pop_pkt_C],
      [exec_eject_pkt_C]: each ≤ [NF_PUSH_PKT_FULL = 9] heap ops).
      The structural argument that [push_kt4] etc. perform at most a
      constant number of such packet operations is immediate by
      inspection (the functions are non-recursive — each is a finite
      pattern-match composed with at most one [green_of_red_k] call,
      and [green_of_red_k] is itself non-recursive with three
      structural cases).  A formal "chain-level WC O(1)" theorem
      linking the pure-functional [kt4] to packet-level cost counts
      remains to be written.

    These open items are tracked in the Gate B section of
    [kb/runbooks/minimum-release-gate.md].

    Cross-references:
    - [OpsKT.v]        — definitions of [push_kt4] etc.
    - [OpsKTSeq.v]     — base [*_kt4_seq] lemmas.
    - [OpsKTRegular.v] — base regularity definitions and [kt2] preservation.
    - [Footprint.v]    — packet-level imperative cost lemmas. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color.
From KTDeque.DequePtr Require Import Model OpsKT OpsKTSeq OpsKTRegular.

Module E := OpsKT.E.

(* ========================================================================== *)
(* Helper: [yellow_wrap_pr] preserves [regular_kt_top].                        *)
(*                                                                             *)
(* [yellow_wrap_pr pre i suf c]:                                               *)
(*   - if [kchain_top_color c <> Red] : returns [PushOk (KCons Yellow _ c)]. *)
(*   - if [kchain_top_color c = Red]  : tries [green_of_red_k c]; on success  *)
(*     returns [PushOk (KCons Yellow _ c')] where [c'] has Green top.          *)
(* In both successful branches the new top is Yellow and the new tail's top   *)
(* is non-Red, so [regular_kt_top] holds.                                      *)
(* ========================================================================== *)

Lemma yellow_wrap_pr_preserves_regular_top :
  forall A (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
         (c c' : KChain A),
    regular_kt c ->
    yellow_wrap_pr pre i suf c = PushOk c' ->
    regular_kt_top c'.
Proof.
  intros A pre i suf c c' Hreg Hyw.
  unfold yellow_wrap_pr in Hyw.
  destruct c as [b | col p tail].
  - (* KEnding: non-Red branch *)
    inversion Hyw; subst c'.
    split; [cbn; discriminate|].
    apply reg_kt_yellow; [cbn; exact I | cbn; discriminate | exact Hreg].
  - destruct col.
    + (* Green: non-Red branch *)
      inversion Hyw; subst c'.
      split; [cbn; discriminate|].
      apply reg_kt_yellow; [cbn; exact I | cbn; discriminate | exact Hreg].
    + (* Yellow: non-Red branch *)
      inversion Hyw; subst c'.
      split; [cbn; discriminate|].
      apply reg_kt_yellow; [cbn; exact I | cbn; discriminate | exact Hreg].
    + (* Red: fires [green_of_red_k] *)
      destruct (green_of_red_k (KCons Red p tail)) as [c''|] eqn:Hg;
        [|discriminate].
      inversion Hyw; subst c'.
      pose proof Hg as Htop. apply green_of_red_k_top_green in Htop.
      assert (Hreg' : regular_kt c'')
        by (eapply green_of_red_k_preserves_regular; eauto).
      split; [cbn; discriminate|].
      apply reg_kt_yellow.
      * cbn; exact I.
      * rewrite Htop; discriminate.
      * exact Hreg'.
Qed.

(* ========================================================================== *)
(* push_kt4 preserves [regular_kt_top].                                        *)
(* ========================================================================== *)

Theorem push_kt4_preserves_regular_top :
  forall A (x : E.t A) (c c' : KChain A),
    regular_kt_top c ->
    push_kt4 x c = PushOk c' ->
    regular_kt_top c'.
Proof.
  intros A x c c' [Htop Hreg] Hp.
  unfold push_kt4 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - (* KEnding b: six sub-cases (B0..B5).  B0..B4 stay KEnding; B5
       promotes to KCons Green (PNode (B3 ...) Hole (B3 ...)) (KEnding B0). *)
    destruct b; inversion Hp; subst c'; clear Hp;
      try (split; [cbn; discriminate | apply reg_kt_ending]).
    (* B5 case: new top is Green. *)
    split; [cbn; discriminate|].
    apply reg_kt_green; [cbn; exact I | apply reg_kt_ending].
  - (* KCons _ Hole _: every colour falls to PushFail. *)
    destruct col; discriminate.
  - destruct col.
    + (* Green: only B2 / B3 succeed, both via yellow_wrap_pr. *)
      apply regular_kt_green_inv in Hreg.
      destruct Hreg as [_ Htail_reg].
      destruct pre; try discriminate;
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
    + (* Yellow: B1/B2/B3 short-circuit to KCons Yellow; B4 fires
         green_of_red_k. *)
      apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      destruct pre as [|a|a b1|a b1 c0|a b1 c0 d|]; try discriminate.
      * (* B1 *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * (* B2 *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * (* B3 *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * (* B4: green_of_red_k path on Red(B5(x a b1 c0 d) i suf) *)
        destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst c'.
        assert (Hreg_red :
                  regular_kt (KCons Red
                                    (PNode (B5 x a b1 c0 d) i suf)
                                    c_tail))
          by (apply reg_kt_red;
              [cbn; exact I | exact Htail_top | exact Htail_reg]).
        assert (Hreg'' : regular_kt c'')
          by (eapply green_of_red_k_preserves_regular; eauto).
        pose proof Hg as Htop''. apply green_of_red_k_top_green in Htop''.
        split; [rewrite Htop''; discriminate | exact Hreg''].
    + (* Red top contradicts [regular_kt_top]'s top-color premise. *)
      cbn in Htop; congruence.
Qed.

(* ========================================================================== *)
(* inject_kt4 preserves [regular_kt_top].  Symmetric to push.                  *)
(* ========================================================================== *)

Theorem inject_kt4_preserves_regular_top :
  forall A (c : KChain A) (x : E.t A) (c' : KChain A),
    regular_kt_top c ->
    inject_kt4 c x = PushOk c' ->
    regular_kt_top c'.
Proof.
  intros A c x c' [Htop Hreg] Hp.
  unfold inject_kt4 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst c'; clear Hp;
      try (split; [cbn; discriminate | apply reg_kt_ending]).
    split; [cbn; discriminate|].
    apply reg_kt_green; [cbn; exact I | apply reg_kt_ending].
  - destruct col; discriminate.
  - destruct col.
    + apply regular_kt_green_inv in Hreg.
      destruct Hreg as [_ Htail_reg].
      destruct suf; try discriminate;
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
    + apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      destruct suf as [|a|a b1|a b1 c0|a b1 c0 d|]; try discriminate.
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst c'.
        assert (Hreg_red :
                  regular_kt (KCons Red
                                    (PNode pre i (B5 a b1 c0 d x))
                                    c_tail))
          by (apply reg_kt_red;
              [cbn; exact I | exact Htail_top | exact Htail_reg]).
        assert (Hreg'' : regular_kt c'')
          by (eapply green_of_red_k_preserves_regular; eauto).
        pose proof Hg as Htop''. apply green_of_red_k_top_green in Htop''.
        split; [rewrite Htop''; discriminate | exact Hreg''].
    + cbn in Htop; congruence.
Qed.

(* ========================================================================== *)
(* pop_kt4 preserves [regular_kt_top].                                         *)
(* ========================================================================== *)

Theorem pop_kt4_preserves_regular_top :
  forall A (c c' : KChain A) (x : E.t A),
    regular_kt_top c ->
    pop_kt4 c = PopOk x c' ->
    regular_kt_top c'.
Proof.
  intros A c c' x [Htop Hreg] Hp.
  unfold pop_kt4 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst c'; clear Hp;
      split; try (cbn; discriminate); apply reg_kt_ending.
  - destruct col; discriminate.
  - destruct col.
    + apply regular_kt_green_inv in Hreg.
      destruct Hreg as [_ Htail_reg].
      destruct pre; try discriminate.
      * (* B2 a b1: yellow_wrap_pr (B1 b1) i suf c_tail *)
        destruct (yellow_wrap_pr _ _ _ _) as [|c''] eqn:Hyw;
          [discriminate|].
        inversion Hp; subst c'.
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
      * (* B3 a b1 c1: yellow_wrap_pr (B2 b1 c1) i suf c_tail *)
        destruct (yellow_wrap_pr _ _ _ _) as [|c''] eqn:Hyw;
          [discriminate|].
        inversion Hp; subst c'.
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
    + apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      destruct pre; try discriminate.
      * (* B1 a: green_of_red_k on KCons Red (PNode B0 i suf) c_tail *)
        destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst c'.
        assert (Hreg_red :
                  regular_kt (KCons Red (PNode B0 i suf) c_tail))
          by (apply reg_kt_red;
              [cbn; exact I | exact Htail_top | exact Htail_reg]).
        assert (Hreg'' : regular_kt c'')
          by (eapply green_of_red_k_preserves_regular; eauto).
        pose proof Hg as Htop''. apply green_of_red_k_top_green in Htop''.
        split; [rewrite Htop''; discriminate | exact Hreg''].
      * (* B2 a b1: PopOk a (KCons Yellow (PNode (B1 b1) i suf) c_tail) *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * (* B3 *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * (* B4 *)
        inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
    + cbn in Htop; congruence.
Qed.

(* ========================================================================== *)
(* eject_kt4 preserves [regular_kt_top].  Symmetric to pop.                    *)
(* ========================================================================== *)

Theorem eject_kt4_preserves_regular_top :
  forall A (c c' : KChain A) (x : E.t A),
    regular_kt_top c ->
    eject_kt4 c = PopOk x c' ->
    regular_kt_top c'.
Proof.
  intros A c c' x [Htop Hreg] Hp.
  unfold eject_kt4 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst c'; clear Hp;
      split; try (cbn; discriminate); apply reg_kt_ending.
  - destruct col; discriminate.
  - destruct col.
    + apply regular_kt_green_inv in Hreg.
      destruct Hreg as [_ Htail_reg].
      destruct suf; try discriminate.
      * destruct (yellow_wrap_pr _ _ _ _) as [|c''] eqn:Hyw;
          [discriminate|].
        inversion Hp; subst c'.
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
      * destruct (yellow_wrap_pr _ _ _ _) as [|c''] eqn:Hyw;
          [discriminate|].
        inversion Hp; subst c'.
        eapply yellow_wrap_pr_preserves_regular_top; eauto.
    + apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      destruct suf; try discriminate.
      * (* B1: green_of_red_k on KCons Red (PNode pre i B0) c_tail *)
        destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst c'.
        assert (Hreg_red :
                  regular_kt (KCons Red (PNode pre i B0) c_tail))
          by (apply reg_kt_red;
              [cbn; exact I | exact Htail_top | exact Htail_reg]).
        assert (Hreg'' : regular_kt c'')
          by (eapply green_of_red_k_preserves_regular; eauto).
        pose proof Hg as Htop''. apply green_of_red_k_top_green in Htop''.
        split; [rewrite Htop''; discriminate | exact Hreg''].
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
      * inversion Hp; subst c'.
        split; [cbn; discriminate|].
        apply reg_kt_yellow; [cbn; exact I | exact Htail_top | exact Htail_reg].
    + cbn in Htop; congruence.
Qed.

(* ========================================================================== *)
(* Canonical bundle: re-export under simple names.                             *)
(* ========================================================================== *)

(** ** Sequence correctness (re-exports from [OpsKTSeq]). *)

Definition push_kt4_seq_thm    := @push_kt4_seq.
Definition inject_kt4_seq_thm  := @inject_kt4_seq.
Definition pop_kt4_seq_thm     := @pop_kt4_seq.
Definition eject_kt4_seq_thm   := @eject_kt4_seq.

(** ** Initial-state regularity (re-export from [OpsKTRegular]). *)

Definition empty_kchain_regular_top_thm := @empty_kchain_regular_top.
