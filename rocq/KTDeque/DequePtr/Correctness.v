(** * Module: KTDeque.DequePtr.Correctness -- functional refinement of the
    cost-instrumented packet ops to the abstract chain operations.

    ## Why this file exists

    The bridge between the abstract spec and the cost-bounded
    imperative DSL.  We have:

    - [OpsAbstract.v] defines [push_chain : E.t A -> Chain A ->
      option (Chain A)] etc.  Pure functions over the abstract type
      [Chain A].
    - [Footprint.v] defines [exec_push_pkt_C] etc.  Cost-tracked
      computations in [MC] over a heap of [PCell] records.

    The cost bounds in [Footprint.v] are about heap operations.  The
    sequence semantics in [OpsAbstract.v] is about [Chain]-level
    structure.  Without a bridge, the cost story doesn't tell us
    anything about what the imperative ops *do* to user data.

    This file proves the bridge:

      Imperative op  ≡  Abstract op  (modulo heap layout)

    via four refinement theorems:
      [exec_push_pkt_C_refines_push_chain]
      [exec_inject_pkt_C_refines_inject_chain]
      [exec_pop_pkt_C_refines_pop_chain]
      [exec_eject_pkt_C_refines_eject_chain]

    Each says: if the heap [H] currently represents abstract chain
    [c] (via [chain_repr c H]), and the abstract op succeeds with
    result [c'], then [exec_*_pkt_C] on [H] produces a heap [H']
    that represents [c'].  The combination with [Footprint.v]'s
    cost bounds is "WC O(1) per op AND functionally correct" — the
    full operational meaning of "verified worst-case O(1) deque".

    ## A subtlety: the [B5] precondition

    Each refinement is conditioned on (a) the abstract op succeeding,
    AND (b) the result not having a [B5] buffer at the top.  Condition
    (b) excludes the overflow case: in the imperative tier, overflow
    fires [make_red] producing a different chain shape than the naive
    abstract [push_chain] / [inject_chain] yields.  In well-formed
    Kaplan-Tarjan code, the regularity invariant
    ([Regularity.v] / [OpsKTRegular.v]) ensures (b) holds when overflow
    would actually fire — that's the whole point of regularity.

    Cross-references:
    - [KTDeque/DequePtr/Footprint.v]   -- the cost-bounded ops.
    - [KTDeque/DequePtr/OpsAbstract.v] -- the abstract surface.
    - [KTDeque/DequePtr/Regularity.v]  -- the invariant that makes
                                          (b) hold in production code.
    - [kb/spec/why-bounded-cascade.md] -- the intuition for why
                                          regularity + WC O(1) is
                                          the central correctness story.
*)

From KTDeque.Common Require Import Prelude FinMapHeap HeapExt Monad
                                    Element CostMonad Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model OpsAbstract Footprint.

(** ** Sequence preservation for the abstract chain ops. *)
Theorem push_pkt_seq :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    push_chain x c = Some c' ->
    chain_to_list c' = E.to_list A x ++ chain_to_list c.
Proof. exact (@push_chain_seq). Qed.

Theorem inject_pkt_seq :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    inject_chain c x = Some c' ->
    chain_to_list c' = chain_to_list c ++ E.to_list A x.
Proof. exact (@inject_chain_seq). Qed.

Theorem pop_pkt_seq :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    pop_chain c = Some (x, c') ->
    chain_to_list c = E.to_list A x ++ chain_to_list c'.
Proof. exact (@pop_chain_seq). Qed.

Theorem eject_pkt_seq :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    eject_chain c = Some (c', x) ->
    chain_to_list c = chain_to_list c' ++ E.to_list A x.
Proof. exact (@eject_chain_seq). Qed.

(** ** Combined: cost-bound + sequence-preservation duo. *)

Theorem packet_push_correct_and_O1 :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    push_chain x c = Some c' ->
    exec_push_pkt_C lroot x H = Some (H', lroot', n) ->
    n <= NF_PUSH_PKT_FULL /\
    chain_to_list c' = E.to_list A x ++ chain_to_list c.
Proof.
  intros A lroot x c c' H H' lroot' n Habs Hexec.
  split.
  - eapply exec_push_pkt_C_cost; eauto.
  - apply (@push_chain_seq A x c c' Habs).
Qed.

Theorem packet_inject_correct_and_O1 :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    inject_chain c x = Some c' ->
    exec_inject_pkt_C lroot x H = Some (H', lroot', n) ->
    n <= NF_PUSH_PKT_FULL /\
    chain_to_list c' = chain_to_list c ++ E.to_list A x.
Proof.
  intros A lroot x c c' H H' lroot' n Habs Hexec.
  split.
  - eapply exec_inject_pkt_C_cost; eauto.
  - apply (@inject_chain_seq A c c' x Habs).
Qed.

(** ** Bidirectional refinement: heap-state to abstract chain.

    NB: the refinement is conditioned on the abstract op producing a
    result whose top-level relevant buffer is NOT [B5].  In the
    overflow case, the imperative tier fires [make_red] and produces
    a different chain shape than the naive abstract [push_chain] /
    [inject_chain] yields.  The Kaplan-Tarjan regularity invariant
    ensures this precondition holds in well-formed code (between
    operations, no top-level buffer is set up to overflow). *)

(** Helpers: extract top-level buffers of a chain, used in
    no-overflow preconditions. *)
Definition is_b5 {X : Type} (b : Buf5 X) : bool :=
  match b with
  | B5 _ _ _ _ _ => true
  | _ => false
  end.

Definition chain_top_pre {A : Type} (c : Chain A) : Buf5 (E.t A) :=
  match c with
  | Ending b => b
  | ChainCons (PNode pre _ _) _ => pre
  | ChainCons Hole _ => B0
  end.

Definition chain_top_suf {A : Type} (c : Chain A) : Buf5 (E.t A) :=
  match c with
  | Ending _ => B0
  | ChainCons (PNode _ _ suf) _ => suf
  | ChainCons Hole _ => B0
  end.

(** Phase S audit (F4/P6): predicate "the chain's top packet is in the
    simple-cons form (inner = Hole)".  When this holds, the four
    no-overflow refinement theorems below apply.  Chains produced by
    the simple-case abstract ops [push_chain] / [inject_chain] /
    [pop_chain] / [eject_chain] preserve [chain_top_simple] so long as
    the input satisfies it.  The nested-cons case (inner = PNode ...)
    is addressed by [chain_repr_cons_inv_nested] and the deferred
    Phase S Stage 2/3 work. *)
Definition chain_top_simple {A : Type} (c : Chain A) : Prop :=
  match c with
  | Ending _ => True
  | ChainCons (PNode _ Hole _) _ => True
  | _ => False
  end.

(** *** Push refinement (no-overflow case).

    When [push_chain] succeeds and the result's top-prefix is not
    [B5], the imperative [exec_push_pkt_C] takes the [OkP] path and
    the resulting heap represents the abstract result. *)

(** Helper destruction lemma for [chain_repr] inversion, avoiding
    fragile inversion-pattern naming.  Decomposes the predicate into
    its underlying components. *)
Lemma chain_repr_inv_ending :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc) (b : Buf5 (E.t A)),
    chain_repr H l (Ending b) ->
    exists cell,
      lookup H l = Some cell /\
      pcell_pre cell = b /\
      pcell_suf cell = B0 /\
      pcell_inner cell = None /\
      pcell_tail cell = None /\
      buf_all_at_level 0 b.
Proof.
  intros A H l b HR. unfold chain_repr in HR.
  inversion HR; subst.
  match goal with
  | [ Hlk : lookup H l = Some ?cc |- _ ] => exists cc
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

(** Curried inversion lemma for the cons case.

    The challenge: the standard [inversion]+[subst] eagerly substitutes
    the [pre]/[suf]/[i]/[c'] parameters with the cell's underlying
    fields, which destroys the [Hsuf : pcell_suf cell = suf] form.

    Solution: prove a slightly weaker version where the conclusion
    abstracts the cell directly (no separate [pre]/[suf] fields), then
    derive the curried form. *)
(** Inversion lemma for the simple-cons case.

    Phase S audit (F4/P6) compatibility: with [chain_repr_at] now
    carrying three constructors (Ending, simple cons, nested cons),
    inversion of [chain_repr H l (ChainCons (PNode pre i suf) c')]
    in general yields a disjunction on [i].  This lemma takes the
    extra precondition [i = Hole] so it can return the simple-case
    witness directly; this matches the four refinement theorems
    below, which all case-split [c] and process the simple-cons
    branch, then independently establish [i = Hole] from their
    abstract op result.  See [chain_repr_cons_inv_nested] for the
    nested companion.

    The four downstream callers each pass [eq_refl] or an [eq_sym]
    derived from [subst i] applied to a [Hole = i] witness. *)
Lemma chain_repr_cons_inv :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc)
         (pre suf : Buf5 (E.t A)) (c' : Chain A),
    chain_repr H l (ChainCons (PNode pre Hole suf) c') ->
    exists cell ltail,
      lookup H l = Some cell /\
      pcell_pre cell = pre /\
      pcell_suf cell = suf /\
      pcell_inner cell = None /\
      pcell_tail cell = Some ltail /\
      buf_all_at_level 0 pre /\
      buf_all_at_level 0 suf /\
      chain_repr_at H ltail c' 1.
Proof.
  intros A H l pre suf c' HR. unfold chain_repr in HR.
  inversion HR; subst.
  - (* simple cons (Hole inner) -- direct match on [PNode pre Hole suf] *)
    match goal with
    | [ Hlk : lookup H l = Some ?cc, Htail : pcell_tail _ = Some ?lt |- _ ] =>
        exists cc, lt
    end.
    repeat (split; [first [assumption | reflexivity] |]).
    assumption.
Qed.

(** Inversion lemma for the nested cons case (i = PNode ...).

    Phase S audit (F4/P6): companion to [chain_repr_cons_inv] for the
    new nested constructor, exposing the inner-packet location and its
    [packet_repr_at] decoding.  Not yet used by the refinement
    theorems (Stage 2/3 deferred). *)
Lemma chain_repr_cons_inv_nested :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc)
         (pre suf pre' suf' : Buf5 (E.t A))
         (i' : Packet A) (c' : Chain A),
    chain_repr H l
      (ChainCons (PNode pre (PNode pre' i' suf') suf) c') ->
    exists cell ltail inner_loc,
      lookup H l = Some cell /\
      pcell_pre cell = pre /\
      pcell_suf cell = suf /\
      pcell_inner cell = Some inner_loc /\
      pcell_tail cell = Some ltail /\
      buf_all_at_level 0 pre /\
      buf_all_at_level 0 suf /\
      packet_repr_at H (Some inner_loc) (PNode pre' i' suf') 1 /\
      chain_repr_at H ltail c' (2 + packet_depth i').
Proof.
  intros A H l pre suf pre' suf' i' c' HR. unfold chain_repr in HR.
  inversion HR; subst.
  match goal with
  | [ Hlk : lookup H l = Some ?cc,
      Htail : pcell_tail _ = Some ?lt,
      HRpkt : packet_repr_at _ (Some ?il) _ _ |- _ ] =>
      exists cc, lt, il
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

Theorem exec_push_pkt_C_refines_push_chain :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    @exec_push_pkt_C A lroot x H = Some (H', lroot', n) ->
    push_chain x c = Some c' ->
    is_b5 (chain_top_pre c') = false ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Hexec Habs Hnb5.
  unfold exec_push_pkt_C, bindC in Hexec.
  unfold exec_push_pkt_naive_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct c as [b0 | p c0].
  - (* Ending b0 *)
    apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb]]]]]].
    rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
    cbn in Habs.
    destruct (buf5_push_naive x b0) as [b'|] eqn:Hpush; [|discriminate].
    inversion Habs; subst c'; clear Habs.
    cbn in Hnb5.
    rewrite Hpre_e in Hexec.
    rewrite Hpush in Hexec.
    pose proof
      (@buf5_push_preserves_levels A 0 x b0 _ Hlx Hwfb Hpush) as Hwfb'.
    (* Local tactic to close one bN case in the Ending branch. *)
    Local Ltac close_ending_case Hexec Hsuf_e Hinner_e Htail_e Hwfb' :=
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
      inversion Hexec; subst; clear Hexec;
      unfold chain_repr;
      eapply chain_repr_ending_at;
        [ rewrite freeze_lookup; cbn;
          match goal with
          | [ |- context [loc_eq_dec ?nl ?nl] ] =>
              destruct (loc_eq_dec nl nl) as [_|nE];
                [reflexivity|contradiction]
          end
        | apply freeze_makes_frozen
        | reflexivity
        | rewrite Hsuf_e; reflexivity
        | rewrite Hinner_e; reflexivity
        | rewrite Htail_e; reflexivity
        | exact Hwfb' ].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + (* B0 impossible *) destruct b0; cbn in Hpush; inversion Hpush.
    + close_ending_case Hexec Hsuf_e Hinner_e Htail_e Hwfb'.
    + close_ending_case Hexec Hsuf_e Hinner_e Htail_e Hwfb'.
    + close_ending_case Hexec Hsuf_e Hinner_e Htail_e Hwfb'.
    + close_ending_case Hexec Hsuf_e Hinner_e Htail_e Hwfb'.
    + discriminate Hnb5.
  - (* ChainCons p c0 *)
    destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Simple cons (i = Hole). *)
      apply chain_repr_cons_inv in HR.
      destruct HR as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      cbn in Habs.
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush; [|discriminate].
      inversion Habs; subst c'; clear Habs.
      cbn in Hnb5.
      rewrite Hpre_c in Hexec.
      rewrite Hpush in Hexec.
      pose proof
        (@buf5_push_preserves_levels A 0 x pre _ Hlx Hwfp Hpush) as Hwfp'.
      pose proof Hsuf_c as Hsuf_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      Local Ltac close_push_simple_cons HHH Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRtl :=
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst; clear Hexec;
        unfold chain_repr;
        eapply chain_repr_cons_at;
          [ rewrite freeze_lookup; cbn;
            destruct (loc_eq_dec (next_loc HHH) (next_loc HHH)) as [_|nE];
              [reflexivity|contradiction]
          | apply freeze_makes_frozen
          | reflexivity
          | cbn; reflexivity
          | cbn; exact Hinner_c'
          | cbn; exact Htail_c'
          | exact Hwfp'
          | exact Hwfs
          | eapply chain_repr_at_persists_strong; [|exact HRtl];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong] ].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * (* B0 impossible *) destruct pre; cbn in Hpush; inversion Hpush.
      * close_push_simple_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRtl.
      * close_push_simple_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRtl.
      * close_push_simple_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRtl.
      * close_push_simple_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRtl.
      * discriminate Hnb5.
    + (* Nested cons (i = PNode ipre ii isuf). *)
      apply chain_repr_cons_inv_nested in HR.
      destruct HR as [cell_c [ltail_c [inner_loc_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs [HRpkt HRtl]]]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      cbn in Habs.
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush; [|discriminate].
      inversion Habs; subst c'; clear Habs.
      cbn in Hnb5.
      rewrite Hpre_c in Hexec.
      rewrite Hpush in Hexec.
      pose proof
        (@buf5_push_preserves_levels A 0 x pre _ Hlx Hwfp Hpush) as Hwfp'.
      pose proof Hsuf_c as Hsuf_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      Local Ltac close_push_nested_cons HHH Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRpkt HRtl :=
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst; clear Hexec;
        unfold chain_repr;
        eapply chain_repr_nested_cons_at;
          [ rewrite freeze_lookup; cbn;
            destruct (loc_eq_dec (next_loc HHH) (next_loc HHH)) as [_|nE];
              [reflexivity|contradiction]
          | apply freeze_makes_frozen
          | reflexivity
          | cbn; reflexivity
          | cbn; exact Hinner_c'
          | cbn; exact Htail_c'
          | exact Hwfp'
          | exact Hwfs
          | eapply packet_repr_at_persists_strong; [|exact HRpkt];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong]
          | eapply chain_repr_at_persists_strong; [|exact HRtl];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong] ].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * destruct pre; cbn in Hpush; inversion Hpush.
      * close_push_nested_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRpkt HRtl.
      * close_push_nested_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRpkt HRtl.
      * close_push_nested_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRpkt HRtl.
      * close_push_nested_cons H Hexec Hinner_c' Htail_c' Hwfp' Hwfs Hwf HRpkt HRtl.
      * discriminate Hnb5.
Qed.

(** *** Inject refinement (no-overflow case).

    For Ending cells, the imperative inject puts the new element into
    [pcell_pre] (preserving the "single buffer in pre" Ending
    convention).  For ChainCons cells, it puts it into [pcell_suf]. *)

Theorem exec_inject_pkt_C_refines_inject_chain :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    @exec_inject_pkt_C A lroot x H = Some (H', lroot', n) ->
    inject_chain c x = Some c' ->
    is_b5 (chain_top_pre c') = false ->
    is_b5 (chain_top_suf c') = false ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Hexec Habs Hnb5p Hnb5s.
  unfold exec_inject_pkt_C, bindC in Hexec.
  unfold exec_inject_pkt_naive_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct c as [b0 | p c0].
  - (* Ending b0 *)
    apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb]]]]]].
    rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
    rewrite Htail_e in Hexec.
    cbn in Habs.
    destruct (buf5_inject_naive b0 x) as [b'|] eqn:Hinj; [|discriminate].
    inversion Habs; subst c'; clear Habs.
    cbn in Hnb5p.
    rewrite Hpre_e in Hexec.
    rewrite Hinj in Hexec.
    pose proof
      (@buf5_inject_preserves_levels A 0 b0 x _ Hlx Hwfb Hinj) as Hwfb'.
    (* Rewrite the remaining cell-projection facts into Hexec to make
       all references concrete; then inversion + subst on the resulting
       equations works without disturbing [b0]. *)
    rewrite Hsuf_e in Hexec.
    rewrite Hinner_e in Hexec.
    Local Ltac close_inject_ending_case Hexec Hwfb' :=
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
      inversion Hexec; subst; clear Hexec;
      unfold chain_repr;
      eapply chain_repr_ending_at;
        [ rewrite freeze_lookup; cbn;
          match goal with
          | [ |- context [loc_eq_dec ?nl ?nl] ] =>
              destruct (loc_eq_dec nl nl) as [_|nE];
                [reflexivity|contradiction]
          end
        | apply freeze_makes_frozen
        | reflexivity
        | reflexivity
        | reflexivity
        | reflexivity
        | exact Hwfb' ].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + destruct b0; cbn in Hinj; inversion Hinj.
    + close_inject_ending_case Hexec Hwfb'.
    + close_inject_ending_case Hexec Hwfb'.
    + close_inject_ending_case Hexec Hwfb'.
    + close_inject_ending_case Hexec Hwfb'.
    + discriminate Hnb5p.
  - (* ChainCons p c0 *)
    destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Simple cons (i = Hole). *)
      apply chain_repr_cons_inv in HR.
      destruct HR as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      rewrite Htail_c in Hexec.
      cbn in Habs.
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hinj; [|discriminate].
      inversion Habs; subst c'; clear Habs.
      cbn in Hnb5s.
      rewrite Hsuf_c in Hexec.
      rewrite Hinj in Hexec.
      pose proof
        (@buf5_inject_preserves_levels A 0 suf x _ Hlx Hwfs Hinj) as Hwfs'.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      Local Ltac close_inject_simple_cons HHH Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRtl :=
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst; clear Hexec;
        unfold chain_repr;
        eapply chain_repr_cons_at;
          [ rewrite freeze_lookup; cbn;
            destruct (loc_eq_dec (next_loc HHH) (next_loc HHH)) as [_|nE];
              [reflexivity|contradiction]
          | apply freeze_makes_frozen
          | simpl; exact Hpre_c'
          | simpl; reflexivity
          | simpl; exact Hinner_c'
          | simpl; reflexivity
          | exact Hwfp
          | exact Hwfs'
          | eapply chain_repr_at_persists_strong; [|exact HRtl];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong] ].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * destruct suf; cbn in Hinj; inversion Hinj.
      * close_inject_simple_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRtl.
      * close_inject_simple_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRtl.
      * close_inject_simple_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRtl.
      * close_inject_simple_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRtl.
      * discriminate Hnb5s.
    + (* Nested cons (i = PNode ipre ii isuf). *)
      apply chain_repr_cons_inv_nested in HR.
      destruct HR as [cell_c [ltail_c [inner_loc_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs [HRpkt HRtl]]]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      rewrite Htail_c in Hexec.
      cbn in Habs.
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hinj; [|discriminate].
      inversion Habs; subst c'; clear Habs.
      cbn in Hnb5s.
      rewrite Hsuf_c in Hexec.
      rewrite Hinj in Hexec.
      pose proof
        (@buf5_inject_preserves_levels A 0 suf x _ Hlx Hwfs Hinj) as Hwfs'.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      Local Ltac close_inject_nested_cons HHH Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRpkt HRtl :=
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst; clear Hexec;
        unfold chain_repr;
        eapply chain_repr_nested_cons_at;
          [ rewrite freeze_lookup; cbn;
            destruct (loc_eq_dec (next_loc HHH) (next_loc HHH)) as [_|nE];
              [reflexivity|contradiction]
          | apply freeze_makes_frozen
          | simpl; exact Hpre_c'
          | simpl; reflexivity
          | simpl; exact Hinner_c'
          | simpl; reflexivity
          | exact Hwfp
          | exact Hwfs'
          | eapply packet_repr_at_persists_strong; [|exact HRpkt];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong]
          | eapply chain_repr_at_persists_strong; [|exact HRtl];
            eapply persists_strong_trans;
              [eapply alloc_persists_strong; exact Hwf
              |apply freeze_persists_strong] ].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * destruct suf; cbn in Hinj; inversion Hinj.
      * close_inject_nested_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRpkt HRtl.
      * close_inject_nested_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRpkt HRtl.
      * close_inject_nested_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRpkt HRtl.
      * close_inject_nested_cons H Hexec Hpre_c' Hinner_c' Hwfp Hwfs' Hwf HRpkt HRtl.
      * discriminate Hnb5s.
Qed.

(** *** Pop refinement.

    Pop has no overflow case (the abstract op fails on B0 input;
    the imperative also fails).  Refinement just tracks the heap
    update and the popped element. *)

Theorem exec_pop_pkt_C_refines_pop_chain :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    @exec_pop_pkt_C A lroot H = Some (H', (x, lroot'), n) ->
    pop_chain c = Some (x, c') ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Hexec Habs.
  unfold exec_pop_pkt_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct c as [b0 | p c0].
  - (* Ending b0 *)
    apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb]]]]]].
    rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
    cbn in Habs.
    destruct (buf5_pop_naive b0) as [[xp b']|] eqn:Hpop; [|discriminate].
    inversion Habs; subst x c'; clear Habs.
    rewrite Hpre_e in Hexec.
    rewrite Hpop in Hexec.
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    pose proof
      (@buf5_pop_preserves_levels A 0 b0 xp b' Hwfb Hpop) as [_ Hwfb'].
    inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
    unfold chain_repr.
    eapply chain_repr_ending_at.
    + rewrite freeze_lookup; cbn;
        destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
          [reflexivity|contradiction].
    + apply freeze_makes_frozen.
    + reflexivity.
    + simpl; exact Hsuf_e.
    + simpl; exact Hinner_e.
    + simpl; exact Htail_e.
    + exact Hwfb'.
  - (* ChainCons p c0 *)
    destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Simple cons (i = Hole). *)
      apply chain_repr_cons_inv in HR.
      destruct HR as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      cbn in Habs.
      destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hpop; [|discriminate].
      inversion Habs; subst x c'; clear Habs.
      rewrite Hpre_c in Hexec.
      rewrite Hpop in Hexec.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      pose proof
        (@buf5_pop_preserves_levels A 0 pre xp pre' Hwfp Hpop) as [_ Hwfp'].
      inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
      unfold chain_repr.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      pose proof Hsuf_c as Hsuf_c'.
      eapply chain_repr_cons_at.
      * rewrite freeze_lookup; cbn;
          destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
            [reflexivity|contradiction].
      * apply freeze_makes_frozen.
      * reflexivity.
      * simpl; exact Hsuf_c'.
      * simpl; exact Hinner_c'.
      * simpl; exact Htail_c'.
      * exact Hwfp'.
      * exact Hwfs.
      * eapply chain_repr_at_persists_strong; [|exact HRtl];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
    + (* Nested cons (i = PNode ipre ii isuf). *)
      apply chain_repr_cons_inv_nested in HR.
      destruct HR as [cell_c [ltail_c [inner_loc_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs [HRpkt HRtl]]]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      cbn in Habs.
      destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hpop; [|discriminate].
      inversion Habs; subst x c'; clear Habs.
      rewrite Hpre_c in Hexec.
      rewrite Hpop in Hexec.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      pose proof
        (@buf5_pop_preserves_levels A 0 pre xp pre' Hwfp Hpop) as [_ Hwfp'].
      inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
      unfold chain_repr.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      pose proof Hsuf_c as Hsuf_c'.
      eapply chain_repr_nested_cons_at.
      * rewrite freeze_lookup; cbn;
          destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
            [reflexivity|contradiction].
      * apply freeze_makes_frozen.
      * reflexivity.
      * simpl; exact Hsuf_c'.
      * simpl; exact Hinner_c'.
      * simpl; exact Htail_c'.
      * exact Hwfp'.
      * exact Hwfs.
      * eapply packet_repr_at_persists_strong; [|exact HRpkt];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
      * eapply chain_repr_at_persists_strong; [|exact HRtl];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
Qed.

(** *** Eject refinement. *)

(** ** Combined: cost + sequence preservation for pop_full / eject_full. *)
Theorem packet_pop_full_correct_and_O1 :
  forall (A : Type) (lroot : Loc) (c : Chain A) (x : E.t A) (c' : Chain A)
         (H H' : HeapP (E.t A)) (r : option (E.t A * Loc)) (n : nat),
    pop_chain_full c = Some (x, c') ->
    exec_pop_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL /\
    chain_to_list c = E.to_list A x ++ chain_to_list c'.
Proof.
  intros A lroot c x c' H H' r n Habs Hexec. split.
  - eapply exec_pop_pkt_full_C_cost; eauto.
  - eapply pop_chain_full_seq; eauto.
Qed.

Theorem packet_eject_full_correct_and_O1 :
  forall (A : Type) (lroot : Loc) (c : Chain A) (c' : Chain A) (x : E.t A)
         (H H' : HeapP (E.t A)) (r : option (Loc * E.t A)) (n : nat),
    eject_chain_full c = Some (c', x) ->
    exec_eject_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL /\
    chain_to_list c = chain_to_list c' ++ E.to_list A x.
Proof.
  intros A lroot c c' x H H' r n Habs Hexec. split.
  - eapply exec_eject_pkt_full_C_cost; eauto.
  - eapply eject_chain_full_seq; eauto.
Qed.

Theorem exec_eject_pkt_C_refines_eject_chain :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    @exec_eject_pkt_C A lroot H = Some (H', (lroot', x), n) ->
    eject_chain c = Some (c', x) ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Hexec Habs.
  unfold exec_eject_pkt_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct c as [b0 | p c0].
  - (* Ending b0 *)
    apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb]]]]]].
    rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
    rewrite Htail_e in Hexec.
    cbn in Habs.
    destruct (buf5_eject_naive b0) as [[b' xp]|] eqn:Hej; [|discriminate].
    inversion Habs; subst c' x; clear Habs.
    rewrite Hpre_e in Hexec.
    rewrite Hej in Hexec.
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    pose proof
      (@buf5_eject_preserves_levels A 0 b0 xp b' Hwfb Hej) as [_ Hwfb'].
    inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
    unfold chain_repr.
    eapply chain_repr_ending_at.
    + rewrite freeze_lookup; cbn;
        destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
          [reflexivity|contradiction].
    + apply freeze_makes_frozen.
    + reflexivity.
    + simpl; first [exact Hsuf_e | reflexivity].
    + simpl; first [exact Hinner_e | reflexivity].
    + simpl; first [exact Htail_e | reflexivity].
    + exact Hwfb'.
  - (* ChainCons p c0 *)
    destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Simple cons (i = Hole). *)
      apply chain_repr_cons_inv in HR.
      destruct HR as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      rewrite Htail_c in Hexec.
      cbn in Habs.
      destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hej; [|discriminate].
      inversion Habs; subst c' x; clear Habs.
      rewrite Hsuf_c in Hexec.
      rewrite Hej in Hexec.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      pose proof
        (@buf5_eject_preserves_levels A 0 suf xp suf' Hwfs Hej) as [_ Hwfs'].
      inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
      unfold chain_repr.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      eapply chain_repr_cons_at.
      * rewrite freeze_lookup; cbn;
          destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
            [reflexivity|contradiction].
      * apply freeze_makes_frozen.
      * simpl; exact Hpre_c'.
      * reflexivity.
      * simpl; exact Hinner_c'.
      * simpl; reflexivity.
      * exact Hwfp.
      * exact Hwfs'.
      * eapply chain_repr_at_persists_strong; [|exact HRtl];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
    + (* Nested cons (i = PNode ipre ii isuf). *)
      apply chain_repr_cons_inv_nested in HR.
      destruct HR as [cell_c [ltail_c [inner_loc_c [Hlk_c [Hpre_c [Hsuf_c
                         [Hinner_c [Htail_c [Hwfp [Hwfs [HRpkt HRtl]]]]]]]]]]].
      rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst c_top; clear Hlk_top.
      rewrite Htail_c in Hexec.
      cbn in Habs.
      destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hej; [|discriminate].
      inversion Habs; subst c' x; clear Habs.
      rewrite Hsuf_c in Hexec.
      rewrite Hej in Hexec.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      pose proof
        (@buf5_eject_preserves_levels A 0 suf xp suf' Hwfs Hej) as [_ Hwfs'].
      inversion Hexec; clear Hexec; try subst H'; try subst lroot'; try subst n.
      unfold chain_repr.
      pose proof Hpre_c as Hpre_c'.
      pose proof Hinner_c as Hinner_c'.
      pose proof Htail_c as Htail_c'.
      eapply chain_repr_nested_cons_at.
      * rewrite freeze_lookup; cbn;
          destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|nE];
            [reflexivity|contradiction].
      * apply freeze_makes_frozen.
      * simpl; exact Hpre_c'.
      * reflexivity.
      * simpl; exact Hinner_c'.
      * simpl; reflexivity.
      * exact Hwfp.
      * exact Hwfs'.
      * eapply packet_repr_at_persists_strong; [|exact HRpkt];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
      * eapply chain_repr_at_persists_strong; [|exact HRtl];
          eapply persists_strong_trans;
            [eapply alloc_persists_strong; exact Hwf
            |apply freeze_persists_strong].
Qed.

(** ** Phase S' Goal B: refinement theorems for the [_full] ops.

    Strategy.  The imperative [exec_push_pkt_C] composes
    [exec_push_pkt_naive_C] with [exec_make_red_push_pkt_C].  The
    naive-overflow branch returns [OverflowP lroot] without ever
    updating the cell — the cell at [lroot] still has its original
    prefix.  [exec_make_red_push_pkt_C] then reads [lroot] and
    pattern-matches [pcell_pre top_cell] against [B5].  But by
    [chain_repr], the cell's [pcell_pre] equals the chain's top
    buffer, which is not [B5] (otherwise the abstract op would have
    returned [None]).  So [exec_make_red_push_pkt_C] returns
    [failC]; the imperative cannot succeed via that branch.

    Hence: when both abstract [push_chain_full] succeeds and the
    imperative [exec_push_pkt_C] succeeds, the imperative must take
    the [OkP] path, which equals [exec_push_pkt_naive_C] producing a
    non-[B5] result.  The abstract [push_chain_full] in turn equals
    [push_chain] when the buffer-level naive push doesn't overflow.
    The two reduce to Goal A.

    For [pop]/[eject_full], the underflow path fires
    [exec_make_green_pop_pkt_C] / [exec_make_green_eject_pkt_C].
    The make_green imperative reads tail cells and tries
    [buf5_pop_naive] / [buf5_eject_naive] across them.  Because
    pop/eject_full's underflow path is more involved (the abstract
    [make_green_pop_chain] only handles the [pop_chain c'] sub-call
    on the tail, while the imperative also tries
    [buf5_eject_naive] on the tail's [suf]), we split the
    [_full] refinement into a no-underflow case (closed) and an
    underflow case (deferred — see status block below). *)

(** [is_b0 b]: the boolean version of "b is B0".  Used in
    no-underflow preconditions. *)
Definition is_b0 {X : Type} (b : Buf5 X) : bool :=
  match b with
  | B0 => true
  | _ => false
  end.

(** *** Helper: under [chain_repr], the cell's [pcell_pre] matches
    [chain_top_pre].  Used to discharge the make_red precondition
    that [pcell_pre = B5] would force the abstract input top to be
    [B5] (and hence [push_chain_full] would fail). *)
Lemma chain_repr_cell_top_pre :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc) (c : Chain A) (cell : PCell (E.t A)),
    chain_repr H l c ->
    lookup H l = Some cell ->
    pcell_pre cell = chain_top_pre c.
Proof.
  intros A H l c cell HR Hlk.
  destruct c as [b | p c0].
  - (* Ending *)
    apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [Hpre_e _]]].
    rewrite Hlk_e in Hlk. inversion Hlk; subst cell_e. exact Hpre_e.
  - (* ChainCons *)
    destruct p as [|pre i suf].
    + (* Hole: chain_repr forces this case impossible, but we still
         need to discharge it. *)
      exfalso. unfold chain_repr in HR. inversion HR.
    + destruct i as [|ipre ii isuf].
      * apply chain_repr_cons_inv in HR.
        destruct HR as [cell_c [_ [Hlk_c [Hpre_c _]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c. exact Hpre_c.
      * apply chain_repr_cons_inv_nested in HR.
        destruct HR as [cell_c [_ [_ [Hlk_c [Hpre_c _]]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c. exact Hpre_c.
Qed.

(** Symmetric helper for [pcell_suf]. *)
Lemma chain_repr_cell_top_suf :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc) (c : Chain A) (cell : PCell (E.t A)),
    chain_repr H l c ->
    lookup H l = Some cell ->
    pcell_suf cell = chain_top_suf c.
Proof.
  intros A H l c cell HR Hlk.
  destruct c as [b | p c0].
  - apply chain_repr_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [_ [Hsuf_e _]]]].
    rewrite Hlk_e in Hlk. inversion Hlk; subst cell_e. exact Hsuf_e.
  - destruct p as [|pre i suf].
    + exfalso. unfold chain_repr in HR. inversion HR.
    + destruct i as [|ipre ii isuf].
      * apply chain_repr_cons_inv in HR.
        destruct HR as [cell_c [_ [Hlk_c [_ [Hsuf_c _]]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c. exact Hsuf_c.
      * apply chain_repr_cons_inv_nested in HR.
        destruct HR as [cell_c [_ [_ [Hlk_c [_ [Hsuf_c _]]]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c. exact Hsuf_c.
Qed.

(** [push_chain_full] succeeding implies the input chain's top
    prefix is not [B5]. *)
Lemma push_chain_full_top_not_b5 :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    push_chain_full x c = Some c' ->
    is_b5 (chain_top_pre c) = false.
Proof.
  intros A x c c' Heq. unfold push_chain_full in Heq.
  destruct c as [b | p c0]; cbn.
  - destruct b as [|y|y z|y z w|y z w u|y z w u v];
      cbn in Heq; try discriminate; reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf];
      destruct pre as [|y|y z|y z w|y z w u|y z w u v];
      cbn in Heq; try discriminate; reflexivity.
Qed.

(** [push_chain_full] result's top prefix is never [B5]:
    - Simple path: result is the buffer-pushed top, restricted to non-B5.
    - Make_red path: result top is [B3 a b c]. *)
Lemma push_chain_full_result_not_b5 :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    push_chain_full x c = Some c' ->
    is_b5 (chain_top_pre c') = false.
Proof.
  intros A x c c' Heq. unfold push_chain_full in Heq.
  destruct c as [b | p c0].
  - destruct (buf5_push_naive x b) as [b'|] eqn:Hp; [|discriminate].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v];
      try (inversion Heq; subst c'; reflexivity).
    (* B5: make_red.  Inspect [make_red_push_chain] result. *)
    unfold make_red_push_chain in Heq.
    destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
      [|discriminate].
    inversion Heq; subst c'; reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner *)
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hp; [|discriminate].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
        try (inversion Heq; subst c'; reflexivity).
      (* B5: make_red. *)
      unfold make_red_push_chain in Heq.
      destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
        [|discriminate].
      destruct (push_chain (E.pair A u v eq) c0) as [c0''|] eqn:Hpush;
        [|discriminate].
      inversion Heq; subst c'; reflexivity.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hp; [|discriminate].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
        try (inversion Heq; subst c'; reflexivity).
      (* B5: make_red Case 3. Result top pre is [B3 _ _ _], not [B5]. *)
      unfold make_red_push_chain in Heq.
      destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
        [|discriminate].
      destruct (buf5_push_naive (E.pair A u v eq) ipre) as [pre''|] eqn:Hpush2;
        [|discriminate].
      destruct pre'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv];
        try discriminate;
        inversion Heq; subst c'; reflexivity.
Qed.

(** [inject_chain_full] succeeding implies the input chain's
    relevant top buffer is not [B5]: pre for Ending, suf for
    ChainCons. *)
Lemma inject_chain_full_pre_not_b5_ending :
  forall (A : Type) (c c' : Chain A) (x : E.t A) (b : Buf5 (E.t A)),
    c = Ending b ->
    inject_chain_full c x = Some c' ->
    is_b5 b = false.
Proof.
  intros A c c' x b Heq Hi. subst c. unfold inject_chain_full in Hi.
  destruct b as [|y|y z|y z w|y z w u|y z w u v];
    cbn in Hi; try discriminate; reflexivity.
Qed.

Lemma inject_chain_full_suf_not_b5_cons :
  forall (A : Type) (c c' : Chain A) (x : E.t A)
         (pre suf : Buf5 (E.t A)) (c0 : Chain A),
    c = ChainCons (PNode pre Hole suf) c0 ->
    inject_chain_full c x = Some c' ->
    is_b5 suf = false.
Proof.
  intros A c c' x pre suf c0 Heq Hi. subst c. unfold inject_chain_full in Hi.
  destruct suf as [|y|y z|y z w|y z w u|y z w u v];
    cbn in Hi; try discriminate; reflexivity.
Qed.

(** [inject_chain_full] result's [chain_top_suf] is never [B5].
    NOTE: result's [chain_top_pre] is NOT vacuously non-B5 — for
    [ChainCons] input the inject doesn't modify [pre], so [pre] is
    propagated through and may be [B5] if the input had one.  The
    [is_b5 (chain_top_pre c') = false] precondition on inject_full
    refinement is therefore genuine. *)
Lemma inject_chain_full_result_suf_not_b5 :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    inject_chain_full c x = Some c' ->
    is_b5 (chain_top_suf c') = false.
Proof.
  intros A c c' x Heq. unfold inject_chain_full in Heq.
  destruct c as [b | p c0].
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hi; [|discriminate].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v];
      try (inversion Heq; subst c'; reflexivity).
    unfold make_red_inject_chain in Heq.
    destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
      [|discriminate].
    inversion Heq; subst c'; reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner *)
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hi; [|discriminate].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v];
        try (inversion Heq; subst c'; reflexivity).
      unfold make_red_inject_chain in Heq.
      destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
        [|discriminate].
      destruct (inject_chain c0 (E.pair A y z eq)) as [c0''|] eqn:Hinj;
        [|discriminate].
      inversion Heq; subst c'; reflexivity.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hi; [|discriminate].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v];
        try (inversion Heq; subst c'; reflexivity).
      unfold make_red_inject_chain in Heq.
      destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
        [|discriminate].
      destruct (buf5_inject_naive isuf (E.pair A y z eq)) as [suf''|] eqn:Hinj2;
        [|discriminate].
      destruct suf'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv];
        try discriminate;
        inversion Heq; subst c'; reflexivity.
Qed.

(** Helper: when [exec_push_pkt_naive_C] takes the [OverflowP] branch
    (Phase S''' shape), the cell at [lroot] is read, the buf5_push
    overflows to [B5 a b cc d e], and a fresh cell is alloc-frozen at
    [next_loc H] carrying the B5 in [pcell_pre] with the original cell's
    [suf]/[inner]/[tail] links.  [l'] is the fresh location. *)
Lemma exec_push_pkt_naive_C_overflow_inv :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    @exec_push_pkt_naive_C A lroot x H = Some (H', OverflowP l', n) ->
    exists cell a b cc d e,
      lookup H lroot = Some cell /\
      is_b5 (pcell_pre cell) = false /\
      buf5_push_naive x (pcell_pre cell) = Some (B5 a b cc d e) /\
      l' = next_loc H /\
      H' = freeze (next_loc H)
             (snd (alloc (mkPCell (B5 a b cc d e) (pcell_suf cell)
                                  (pcell_inner cell) (pcell_tail cell)) H)).
Proof.
  intros A lroot x H H' l' n Hex.
  unfold exec_push_pkt_naive_C, bindC in Hex.
  unfold read_MC in Hex.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  destruct (buf5_push_naive x (pcell_pre c0)) as [b'|] eqn:Hp; [|discriminate].
  destruct b' as [|y|y z|y z w|y z w u|y z w u v];
    try (unfold alloc_freeze_MC, bindC, alloc_MC, freeze_MC, retC in Hex;
         inversion Hex; fail).
  (* Only the B5 case remains.  Set up a let-binding for the alloc
     pair so [snd (alloc ...)] stays symbolic through reductions. *)
  exists c0, y, z, w, u, v.
  split. { reflexivity. }
  split.
  { destruct (pcell_pre c0) as [|p1|p1 p2|p1 p2 p3|p1 p2 p3 p4|p1 p2 p3 p4 p5];
      cbn in Hp; try discriminate; reflexivity. }
  split. { exact Hp. }
  set (cell5 := mkPCell (B5 y z w u v) (pcell_suf c0)
                        (pcell_inner c0) (pcell_tail c0)) in *.
  unfold alloc_freeze_MC, bindC, retC, alloc_MC, freeze_MC in Hex.
  injection Hex; intros En El EH; clear Hex.
  split. { exact (eq_sym El). }
  rewrite <- EH. unfold alloc. cbn. reflexivity.
Qed.

(** Symmetric for inject (Phase S''' shape). *)
Lemma exec_inject_pkt_naive_C_overflow_inv :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    @exec_inject_pkt_naive_C A lroot x H = Some (H', OverflowP l', n) ->
    exists cell a b cc d e,
      lookup H lroot = Some cell /\
      l' = next_loc H /\
      ((pcell_tail cell = None /\
        is_b5 (pcell_pre cell) = false /\
        buf5_inject_naive (pcell_pre cell) x = Some (B5 a b cc d e) /\
        H' = freeze (next_loc H)
               (snd (alloc (mkPCell (B5 a b cc d e) (pcell_suf cell)
                                    (pcell_inner cell) (pcell_tail cell)) H)))
      \/
       (exists ltail, pcell_tail cell = Some ltail /\
        is_b5 (pcell_suf cell) = false /\
        buf5_inject_naive (pcell_suf cell) x = Some (B5 a b cc d e) /\
        H' = freeze (next_loc H)
               (snd (alloc (mkPCell (pcell_pre cell) (B5 a b cc d e)
                                    (pcell_inner cell) (Some ltail)) H)))).
Proof.
  intros A lroot x H H' l' n Hex.
  unfold exec_inject_pkt_naive_C, bindC in Hex.
  unfold read_MC in Hex.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  destruct (pcell_tail c0) as [ltail|] eqn:Htail.
  - (* Some tail *)
    destruct (buf5_inject_naive (pcell_suf c0) x) as [s'|] eqn:Hi; [|discriminate].
    destruct s' as [|y|y z|y z w|y z w u|y z w u v];
      try (unfold alloc_freeze_MC, bindC, alloc_MC, freeze_MC, retC in Hex;
           inversion Hex; fail).
    exists c0, y, z, w, u, v.
    split. { reflexivity. }
    set (cell5 := mkPCell (pcell_pre c0) (B5 y z w u v)
                          (pcell_inner c0) (Some ltail)) in *.
    unfold alloc_freeze_MC, bindC, retC, alloc_MC, freeze_MC in Hex.
    injection Hex; intros En El EH; clear Hex.
    split. { exact (eq_sym El). }
    right. exists ltail.
    split. { exact Htail. }
    split.
    { destruct (pcell_suf c0) as [|p1|p1 p2|p1 p2 p3|p1 p2 p3 p4|p1 p2 p3 p4 p5];
        cbn in Hi; try discriminate; reflexivity. }
    split. { exact Hi. }
    rewrite <- EH. unfold alloc. cbn. reflexivity.
  - (* None tail *)
    destruct (buf5_inject_naive (pcell_pre c0) x) as [b'|] eqn:Hi; [|discriminate].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v];
      try (unfold alloc_freeze_MC, bindC, alloc_MC, freeze_MC, retC in Hex;
           inversion Hex; fail).
    exists c0, y, z, w, u, v.
    split. { reflexivity. }
    rewrite <- Htail in Hex.
    set (cell5 := mkPCell (B5 y z w u v) (pcell_suf c0)
                          (pcell_inner c0) (pcell_tail c0)) in *.
    unfold alloc_freeze_MC, bindC, retC, alloc_MC, freeze_MC in Hex.
    injection Hex; intros En El EH; clear Hex.
    split. { exact (eq_sym El). }
    left.
    split. { exact Htail. }
    split.
    { destruct (pcell_pre c0) as [|p1|p1 p2|p1 p2 p3|p1 p2 p3 p4|p1 p2 p3 p4 p5];
        cbn in Hi; try discriminate; reflexivity. }
    split. { exact Hi. }
    rewrite <- EH. unfold alloc. cbn. reflexivity.
Qed.

(** [exec_make_red_push_pkt_C] requires [pcell_pre cell = B5] at
    [lroot]; if [pcell_pre cell] is non-B5, it returns [None]. *)
Lemma exec_make_red_push_pkt_C_pre_b5_required :
  forall (A : Type) (lroot : Loc) (H : HeapP (E.t A)) (cell : PCell (E.t A)),
    lookup H lroot = Some cell ->
    is_b5 (pcell_pre cell) = false ->
    @exec_make_red_push_pkt_C A lroot H = None.
Proof.
  intros A lroot H cell Hlk Hnb5.
  unfold exec_make_red_push_pkt_C, bindC.
  unfold read_MC. rewrite Hlk.
  destruct (pcell_pre cell) as [|y|y z|y z w|y z w u|y z w u v];
    cbn in Hnb5; try discriminate; reflexivity.
Qed.

(** Symmetric for inject: the imperative make_red_inject branches on
    [pcell_tail].  If [None]: requires [pcell_pre = B5].  If
    [Some _]: requires [pcell_suf = B5]. *)
Lemma exec_make_red_inject_pkt_C_pre_b5_required_ending :
  forall (A : Type) (lroot : Loc) (H : HeapP (E.t A)) (cell : PCell (E.t A)),
    lookup H lroot = Some cell ->
    pcell_tail cell = None ->
    is_b5 (pcell_pre cell) = false ->
    @exec_make_red_inject_pkt_C A lroot H = None.
Proof.
  intros A lroot H cell Hlk Htail Hnb5.
  unfold exec_make_red_inject_pkt_C, bindC.
  unfold read_MC. rewrite Hlk.
  rewrite Htail.
  destruct (pcell_pre cell) as [|y|y z|y z w|y z w u|y z w u v];
    cbn in Hnb5; try discriminate; reflexivity.
Qed.

Lemma exec_make_red_inject_pkt_C_suf_b5_required_cons :
  forall (A : Type) (lroot : Loc) (H : HeapP (E.t A)) (cell : PCell (E.t A))
         (ltail : Loc),
    lookup H lroot = Some cell ->
    pcell_tail cell = Some ltail ->
    is_b5 (pcell_suf cell) = false ->
    @exec_make_red_inject_pkt_C A lroot H = None.
Proof.
  intros A lroot H cell ltail Hlk Htail Hnb5.
  unfold exec_make_red_inject_pkt_C, bindC.
  unfold read_MC. rewrite Hlk.
  rewrite Htail.
  destruct (pcell_suf cell) as [|y|y z|y z w|y z w u|y z w u v];
    cbn in Hnb5; try discriminate; reflexivity.
Qed.


(** *** Phase S''' helpers: composed alloc-freeze lookup lemmas.

    Working with [freeze (next_loc H) (snd (alloc c H))] one rewrite
    at a time triggers Coq's eta/iota reduction on [alloc] and turns
    the heap into a record literal that defeats further pattern
    matching.  These wrappers do the rewriting in one shot, opaquely. *)
Lemma lookup_alloc_freeze_self :
  forall {C : Type} (c : C) (H : Heap C),
    lookup (freeze (next_loc H) (snd (alloc c H))) (next_loc H) = Some c.
Proof.
  intros C c H. rewrite freeze_lookup. apply alloc_lookup_self.
Qed.

Lemma lookup_alloc_freeze_other :
  forall {C : Type} (c : C) (H : Heap C) (l : Loc),
    l <> next_loc H ->
    lookup (freeze (next_loc H) (snd (alloc c H))) l = lookup H l.
Proof.
  intros C c H l Hne.
  rewrite freeze_lookup. apply lookup_after_alloc. exact Hne.
Qed.

Lemma is_frozen_alloc_freeze_self :
  forall {C : Type} (c : C) (H : Heap C),
    is_frozen (freeze (next_loc H) (snd (alloc c H))) (next_loc H) = true.
Proof.
  intros C c H. apply freeze_makes_frozen.
Qed.

Lemma is_frozen_alloc_freeze_preserves :
  forall {C : Type} (c : C) (H : Heap C) (l : Loc),
    is_frozen H l = true ->
    is_frozen (freeze (next_loc H) (snd (alloc c H))) l = true.
Proof.
  intros C c H l Hf.
  apply freeze_preserves_frozen.
  rewrite alloc_preserves_frozen. exact Hf.
Qed.

(** Composed next_loc through alloc-freeze: bumps by [Pos.succ]. *)
Lemma next_loc_alloc_freeze :
  forall {C : Type} (c : C) (H : Heap C),
    next_loc (freeze (next_loc H) (snd (alloc c H))) = Pos.succ (next_loc H).
Proof.
  intros C c H. rewrite freeze_next_loc. apply next_loc_after_alloc.
Qed.

(** *** Phase S''' — level-k inversion lemmas for [chain_repr_at].

    Companions to [chain_repr_inv_ending] / [chain_repr_cons_inv] /
    [chain_repr_cons_inv_nested] that operate at an arbitrary level [k]
    rather than the implicit 0.  Used by the make_red Cons sub-case
    lemma to invert [chain_repr_at H ltail c' 1]. *)
Lemma chain_repr_at_inv_ending :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc) (b : Buf5 (E.t A)) (k : nat),
    chain_repr_at H l (Ending b) k ->
    exists cell,
      lookup H l = Some cell /\
      is_frozen H l = true /\
      pcell_pre cell = b /\
      pcell_suf cell = B0 /\
      pcell_inner cell = None /\
      pcell_tail cell = None /\
      buf_all_at_level k b.
Proof.
  intros A H l b k HR. inversion HR; subst.
  match goal with
  | [ Hlk : lookup H l = Some ?cc |- _ ] => exists cc
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

Lemma chain_repr_at_inv_simple_cons :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc)
         (pre suf : Buf5 (E.t A)) (c' : Chain A) (k : nat),
    chain_repr_at H l (ChainCons (PNode pre Hole suf) c') k ->
    exists cell ltail,
      lookup H l = Some cell /\
      is_frozen H l = true /\
      pcell_pre cell = pre /\
      pcell_suf cell = suf /\
      pcell_inner cell = None /\
      pcell_tail cell = Some ltail /\
      buf_all_at_level k pre /\
      buf_all_at_level k suf /\
      chain_repr_at H ltail c' (S k).
Proof.
  intros A H l pre suf c' k HR. inversion HR; subst.
  match goal with
  | [ Hlk : lookup H l = Some ?cc, Htail : pcell_tail _ = Some ?lt |- _ ] =>
      exists cc, lt
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

Lemma chain_repr_at_inv_nested_cons :
  forall (A : Type) (H : HeapP (E.t A)) (l : Loc)
         (pre suf pre' suf' : Buf5 (E.t A))
         (i' : Packet A) (c' : Chain A) (k : nat),
    chain_repr_at H l
      (ChainCons (PNode pre (PNode pre' i' suf') suf) c') k ->
    exists cell ltail inner_loc,
      lookup H l = Some cell /\
      is_frozen H l = true /\
      pcell_pre cell = pre /\
      pcell_suf cell = suf /\
      pcell_inner cell = Some inner_loc /\
      pcell_tail cell = Some ltail /\
      buf_all_at_level k pre /\
      buf_all_at_level k suf /\
      packet_repr_at H (Some inner_loc) (PNode pre' i' suf') (S k) /\
      chain_repr_at H ltail c' (S (S k) + packet_depth i').
Proof.
  intros A H l pre suf pre' suf' i' c' k HR. inversion HR; subst.
  match goal with
  | [ Hlk : lookup H l = Some ?cc,
      Htail : pcell_tail _ = Some ?lt,
      HRpkt : packet_repr_at _ (Some ?il) _ _ |- _ ] =>
      exists cc, lt, il
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

(** Inversion lemma for [packet_repr_at H (Some inner_loc) (PNode pre i suf) k]. *)
Lemma packet_repr_at_pnode_inv :
  forall (A : Type) (H : HeapP (E.t A)) (inner_loc : Loc)
         (pre suf : Buf5 (E.t A)) (i : Packet A) (k : nat),
    packet_repr_at H (Some inner_loc) (PNode pre i suf) k ->
    exists cell,
      lookup H inner_loc = Some cell /\
      is_frozen H inner_loc = true /\
      pcell_pre cell = pre /\
      pcell_suf cell = suf /\
      pcell_tail cell = None /\
      buf_all_at_level k pre /\
      buf_all_at_level k suf /\
      packet_repr_at H (pcell_inner cell) i (S k).
Proof.
  intros A H inner_loc pre suf i k HR. inversion HR; subst.
  match goal with
  | [ Hlk : lookup H inner_loc = Some ?cc |- _ ] => exists cc
  end.
  repeat (split; [first [assumption | reflexivity] |]).
  assumption.
Qed.

(** *** Phase S''' — make_red push refinement (Ending sub-case).

    The first sub-case of P2-residual: when the abstract chain
    being repaired is [Ending (B5 a b cc d e)] (the top is just a
    single B5 buffer with no tail), the abstract returns
    [ChainCons (PNode (B3 a b cc) Hole B0) (Ending (B1 (E.pair d e)))]
    via [make_red_push_chain]; the imperative does two alloc-freezes
    (new tail Ending(B1 pde) at [next_loc H], new top with B3 prefix
    at [next_loc H']).  Both produce the same chain shape — heap
    representation matches.

    Hypothesis form: [lover] holds the materialized B5 cell (allocated
    by Phase S''' [exec_push_pkt_naive_C] OverflowP arm) with
    [suf = B0], [inner = None], [tail = None] — these are the Ending
    invariants.  Levels at 0 throughout.  *)
Lemma exec_make_red_push_pkt_C_refines_ending :
  forall (A : Type) (lover : Loc)
         (a b cc d e : E.t A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat)
         (c'' : Chain A),
    lookup H lover = Some (mkPCell (B5 a b cc d e) B0 None None) ->
    is_frozen H lover = true ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    @exec_make_red_push_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_push_chain (Ending (B5 a b cc d e)) = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover a b cc d e H H' lroot' n c''
         Hlk Hf_lover Hwf Hla Hlb Hlcc Hld Hle Hexec Habs.
  (* Step 1: peel back both abstract and imperative on the SAME
     [Nat.eq_dec] case — both consume it and produce the same
     [E.pair A d e eq] term.  Sharing the [eq] proof avoids UIP. *)
  unfold make_red_push_chain in Habs.
  unfold exec_make_red_push_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk in Hexec. cbn in Hexec.
  unfold pkt_pair_safe in Hexec.
  destruct (Nat.eq_dec (E.level A d) (E.level A e)) as [eq|]; [|discriminate].
  inversion Habs; subst c''; clear Habs.
  cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
  inversion Hexec; subst H' lroot' n; clear Hexec.
  (* Step 2: name the intermediate heaps.  H1 = post-tail-alloc-freeze;
     H2 = post-top-alloc-freeze.  lroot' = next_loc H1 = new top. *)
  set (cell_tail := mkPCell (B1 (E.pair A d e eq)) B0 (None : option Loc)
                            (None : option Loc)).
  set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
  set (cell_top := mkPCell (B3 a b cc) B0 (None : option Loc)
                           (Some (next_loc H))).
  set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
  (* The new top loc is [next_loc H1]; the new tail loc is
     [next_loc H] (= fst (alloc cell_tail H)). *)
  assert (Hnext_loc_H1 : next_loc H1 = Pos.succ (next_loc H)).
  { unfold H1. rewrite freeze_next_loc. apply next_loc_after_alloc. }
  assert (Hwf1 : well_formed_heap H1).
  { unfold H1. apply freeze_well_formed.
    apply alloc_well_formed. exact Hwf. }
  (* Step 3: discharge the chain_repr goal.  Build it bottom-up:
     first the inner Ending (at next_loc H), then the cons. *)
  (* Pre-establish the two lookups and frozenness facts AS LEMMAS, so
     the unifier doesn't expand [snd (alloc ...)] at the wrong time. *)
  assert (Hne : next_loc H <> next_loc H1).
  { rewrite Hnext_loc_H1.
    intros Heq. exact (Pos.succ_discr (next_loc H) Heq). }
  assert (Hlk_top : lookup H2 (next_loc H1) = Some cell_top).
  { unfold H2. apply lookup_alloc_freeze_self. }
  assert (Hlk_tail : lookup H2 (next_loc H) = Some cell_tail).
  { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
    unfold H1. apply lookup_alloc_freeze_self. }
  assert (Hf_top : is_frozen H2 (next_loc H1) = true).
  { unfold H2. apply is_frozen_alloc_freeze_self. }
  assert (Hf_tail : is_frozen H2 (next_loc H) = true).
  { unfold H2. apply is_frozen_alloc_freeze_preserves.
    unfold H1. apply is_frozen_alloc_freeze_self. }
  unfold chain_repr.
  eapply chain_repr_cons_at with (ltail := next_loc H).
  - exact Hlk_top.
  - exact Hf_top.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn. tauto.
  - cbn. exact I.
  - eapply chain_repr_ending_at with (b := B1 (E.pair A d e eq)).
    + exact Hlk_tail.
    + exact Hf_tail.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold buf_all_at_level. rewrite E.level_pair. rewrite Hld. reflexivity.
Qed.

(** *** Phase S''' — make_red push refinement (ChainCons sub-case).

    Dual of the Ending sub-case.  The cell at [lover] holds a B5 in
    [pcell_pre] with [pcell_inner = None] and [pcell_tail = Some ltail],
    where [ltail] decodes a chain [c'] at level 1.  The abstract
    [make_red_push_chain] pairs (d,e), pushes the pair onto [c'] (via
    [push_chain]), and forms a new top with [B3 a b c] in pre, the
    original suf, and tail = the pushed-onto chain.

    The imperative reads [ltail], does [buf5_push_naive pde tail.pre],
    alloc-freezes a new tail, then alloc-freezes a new top.  Three
    shapes for [c'] (Ending / simple cons / nested cons), times five
    non-B5 outcomes for [buf5_push_naive] = 15 sub-cases. *)
Lemma exec_make_red_push_pkt_C_refines_cons :
  forall (A : Type) (lover : Loc) (a b cc d e : E.t A)
         (suf : Buf5 (E.t A)) (ltail : Loc) (c' c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover = Some (mkPCell (B5 a b cc d e) suf None (Some ltail)) ->
    is_frozen H lover = true ->
    chain_repr_at H ltail c' 1 ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    buf_all_at_level 0 suf ->
    @exec_make_red_push_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_push_chain (ChainCons (PNode (B5 a b cc d e) Hole suf) c') = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover a b cc d e suf ltail c' c'' H H' lroot' n
         Hlk_top Hf_top HRtl Hwf Hla Hlb Hlcc Hld Hle Hwfs Hexec Habs.
  unfold make_red_push_chain in Habs.
  destruct (Nat.eq_dec (E.level A d) (E.level A e)) as [eq|]; [|discriminate].
  destruct (push_chain (E.pair A d e eq) c') as [c''_inner|] eqn:Habs_inner;
    [|discriminate].
  inversion Habs; subst c''; clear Habs.
  unfold exec_make_red_push_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk_top in Hexec. cbn in Hexec.
  unfold pkt_pair_safe in Hexec.
  destruct (Nat.eq_dec (E.level A d) (E.level A e)) as [eq2|]; [|discriminate].
  assert (Heq_eq : eq2 = eq) by (apply Eqdep_dec.UIP_dec; apply Nat.eq_dec).
  subst eq2.
  set (pde := E.pair A d e eq) in *.
  assert (Hl_pde : E.level A pde = 1).
  { unfold pde. rewrite E.level_pair. cbn. f_equal. exact Hld. }
  destruct c' as [b' | p' c'0].
  - (* c' = Ending b' *)
    apply chain_repr_at_inv_ending in HRtl.
    destruct HRtl as [tail_cell [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                       [Htl_inner [Htl_tail Hwfb']]]]]]].
    cbn in Habs_inner.
    destruct (buf5_push_naive pde b') as [b''|] eqn:Hpush_b'; [|discriminate].
    inversion Habs_inner; subst c''_inner; clear Habs_inner.
    rewrite Hlk_tl in Hexec. cbn in Hexec.
    rewrite Htl_pre in Hexec.
    rewrite Hpush_b' in Hexec.
    pose proof (@buf5_push_preserves_levels A 1 pde b' b'' Hl_pde Hwfb' Hpush_b')
      as Hwfb''.
    rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
    (* Five non-B5 cases close via wrapper-based discharge.
       For Ending case, the inner chain at level 1 is [Ending b'']. *)
    destruct b'' as [|y|y z|y z w|y z w u|y z w u v].
    + (* B0 — abstract value; b' must have been emptier... but
         buf5_push_naive on a non-empty result is non-empty.  So this
         is impossible. *)
      destruct b'; cbn in Hpush_b'; inversion Hpush_b'.
    + (* B1 *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B1 y) B0 (None : option Loc) (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1).
      { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
      { unfold H2. apply lookup_alloc_freeze_self. }
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
      { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
        unfold H1. apply lookup_alloc_freeze_self. }
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
      { unfold H2. apply is_frozen_alloc_freeze_self. }
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
      { unfold H2. apply is_frozen_alloc_freeze_preserves.
        unfold H1. apply is_frozen_alloc_freeze_self. }
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew.
      * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * cbn. tauto.
      * exact Hwfs.
      * eapply chain_repr_ending_at with (b := B1 y).
        -- exact Hlk_tailnew.
        -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + (* B2 *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B2 y z) B0 (None : option Loc) (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1).
      { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
      { unfold H2. apply lookup_alloc_freeze_self. }
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
      { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
        unfold H1. apply lookup_alloc_freeze_self. }
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
      { unfold H2. apply is_frozen_alloc_freeze_self. }
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
      { unfold H2. apply is_frozen_alloc_freeze_preserves.
        unfold H1. apply is_frozen_alloc_freeze_self. }
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew.
      * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * cbn. tauto.
      * exact Hwfs.
      * eapply chain_repr_ending_at with (b := B2 y z).
        -- exact Hlk_tailnew.
        -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + (* B3 *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B3 y z w) B0 (None : option Loc) (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1).
      { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
      { unfold H2. apply lookup_alloc_freeze_self. }
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
      { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
        unfold H1. apply lookup_alloc_freeze_self. }
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
      { unfold H2. apply is_frozen_alloc_freeze_self. }
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
      { unfold H2. apply is_frozen_alloc_freeze_preserves.
        unfold H1. apply is_frozen_alloc_freeze_self. }
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew.
      * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * cbn. tauto.
      * exact Hwfs.
      * eapply chain_repr_ending_at with (b := B3 y z w).
        -- exact Hlk_tailnew.
        -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + (* B4 *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B4 y z w u) B0 (None : option Loc)
                                (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1).
      { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
      { unfold H2. apply lookup_alloc_freeze_self. }
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
      { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
        unfold H1. apply lookup_alloc_freeze_self. }
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
      { unfold H2. apply is_frozen_alloc_freeze_self. }
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
      { unfold H2. apply is_frozen_alloc_freeze_preserves.
        unfold H1. apply is_frozen_alloc_freeze_self. }
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew.
      * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * cbn. tauto.
      * exact Hwfs.
      * eapply chain_repr_ending_at with (b := B4 y z w u).
        -- exact Hlk_tailnew.
        -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + (* B5 — failC *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      discriminate Hexec.
  - (* c' = ChainCons p' c'0 *)
    destruct p' as [|p'_pre p'_inner p'_suf].
    + (* Hole: chain_repr_at impossible *)
      exfalso. inversion HRtl.
    + destruct p'_inner as [|p'_pre' p'_ii p'_suf'].
      * (* simple cons: c' = ChainCons (PNode p'_pre Hole p'_suf) c'0 *)
        apply chain_repr_at_inv_simple_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail [Hwfp [Hwfsp HRtl2]]]]]]]]]].
        cbn in Habs_inner.
        destruct (buf5_push_naive pde p'_pre) as [pre''|] eqn:Hpush_p'pre;
          [|discriminate].
        inversion Habs_inner; subst c''_inner; clear Habs_inner.
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        rewrite Htl_pre in Hexec.
        rewrite Hpush_p'pre in Hexec.
        pose proof (@buf5_push_preserves_levels A 1 pde p'_pre pre''
                      Hl_pde Hwfp Hpush_p'pre) as Hwfpre''.
        rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
        (* Each non-B5 case: alloc-freeze new tail (mkPCell pre'' p'_suf
           None (Some ltail2)) ⟶ alloc-freeze new top.  Inner chain
           goal: ChainCons (PNode pre'' Hole p'_suf) c'0 at level 1. *)
        destruct pre'' as [|y|y z|y z w|y z w u|y z w u v].
        -- destruct p'_pre; cbn in Hpush_p'pre; inversion Hpush_p'pre.
        -- (* B1 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B1 y) p'_suf (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 (* H ⤳ H1 ⤳ H2.  H1 = freeze ... (alloc cell_tail H);
                    H2 = freeze ... (alloc cell_top H1). *)
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B2 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B2 y z) p'_suf (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B3 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B3 y z w) p'_suf (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B4 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B4 y z w u) p'_suf (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B5 — failC *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           discriminate Hexec.
      * (* nested cons: c' = ChainCons (PNode p'_pre (PNode ...) p'_suf) c'0 *)
        apply chain_repr_at_inv_nested_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [inner_loc2
                           [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail
                           [Hwfp [Hwfsp [HRpkt HRtl2]]]]]]]]]]]].
        cbn in Habs_inner.
        destruct (buf5_push_naive pde p'_pre) as [pre''|] eqn:Hpush_p'pre;
          [|discriminate].
        inversion Habs_inner; subst c''_inner; clear Habs_inner.
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        rewrite Htl_pre in Hexec.
        rewrite Hpush_p'pre in Hexec.
        pose proof (@buf5_push_preserves_levels A 1 pde p'_pre pre''
                      Hl_pde Hwfp Hpush_p'pre) as Hwfpre''.
        rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
        destruct pre'' as [|y|y z|y z w|y z w u|y z w u v].
        -- destruct p'_pre; cbn in Hpush_p'pre; inversion Hpush_p'pre.
        -- (* B1 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B1 y) p'_suf (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 (* H ⤳ H1 ⤳ H2.  H1 = freeze ... (alloc cell_tail H);
                    H2 = freeze ... (alloc cell_top H1). *)
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B2 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B2 y z) p'_suf (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B3 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B3 y z w) p'_suf (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B4 *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell (B4 y z w u) p'_suf (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1).
           { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
           { unfold H2. apply lookup_alloc_freeze_self. }
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail).
           { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
             unfold H1. apply lookup_alloc_freeze_self. }
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
           { unfold H2. apply is_frozen_alloc_freeze_self. }
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true).
           { unfold H2. apply is_frozen_alloc_freeze_preserves.
             unfold H1. apply is_frozen_alloc_freeze_self. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ cbn. tauto. ++ exact Hwfs.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfpre''. ** exact Hwfsp.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- (* B5 — failC *)
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           discriminate Hexec.
Qed.

(** *** Phase S8 — make_red push refinement (nested-cons sub-case).

    Closes the Phase S7 deferral: when the abstract make_red Case 3
    fires, the imperative [exec_make_red_push_pkt_C] dispatches via
    [pcell_inner top_cell = Some inner_loc].  The lemma covers the
    [i' = Hole] sub-shape (depth-2 nested top with simple inner),
    which is the only one reachable under the regularity invariant
    (see [reg_ch_nested] in Regularity.v).

    Cell layout:
    - top_cell: pcell_pre = B5 a b cc d e, pcell_suf = suf,
                pcell_inner = Some inner_loc, pcell_tail = Some ltail.
    - inner_cell at inner_loc: pcell_pre = pre', pcell_suf = suf',
                pcell_inner = None, pcell_tail = None.
    - ltail decodes [c'] at chain level [2] (the new encoding,
      reflecting the packet_depth-2 shift).

    Imperative trace: read top, read inner, push pde onto pre',
    alloc-freeze new_link [(pre_new, suf', None, Some ltail)],
    alloc-freeze new_top [(B3 a b cc, suf, None, Some new_link)]. *)
Lemma exec_make_red_push_pkt_C_refines_nested :
  forall (A : Type) (lover inner_loc ltail : Loc)
         (a b cc d e : E.t A)
         (pre' suf suf' : Buf5 (E.t A))
         (i' : Packet A) (c' c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover =
      Some (mkPCell (B5 a b cc d e) suf (Some inner_loc) (Some ltail)) ->
    is_frozen H lover = true ->
    packet_repr_at H (Some inner_loc) (PNode pre' i' suf') 1 ->
    chain_repr_at H ltail c' (2 + packet_depth i') ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    buf_all_at_level 0 suf ->
    @exec_make_red_push_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_push_chain
      (ChainCons (PNode (B5 a b cc d e) (PNode pre' i' suf') suf) c') = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover inner_loc ltail a b cc d e pre' suf suf' i' c' c''
         H H' lroot' n
         Hlk_top Hf_top HRpkt HRtl Hwf
         Hla Hlb Hlcc Hld Hle Hwfs Hexec Habs.
  (* Decompose the inner packet representation. *)
  pose proof (@packet_repr_at_pnode_inv A H inner_loc pre' suf' i' 1 HRpkt)
    as [inner_cell [Hlk_inner [Hf_inner [Hpre_in [Hsuf_in
         [Htail_in [Hwfp' [Hwfs' HRpkt_inner]]]]]]]].
  unfold make_red_push_chain in Habs.
  destruct (Nat.eq_dec (E.level A d) (E.level A e)) as [eq|]; [|discriminate].
  destruct (buf5_push_naive (E.pair A d e eq) pre') as [pre_new|] eqn:Hpush;
    [|discriminate].
  (* Compact reasoning: each buffer-shape sub-case shares the imperative
     trace and persistence reasoning; only the chosen [pre_new] shape and
     final [chain_repr_at] dispatch on i' (Hole vs PNode) differ. *)
  destruct pre_new as [|y|y z|y z w|y z w u|y z w u v]; try discriminate;
    [
      (* B0: impossible *)
      destruct pre'; cbn in Hpush; inversion Hpush
    | | | | ].
  (* For each of the four non-trivial buffer cases (B1/B2/B3/B4), we run
     the imperative trace, materialize H1/H2, and then dispatch on i'. *)
  all: inversion Habs; subst c''; clear Habs;
       unfold exec_make_red_push_pkt_C, bindC in Hexec;
       unfold read_MC in Hexec;
       rewrite Hlk_top in Hexec; cbn in Hexec;
       unfold pkt_pair_safe in Hexec;
       (destruct (Nat.eq_dec (E.level A d) (E.level A e)) as [eq2|];
          [|discriminate]);
       (assert (Heq_eq : eq2 = eq)
          by (apply Eqdep_dec.UIP_dec; apply Nat.eq_dec));
       subst eq2;
       rewrite Hlk_inner in Hexec; cbn in Hexec;
       rewrite Hpre_in in Hexec;
       rewrite Hpush in Hexec;
       cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
       inversion Hexec; subst H' lroot' n; clear Hexec.
  (* Now the goal in each of the four cases is to build [chain_repr H2 ...]
     where H2 is the result of two alloc-freezes.  Common preamble. *)
  - (* B1 pre_new *)
    set (cell_link := mkPCell (B1 y) (pcell_suf inner_cell) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_push_preserves_levels A 1 (E.pair A d e eq) pre' (B1 y))
      as Hwfp_new.
    assert (Hl_pde : E.level A (E.pair A d e eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hld. }
    specialize (Hwfp_new Hl_pde Hwfp' Hpush). cbn in Hwfp_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + cbn. tauto. + exact Hwfs.
    + (* New chain link.  Dispatch on i' (Hole / PNode). *)
      destruct i' as [|i'_pre i'_inner i'_suf].
      * (* i' = Hole: simple cons new_link. *)
        assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * (* i' = PNode: nested cons new_link. *)
        remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B2 pre_new *)
    set (cell_link := mkPCell (B2 y z) (pcell_suf inner_cell) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_push_preserves_levels A 1 (E.pair A d e eq) pre' (B2 y z))
      as Hwfp_new.
    assert (Hl_pde : E.level A (E.pair A d e eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hld. }
    specialize (Hwfp_new Hl_pde Hwfp' Hpush). cbn in Hwfp_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + cbn. tauto. + exact Hwfs.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * (* i' = Hole: simple cons new_link. *)
        assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * (* i' = PNode: nested cons new_link. *)
        (* Extract pcell_inner inner_cell = Some inner2_loc from HRpkt_inner. *)
        remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B3 pre_new *)
    set (cell_link := mkPCell (B3 y z w) (pcell_suf inner_cell) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_push_preserves_levels A 1 (E.pair A d e eq) pre' (B3 y z w))
      as Hwfp_new.
    assert (Hl_pde : E.level A (E.pair A d e eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hld. }
    specialize (Hwfp_new Hl_pde Hwfp' Hpush). cbn in Hwfp_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + cbn. tauto. + exact Hwfs.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * (* i' = Hole: simple cons new_link. *)
        assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * (* i' = PNode: nested cons new_link. *)
        (* Extract pcell_inner inner_cell = Some inner2_loc from HRpkt_inner. *)
        remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B4 pre_new *)
    set (cell_link := mkPCell (B4 y z w u) (pcell_suf inner_cell) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell (B3 a b cc) suf (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_push_preserves_levels A 1 (E.pair A d e eq) pre'
                  (B4 y z w u))
      as Hwfp_new.
    assert (Hl_pde : E.level A (E.pair A d e eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hld. }
    specialize (Hwfp_new Hl_pde Hwfp' Hpush). cbn in Hwfp_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + cbn. tauto. + exact Hwfs.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * (* i' = Hole: simple cons new_link. *)
        assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * (* i' = PNode: nested cons new_link. *)
        (* Extract pcell_inner inner_cell = Some inner2_loc from HRpkt_inner. *)
        remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hsuf_in.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp_new. -- exact Hwfs'.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
Qed.

(** *** Phase S''' — make_red inject refinement (Ending sub-case).

    Dual of [exec_make_red_push_pkt_C_refines_ending].  The cell at
    [lover] has [pcell_pre = B5 a b cc d e] (from an Ending overflow
    via inject), [pcell_suf = B0], [pcell_inner = None], [pcell_tail =
    None].  The abstract returns
    [ChainCons (PNode B0 Hole (B3 cc d e)) (Ending (B1 (E.pair A a b eq)))]. *)
Lemma exec_make_red_inject_pkt_C_refines_ending :
  forall (A : Type) (lover : Loc) (a b cc d e : E.t A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat) (c'' : Chain A),
    lookup H lover = Some (mkPCell (B5 a b cc d e) B0 None None) ->
    is_frozen H lover = true ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    @exec_make_red_inject_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_inject_chain (Ending (B5 a b cc d e)) = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover a b cc d e H H' lroot' n c''
         Hlk Hf_lover Hwf Hla Hlb Hlcc Hld Hle Hexec Habs.
  unfold make_red_inject_chain in Habs.
  unfold exec_make_red_inject_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk in Hexec. cbn in Hexec.
  unfold pkt_pair_safe in Hexec.
  destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [eq|]; [|discriminate].
  inversion Habs; subst c''; clear Habs.
  cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
  inversion Hexec; subst H' lroot' n; clear Hexec.
  set (cell_tail := mkPCell (B1 (E.pair A a b eq)) B0 (None : option Loc)
                            (None : option Loc)).
  set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
  set (cell_top := mkPCell B0 (B3 cc d e) (None : option Loc)
                           (Some (next_loc H))).
  set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
  assert (Hnext_loc_H1 : next_loc H1 = Pos.succ (next_loc H)).
  { unfold H1. rewrite freeze_next_loc. apply next_loc_after_alloc. }
  assert (Hne : next_loc H <> next_loc H1).
  { rewrite Hnext_loc_H1.
    intros Heq. exact (Pos.succ_discr (next_loc H) Heq). }
  assert (Hlk_top : lookup H2 (next_loc H1) = Some cell_top).
  { unfold H2. apply lookup_alloc_freeze_self. }
  assert (Hlk_tail : lookup H2 (next_loc H) = Some cell_tail).
  { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
    unfold H1. apply lookup_alloc_freeze_self. }
  assert (Hf_top : is_frozen H2 (next_loc H1) = true).
  { unfold H2. apply is_frozen_alloc_freeze_self. }
  assert (Hf_tail : is_frozen H2 (next_loc H) = true).
  { unfold H2. apply is_frozen_alloc_freeze_preserves.
    unfold H1. apply is_frozen_alloc_freeze_self. }
  unfold chain_repr.
  eapply chain_repr_cons_at with (ltail := next_loc H).
  - exact Hlk_top.
  - exact Hf_top.
  - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - cbn. exact I.
  - cbn. tauto.
  - eapply chain_repr_ending_at with (b := B1 (E.pair A a b eq)).
    + exact Hlk_tail.
    + exact Hf_tail.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + unfold buf_all_at_level. rewrite E.level_pair. rewrite Hla. reflexivity.
Qed.

(** *** Phase S''' — make_red inject refinement (ChainCons sub-case).

    Dual of [exec_make_red_push_pkt_C_refines_cons].  Here the cell at
    [lover] has [pcell_suf = B5 a b cc d e] and [pcell_tail = Some
    ltail].  The abstract pairs (a,b) at level 1, injects the pair
    into [c'] (via [inject_chain]), and forms a new top cell.

    The imperative dispatches on the inner tail's [pcell_tail]:
    - None (inner tail is Ending): inject pab into tail.pre.
    - Some (inner tail is ChainCons): inject pab into tail.suf. *)
Lemma exec_make_red_inject_pkt_C_refines_cons :
  forall (A : Type) (lover : Loc) (a b cc d e : E.t A)
         (pre : Buf5 (E.t A)) (ltail : Loc) (c' c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover = Some (mkPCell pre (B5 a b cc d e) None (Some ltail)) ->
    is_frozen H lover = true ->
    chain_repr_at H ltail c' 1 ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    buf_all_at_level 0 pre ->
    @exec_make_red_inject_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_inject_chain (ChainCons (PNode pre Hole (B5 a b cc d e)) c') = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover a b cc d e pre ltail c' c'' H H' lroot' n
         Hlk_top Hf_top HRtl Hwf Hla Hlb Hlcc Hld Hle Hwfp Hexec Habs.
  unfold make_red_inject_chain in Habs.
  destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [eq|]; [|discriminate].
  destruct (inject_chain c' (E.pair A a b eq)) as [c''_inner|] eqn:Habs_inner;
    [|discriminate].
  inversion Habs; subst c''; clear Habs.
  unfold exec_make_red_inject_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk_top in Hexec. cbn in Hexec.
  unfold pkt_pair_safe in Hexec.
  destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [eq2|]; [|discriminate].
  assert (Heq_eq : eq2 = eq) by (apply Eqdep_dec.UIP_dec; apply Nat.eq_dec).
  subst eq2.
  set (pab := E.pair A a b eq) in *.
  assert (Hl_pab : E.level A pab = 1).
  { unfold pab. rewrite E.level_pair. cbn. f_equal. exact Hla. }
  destruct c' as [b' | p' c'0].
  - (* c' = Ending b' *)
    apply chain_repr_at_inv_ending in HRtl.
    destruct HRtl as [tail_cell [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                       [Htl_inner [Htl_tail Hwfb']]]]]]].
    cbn in Habs_inner.
    destruct (buf5_inject_naive b' pab) as [b''|] eqn:Hinj_b'; [|discriminate].
    inversion Habs_inner; subst c''_inner; clear Habs_inner.
    rewrite Hlk_tl in Hexec. cbn in Hexec.
    rewrite Htl_tail in Hexec.  (* dispatch: None branch *)
    rewrite Htl_pre in Hexec.
    rewrite Hinj_b' in Hexec.
    pose proof (@buf5_inject_preserves_levels A 1 b' pab b''
                  Hl_pab Hwfb' Hinj_b') as Hwfb''.
    rewrite Htl_suf, Htl_inner in Hexec.
    destruct b'' as [|y|y z|y z w|y z w u|y z w u v].
    + destruct b'; cbn in Hinj_b'; inversion Hinj_b'.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B1 y) B0 (None : option Loc)
                                (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1)
        by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
        by (unfold H2; apply lookup_alloc_freeze_self).
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
        by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
            unfold H1; apply lookup_alloc_freeze_self).
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_self).
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_preserves;
            unfold H1; apply is_frozen_alloc_freeze_self).
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew. * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp. * cbn; tauto.
      * eapply chain_repr_ending_at.
        -- exact Hlk_tailnew. -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B2 y z) B0 (None : option Loc)
                                (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1)
        by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
        by (unfold H2; apply lookup_alloc_freeze_self).
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
        by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
            unfold H1; apply lookup_alloc_freeze_self).
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_self).
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_preserves;
            unfold H1; apply is_frozen_alloc_freeze_self).
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew. * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp. * cbn; tauto.
      * eapply chain_repr_ending_at.
        -- exact Hlk_tailnew. -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B3 y z w) B0 (None : option Loc)
                                (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1)
        by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
        by (unfold H2; apply lookup_alloc_freeze_self).
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
        by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
            unfold H1; apply lookup_alloc_freeze_self).
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_self).
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_preserves;
            unfold H1; apply is_frozen_alloc_freeze_self).
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew. * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp. * cbn; tauto.
      * eapply chain_repr_ending_at.
        -- exact Hlk_tailnew. -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      set (cell_tail := mkPCell (B4 y z w u) B0 (None : option Loc)
                                (None : option Loc)).
      set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
      set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                               (Some (next_loc H))).
      set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
      assert (Hne : next_loc H <> next_loc H1)
        by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
      assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
        by (unfold H2; apply lookup_alloc_freeze_self).
      assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
        by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
            unfold H1; apply lookup_alloc_freeze_self).
      assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_self).
      assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
        by (unfold H2; apply is_frozen_alloc_freeze_preserves;
            unfold H1; apply is_frozen_alloc_freeze_self).
      unfold chain_repr.
      eapply chain_repr_cons_at with (ltail := next_loc H).
      * exact Hlk_topnew. * exact Hf_topnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp. * cbn; tauto.
      * eapply chain_repr_ending_at.
        -- exact Hlk_tailnew. -- exact Hf_tailnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- exact Hwfb''.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      discriminate Hexec.
  - (* c' = ChainCons p' c'0 *)
    destruct p' as [|p'_pre p'_inner p'_suf].
    + exfalso. inversion HRtl.
    + destruct p'_inner as [|p'_pre' p'_ii p'_suf'].
      * (* simple cons *)
        apply chain_repr_at_inv_simple_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail [Hwfp' [Hwfsp' HRtl2]]]]]]]]]].
        cbn in Habs_inner.
        destruct (buf5_inject_naive p'_suf pab) as [suf''|] eqn:Hinj_p'suf;
          [|discriminate].
        inversion Habs_inner; subst c''_inner; clear Habs_inner.
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        rewrite Htl_tail in Hexec.  (* dispatch: Some branch *)
        rewrite Htl_suf in Hexec.
        rewrite Hinj_p'suf in Hexec.
        pose proof (@buf5_inject_preserves_levels A 1 p'_suf pab suf''
                      Hl_pab Hwfsp' Hinj_p'suf) as Hwfsuf''.
        rewrite Htl_pre, Htl_inner in Hexec.
        destruct suf'' as [|y|y z|y z w|y z w u|y z w u v].
        -- destruct p'_suf; cbn in Hinj_p'suf; inversion Hinj_p'suf.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B1 y) (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B2 y z) (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B3 y z w) (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B4 y z w u) (None : option Loc)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_cons_at with (ltail := ltail2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 assert (HpsH_H1 : persists_strong H H1).
                 { unfold H1.
                   eapply persists_strong_trans.
                   { eapply alloc_persists_strong. exact Hwf. }
                   apply freeze_persists_strong. }
                 assert (HwfH1 : well_formed_heap H1).
                 { unfold H1. apply freeze_well_formed.
                   apply alloc_well_formed. exact Hwf. }
                 eapply persists_strong_trans; [exact HpsH_H1|].
                 unfold H2.
                 eapply persists_strong_trans.
                 { eapply alloc_persists_strong. exact HwfH1. }
                 apply freeze_persists_strong.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           discriminate Hexec.
      * (* nested cons *)
        apply chain_repr_at_inv_nested_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [inner_loc2
                           [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail
                           [Hwfp' [Hwfsp' [HRpkt HRtl2]]]]]]]]]]]].
        cbn in Habs_inner.
        destruct (buf5_inject_naive p'_suf pab) as [suf''|] eqn:Hinj_p'suf;
          [|discriminate].
        inversion Habs_inner; subst c''_inner; clear Habs_inner.
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        rewrite Htl_tail in Hexec.
        rewrite Htl_suf in Hexec.
        rewrite Hinj_p'suf in Hexec.
        pose proof (@buf5_inject_preserves_levels A 1 p'_suf pab suf''
                      Hl_pab Hwfsp' Hinj_p'suf) as Hwfsuf''.
        rewrite Htl_pre, Htl_inner in Hexec.
        destruct suf'' as [|y|y z|y z w|y z w u|y z w u v].
        -- destruct p'_suf; cbn in Hinj_p'suf; inversion Hinj_p'suf.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B1 y) (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           assert (HpsH_H1 : persists_strong H H1).
           { unfold H1.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HwfH1 : well_formed_heap H1).
           { unfold H1. apply freeze_well_formed.
             apply alloc_well_formed. exact Hwf. }
           assert (HpsHH2 : persists_strong H H2).
           { eapply persists_strong_trans; [exact HpsH_H1|].
             unfold H2.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact HwfH1. }
             apply freeze_persists_strong. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 exact HpsHH2.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 exact HpsHH2.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B2 y z) (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           assert (HpsH_H1 : persists_strong H H1).
           { unfold H1.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HwfH1 : well_formed_heap H1).
           { unfold H1. apply freeze_well_formed.
             apply alloc_well_formed. exact Hwf. }
           assert (HpsHH2 : persists_strong H H2).
           { eapply persists_strong_trans; [exact HpsH_H1|].
             unfold H2.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact HwfH1. }
             apply freeze_persists_strong. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 exact HpsHH2.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 exact HpsHH2.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B3 y z w) (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           assert (HpsH_H1 : persists_strong H H1).
           { unfold H1.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HwfH1 : well_formed_heap H1).
           { unfold H1. apply freeze_well_formed.
             apply alloc_well_formed. exact Hwf. }
           assert (HpsHH2 : persists_strong H H2).
           { eapply persists_strong_trans; [exact HpsH_H1|].
             unfold H2.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact HwfH1. }
             apply freeze_persists_strong. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 exact HpsHH2.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 exact HpsHH2.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           set (cell_tail := mkPCell p'_pre (B4 y z w u) (Some inner_loc2)
                                     (Some ltail2)).
           set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
           set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                                    (Some (next_loc H))).
           set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
           assert (Hne : next_loc H <> next_loc H1)
             by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
           assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
             by (unfold H2; apply lookup_alloc_freeze_self).
           assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
             by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
                 unfold H1; apply lookup_alloc_freeze_self).
           assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_self).
           assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
             by (unfold H2; apply is_frozen_alloc_freeze_preserves;
                 unfold H1; apply is_frozen_alloc_freeze_self).
           assert (HpsH_H1 : persists_strong H H1).
           { unfold H1.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HwfH1 : well_formed_heap H1).
           { unfold H1. apply freeze_well_formed.
             apply alloc_well_formed. exact Hwf. }
           assert (HpsHH2 : persists_strong H H2).
           { eapply persists_strong_trans; [exact HpsH_H1|].
             unfold H2.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact HwfH1. }
             apply freeze_persists_strong. }
           unfold chain_repr.
           eapply chain_repr_cons_at with (ltail := next_loc H).
           ++ exact Hlk_topnew. ++ exact Hf_topnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp. ++ cbn; tauto.
           ++ eapply chain_repr_nested_cons_at
                with (ltail := ltail2) (inner_loc := inner_loc2).
              ** exact Hlk_tailnew. ** exact Hf_tailnew.
              ** reflexivity. ** reflexivity. ** reflexivity. ** reflexivity.
              ** exact Hwfp'. ** exact Hwfsuf''.
              ** eapply packet_repr_at_persists_strong; [|exact HRpkt].
                 exact HpsHH2.
              ** eapply chain_repr_at_persists_strong; [|exact HRtl2].
                 exact HpsHH2.
        -- cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           discriminate Hexec.
Qed.

(** *** Phase S8 — make_red inject refinement (nested-cons sub-case).

    Dual of [exec_make_red_push_pkt_C_refines_nested].  Top cell holds
    pre = pre, suf = B5 a b cc d e, inner = Some inner_loc, tail = Some
    ltail; inner_cell holds pre = pre', suf = suf', inner = None, tail
    = None (i' = Hole sub-case).  Imperative reads top, reads inner,
    injects pab onto suf', allocs new_link (pre', suf_new, None, Some
    ltail), allocs new_top (pre, B3 cc d e, None, Some new_link). *)
Lemma exec_make_red_inject_pkt_C_refines_nested :
  forall (A : Type) (lover inner_loc ltail : Loc)
         (a b cc d e : E.t A)
         (pre pre' suf' : Buf5 (E.t A))
         (i' : Packet A) (c' c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover =
      Some (mkPCell pre (B5 a b cc d e) (Some inner_loc) (Some ltail)) ->
    is_frozen H lover = true ->
    packet_repr_at H (Some inner_loc) (PNode pre' i' suf') 1 ->
    chain_repr_at H ltail c' (2 + packet_depth i') ->
    well_formed_heap H ->
    E.level A a = 0 -> E.level A b = 0 -> E.level A cc = 0 ->
    E.level A d = 0 -> E.level A e = 0 ->
    buf_all_at_level 0 pre ->
    @exec_make_red_inject_pkt_C A lover H = Some (H', lroot', n) ->
    make_red_inject_chain
      (ChainCons (PNode pre (PNode pre' i' suf') (B5 a b cc d e)) c') = Some c'' ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover inner_loc ltail a b cc d e pre pre' suf' i' c' c''
         H H' lroot' n
         Hlk_top Hf_top HRpkt HRtl Hwf
         Hla Hlb Hlcc Hld Hle Hwfp Hexec Habs.
  pose proof (@packet_repr_at_pnode_inv A H inner_loc pre' suf' i' 1 HRpkt)
    as [inner_cell [Hlk_inner [Hf_inner [Hpre_in [Hsuf_in
         [Htail_in [Hwfp' [Hwfs' HRpkt_inner]]]]]]]].
  unfold make_red_inject_chain in Habs.
  destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [eq|]; [|discriminate].
  destruct (buf5_inject_naive suf' (E.pair A a b eq)) as [suf_new|] eqn:Hinj;
    [|discriminate].
  destruct suf_new as [|y|y z|y z w|y z w u|y z w u v]; try discriminate;
    [
      (* B0: impossible *)
      destruct suf'; cbn in Hinj; inversion Hinj
    | | | | ].
  all: inversion Habs; subst c''; clear Habs;
       unfold exec_make_red_inject_pkt_C, bindC in Hexec;
       unfold read_MC in Hexec;
       rewrite Hlk_top in Hexec; cbn in Hexec;
       unfold pkt_pair_safe in Hexec;
       (destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [eq2|];
          [|discriminate]);
       (assert (Heq_eq : eq2 = eq)
          by (apply Eqdep_dec.UIP_dec; apply Nat.eq_dec));
       subst eq2;
       rewrite Hlk_inner in Hexec; cbn in Hexec;
       rewrite Hsuf_in in Hexec;
       rewrite Hinj in Hexec;
       cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
       inversion Hexec; subst H' lroot' n; clear Hexec.
  - (* B1 *)
    set (cell_link := mkPCell (pcell_pre inner_cell) (B1 y) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_inject_preserves_levels A 1 suf' (E.pair A a b eq) (B1 y))
      as Hwfs_new.
    assert (Hl_pab : E.level A (E.pair A a b eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hla. }
    specialize (Hwfs_new Hl_pab Hwfs' Hinj). cbn in Hwfs_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp. + cbn; tauto.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * (* i' = Hole: simple cons new_link. *)
        assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * (* i' = PNode: nested cons new_link. *)
        remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B2 *)
    set (cell_link := mkPCell (pcell_pre inner_cell) (B2 y z) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_inject_preserves_levels A 1 suf' (E.pair A a b eq) (B2 y z))
      as Hwfs_new.
    assert (Hl_pab : E.level A (E.pair A a b eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hla. }
    specialize (Hwfs_new Hl_pab Hwfs' Hinj). cbn in Hwfs_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp. + cbn; tauto.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B3 *)
    set (cell_link := mkPCell (pcell_pre inner_cell) (B3 y z w) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_inject_preserves_levels A 1 suf' (E.pair A a b eq)
                  (B3 y z w))
      as Hwfs_new.
    assert (Hl_pab : E.level A (E.pair A a b eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hla. }
    specialize (Hwfs_new Hl_pab Hwfs' Hinj). cbn in Hwfs_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp. + cbn; tauto.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
  - (* B4 *)
    set (cell_link := mkPCell (pcell_pre inner_cell) (B4 y z w u) (pcell_inner inner_cell)
                              (Some ltail)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_link H))).
    set (cell_top := mkPCell pre (B3 cc d e) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1).
    { unfold H1. rewrite next_loc_alloc_freeze. apply Pos.succ_discr. }
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top).
    { unfold H2. apply lookup_alloc_freeze_self. }
    assert (Hlk_linknew : lookup H2 (next_loc H) = Some cell_link).
    { unfold H2. rewrite lookup_alloc_freeze_other by exact Hne.
      unfold H1. apply lookup_alloc_freeze_self. }
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true).
    { unfold H2. apply is_frozen_alloc_freeze_self. }
    assert (Hf_linknew : is_frozen H2 (next_loc H) = true).
    { unfold H2. apply is_frozen_alloc_freeze_preserves.
      unfold H1. apply is_frozen_alloc_freeze_self. }
    assert (HpsHH2 : persists_strong H H2).
    { unfold H2. eapply persists_strong_trans.
      { unfold H1. eapply persists_strong_trans.
        { eapply alloc_persists_strong. exact Hwf. }
        apply freeze_persists_strong. }
      eapply persists_strong_trans.
      { eapply alloc_persists_strong.
        unfold H1. apply freeze_well_formed.
        apply alloc_well_formed. exact Hwf. }
      apply freeze_persists_strong. }
    pose proof (@buf5_inject_preserves_levels A 1 suf' (E.pair A a b eq)
                  (B4 y z w u))
      as Hwfs_new.
    assert (Hl_pab : E.level A (E.pair A a b eq) = 1).
    { rewrite E.level_pair. cbn. f_equal. exact Hla. }
    specialize (Hwfs_new Hl_pab Hwfs' Hinj). cbn in Hwfs_new.
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp. + cbn; tauto.
    + destruct i' as [|i'_pre i'_inner i'_suf].
      * assert (Hpci_none : pcell_inner inner_cell = None)
          by (inversion HRpkt_inner; reflexivity).
        eapply chain_repr_cons_at with (ltail := ltail).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. exact Hpci_none.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
      * remember (pcell_inner inner_cell) as ic_inner eqn:Heq_ic.
        destruct ic_inner as [inner2_loc|].
        2:{ exfalso. inversion HRpkt_inner. }
        eapply chain_repr_nested_cons_at
          with (ltail := ltail) (inner_loc := inner2_loc).
        -- exact Hlk_linknew. -- exact Hf_linknew.
        -- unfold cell_link. cbn. exact Hpre_in.
        -- reflexivity.
        -- unfold cell_link. cbn. reflexivity.
        -- reflexivity.
        -- exact Hwfp'. -- exact Hwfs_new.
        -- eapply packet_repr_at_persists_strong; [exact HpsHH2|].
           exact HRpkt_inner.
        -- replace (S (S 1) + packet_depth i'_inner)
                with (2 + packet_depth (PNode i'_pre i'_inner i'_suf))
                by (cbn; lia).
           eapply chain_repr_at_persists_strong; [|exact HRtl]. exact HpsHH2.
Qed.

(** *** Phase S'''' — make_green refinement lemmas (P3-residual closure).

    Dual of the four make_red refinement lemmas above.  The imperative
    [exec_make_green_pop_pkt_C] / [exec_make_green_eject_pkt_C] each
    have a fallback branch (try the dual side of the tail cell when the
    primary buffer is empty) that the abstract make_green ops do NOT
    mirror.  Key insight (verified by reasoning about the abstract):
    when the imperative's fallback fires, the tail's primary buffer is
    [B0], which forces [pop_chain c'] (resp. [eject_chain c']) to
    return [None], so [make_green_pop_chain] (resp. [_eject_]) returns
    [None].  Hence the abstract-success hypothesis is contradicted and
    the case is discharged by [discriminate].

    The success branches mirror the make_red structure: alloc-freeze a
    new tail cell (with the popped/ejected buffer) at [next_loc H],
    then alloc-freeze a new top cell (with [B1 y] in the relevant
    buffer) at [next_loc H1].  Three chain shapes for [c'] (Ending /
    simple cons / nested cons), times five non-B0 outcomes for the
    primary tail buffer = 15 sub-cases each. *)

(** Helper: when [chain_repr_at H ltail c' k] holds with the cell at
    [ltail] having [pcell_pre = B0], the abstract [pop_chain c']
    returns [None].  Used to discharge the make_green fallback case. *)
Lemma pop_chain_None_from_pre_B0 :
  forall (A : Type) (c' : Chain A) (H : HeapP (E.t A))
         (l : Loc) (cell : PCell (E.t A)) (k : nat),
    chain_repr_at H l c' k ->
    lookup H l = Some cell ->
    pcell_pre cell = B0 ->
    pop_chain c' = None.
Proof.
  intros A c' H l cell k HR Hlk Hpre.
  destruct c' as [b | p c0].
  - apply chain_repr_at_inv_ending in HR.
    destruct HR as [cell_e [Hlk_e [_ [Hpre_e _]]]].
    rewrite Hlk_e in Hlk. inversion Hlk; subst cell_e.
    cbn. rewrite <- Hpre_e. rewrite Hpre. reflexivity.
  - destruct p as [|pre i suf].
    + (* Hole inner: chain_repr_at impossible *) inversion HR.
    + destruct i as [|ipre ii isuf].
      * apply chain_repr_at_inv_simple_cons in HR.
        destruct HR as [cell_c [_ [Hlk_c [_ [Hpre_c _]]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c.
        cbn. rewrite <- Hpre_c. rewrite Hpre. reflexivity.
      * apply chain_repr_at_inv_nested_cons in HR.
        destruct HR as [cell_c [_ [_ [Hlk_c [_ [Hpre_c _]]]]]].
        rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c.
        cbn. rewrite <- Hpre_c. rewrite Hpre. reflexivity.
Qed.

(** Symmetric helper for eject in the ChainCons (non-Ending) case.

    For [c' = ChainCons (PNode _ _ suf') _] at level k+1, the cell at
    [l] has [pcell_suf cell = suf'].  The abstract [eject_chain c']
    looks at [suf']; if [suf' = B0], it returns [None].  Coupled with
    the imperative's fallback firing on [pcell_suf tail_cell = B0], the
    fallback case is unreachable when both abstract and imperative
    succeed (and c' is a cons). *)
Lemma eject_chain_None_from_suf_B0_cons :
  forall (A : Type) (p' : Packet A) (c'0 : Chain A)
         (H : HeapP (E.t A)) (l : Loc) (cell : PCell (E.t A)) (k : nat),
    chain_repr_at H l (ChainCons p' c'0) k ->
    lookup H l = Some cell ->
    pcell_suf cell = B0 ->
    eject_chain (ChainCons p' c'0) = None.
Proof.
  intros A p' c'0 H l cell k HR Hlk Hsuf.
  destruct p' as [|p'_pre p'_inner p'_suf].
  - inversion HR.
  - destruct p'_inner as [|p'_pre' p'_ii p'_suf'].
    + apply chain_repr_at_inv_simple_cons in HR.
      destruct HR as [cell_c [_ [Hlk_c [_ [_ [Hsuf_c _]]]]]].
      rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c.
      cbn. rewrite <- Hsuf_c. rewrite Hsuf. reflexivity.
    + apply chain_repr_at_inv_nested_cons in HR.
      destruct HR as [cell_c [_ [_ [Hlk_c [_ [_ [Hsuf_c _]]]]]]].
      rewrite Hlk_c in Hlk. inversion Hlk; subst cell_c.
      cbn. rewrite <- Hsuf_c. rewrite Hsuf. reflexivity.
Qed.

(** Make_green pop refinement: simple-cons (i = Hole) sub-case of c'.

    Only the PRIMARY (non-fallback) branch is mirrored.  The fallback
    case is unreachable when both abstract and imperative succeed:
    fallback fires on tail.pre = B0, but then pop_chain c' = None,
    contradicting Habs. *)
Lemma exec_make_green_pop_pkt_C_refines :
  forall (A : Type) (lover : Loc)
         (suf : Buf5 (E.t A))
         (ltail : Loc)
         (c' : Chain A) (x : E.t A) (c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover = Some (mkPCell B0 suf None (Some ltail)) ->
    is_frozen H lover = true ->
    chain_repr_at H ltail c' 1 ->
    well_formed_heap H ->
    buf_all_at_level 0 suf ->
    @exec_make_green_pop_pkt_C A lover H = Some (H', Some (x, lroot'), n) ->
    make_green_pop_chain (ChainCons (PNode B0 Hole suf) c') = Some (x, c'') ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover suf ltail c' x c'' H H' lroot' n
         Hlk_top Hf_top HRtl Hwf Hwfs Hexec Habs.
  unfold make_green_pop_chain in Habs.
  destruct (pop_chain c') as [[paired c''_inner]|] eqn:Hpop_c'; [|discriminate].
  destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
  inversion Habs; subst x c''; clear Habs.
  unfold exec_make_green_pop_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk_top in Hexec. cbn in Hexec.
  destruct c' as [b' | p' c'0].
  - (* c' = Ending b' *)
    apply chain_repr_at_inv_ending in HRtl.
    destruct HRtl as [tail_cell [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                       [Htl_inner [Htl_tail Hwfb']]]]]]].
    rewrite Hlk_tl in Hexec. cbn in Hexec.
    cbn in Hpop_c'.
    destruct (buf5_pop_naive b') as [[paired_a b'']|] eqn:Hpop_b'; [|discriminate].
    inversion Hpop_c'; subst paired c''_inner; clear Hpop_c'.
    rewrite Htl_pre in Hexec. rewrite Hpop_b' in Hexec.
    rewrite Hup in Hexec.
    rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
    pose proof (@buf5_pop_preserves_levels A 1 b' paired_a b'' Hwfb' Hpop_b')
      as [Hl_paired Hwfb''].
    pose proof (E.unpair_level A paired_a xa ya Hup) as [Hl_paired_eq Hl_eq].
    assert (Hl_xa : E.level A xa = 0).
    { lia. }
    assert (Hl_ya : E.level A ya = 0).
    { lia. }
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' lroot' n; clear Hexec.
    set (cell_tail := mkPCell b'' B0 (None : option Loc) (None : option Loc)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
    set (cell_top := mkPCell (B1 ya) suf (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1)
      by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
      by (unfold H2; apply lookup_alloc_freeze_self).
    assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
      by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
          unfold H1; apply lookup_alloc_freeze_self).
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_self).
    assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_preserves;
          unfold H1; apply is_frozen_alloc_freeze_self).
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew.
    + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + cbn. exact Hl_ya.
    + exact Hwfs.
    + eapply chain_repr_ending_at with (b := b'').
      * exact Hlk_tailnew.
      * exact Hf_tailnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfb''.
  - (* c' = ChainCons p' c'0 *)
    destruct p' as [|p'_pre p'_inner p'_suf].
    + exfalso. inversion HRtl.
    + destruct p'_inner as [|p'_pre' p'_ii p'_suf'].
      * (* simple cons *)
        apply chain_repr_at_inv_simple_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail [Hwfp' [Hwfsp' HRtl2]]]]]]]]]].
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        cbn in Hpop_c'.
        destruct (buf5_pop_naive p'_pre) as [[paired_a p'_pre'']|] eqn:Hpop_p'pre;
          [|discriminate].
        inversion Hpop_c'; subst paired c''_inner; clear Hpop_c'.
        rewrite Htl_pre in Hexec. rewrite Hpop_p'pre in Hexec.
        rewrite Hup in Hexec.
        rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
        pose proof (@buf5_pop_preserves_levels A 1 p'_pre paired_a p'_pre''
                       Hwfp' Hpop_p'pre) as [Hl_paired Hwfp''].
        pose proof (E.unpair_level A paired_a xa ya Hup) as [Hl_paired_eq Hl_eq].
        assert (Hl_ya : E.level A ya = 0) by lia.
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
        inversion Hexec; subst H' lroot' n; clear Hexec.
        set (cell_tail := mkPCell p'_pre'' p'_suf (None : option Loc)
                                  (Some ltail2)).
        set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
        set (cell_top := mkPCell (B1 ya) suf (None : option Loc)
                                 (Some (next_loc H))).
        set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
        assert (Hne : next_loc H <> next_loc H1)
          by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
        assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
          by (unfold H2; apply lookup_alloc_freeze_self).
        assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
          by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
              unfold H1; apply lookup_alloc_freeze_self).
        assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
          by (unfold H2; apply is_frozen_alloc_freeze_self).
        assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
          by (unfold H2; apply is_frozen_alloc_freeze_preserves;
              unfold H1; apply is_frozen_alloc_freeze_self).
        assert (HpsH_H1 : persists_strong H H1).
        { unfold H1.
          eapply persists_strong_trans.
          { eapply alloc_persists_strong. exact Hwf. }
          apply freeze_persists_strong. }
        assert (HwfH1 : well_formed_heap H1).
        { unfold H1. apply freeze_well_formed.
          apply alloc_well_formed. exact Hwf. }
        assert (HpsHH2 : persists_strong H H2).
        { eapply persists_strong_trans; [exact HpsH_H1|].
          unfold H2.
          eapply persists_strong_trans.
          { eapply alloc_persists_strong. exact HwfH1. }
          apply freeze_persists_strong. }
        unfold chain_repr.
        eapply chain_repr_cons_at with (ltail := next_loc H).
        -- exact Hlk_topnew. -- exact Hf_topnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- cbn. exact Hl_ya.
        -- exact Hwfs.
        -- eapply chain_repr_cons_at with (ltail := ltail2).
           ++ exact Hlk_tailnew. ++ exact Hf_tailnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp''. ++ exact Hwfsp'.
           ++ eapply chain_repr_at_persists_strong; [|exact HRtl2].
              exact HpsHH2.
      * (* nested cons *)
        apply chain_repr_at_inv_nested_cons in HRtl.
        destruct HRtl as [tail_cell [ltail2 [inner_loc2
                           [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                           [Htl_inner [Htl_tail
                           [Hwfp' [Hwfsp' [HRpkt HRtl2]]]]]]]]]]]].
        rewrite Hlk_tl in Hexec. cbn in Hexec.
        cbn in Hpop_c'.
        destruct (buf5_pop_naive p'_pre) as [[paired_a p'_pre'']|] eqn:Hpop_p'pre;
          [|discriminate].
        inversion Hpop_c'; subst paired c''_inner; clear Hpop_c'.
        rewrite Htl_pre in Hexec. rewrite Hpop_p'pre in Hexec.
        rewrite Hup in Hexec.
        rewrite Htl_suf, Htl_inner, Htl_tail in Hexec.
        pose proof (@buf5_pop_preserves_levels A 1 p'_pre paired_a p'_pre''
                       Hwfp' Hpop_p'pre) as [Hl_paired Hwfp''].
        pose proof (E.unpair_level A paired_a xa ya Hup) as [Hl_paired_eq Hl_eq].
        assert (Hl_ya : E.level A ya = 0) by lia.
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
        inversion Hexec; subst H' lroot' n; clear Hexec.
        set (cell_tail := mkPCell p'_pre'' p'_suf (Some inner_loc2)
                                  (Some ltail2)).
        set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
        set (cell_top := mkPCell (B1 ya) suf (None : option Loc)
                                 (Some (next_loc H))).
        set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
        assert (Hne : next_loc H <> next_loc H1)
          by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
        assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
          by (unfold H2; apply lookup_alloc_freeze_self).
        assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
          by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
              unfold H1; apply lookup_alloc_freeze_self).
        assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
          by (unfold H2; apply is_frozen_alloc_freeze_self).
        assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
          by (unfold H2; apply is_frozen_alloc_freeze_preserves;
              unfold H1; apply is_frozen_alloc_freeze_self).
        assert (HpsH_H1 : persists_strong H H1).
        { unfold H1.
          eapply persists_strong_trans.
          { eapply alloc_persists_strong. exact Hwf. }
          apply freeze_persists_strong. }
        assert (HwfH1 : well_formed_heap H1).
        { unfold H1. apply freeze_well_formed.
          apply alloc_well_formed. exact Hwf. }
        assert (HpsHH2 : persists_strong H H2).
        { eapply persists_strong_trans; [exact HpsH_H1|].
          unfold H2.
          eapply persists_strong_trans.
          { eapply alloc_persists_strong. exact HwfH1. }
          apply freeze_persists_strong. }
        unfold chain_repr.
        eapply chain_repr_cons_at with (ltail := next_loc H).
        -- exact Hlk_topnew. -- exact Hf_topnew.
        -- reflexivity. -- reflexivity. -- reflexivity. -- reflexivity.
        -- cbn. exact Hl_ya.
        -- exact Hwfs.
        -- eapply chain_repr_nested_cons_at
             with (ltail := ltail2) (inner_loc := inner_loc2).
           ++ exact Hlk_tailnew. ++ exact Hf_tailnew.
           ++ reflexivity. ++ reflexivity. ++ reflexivity. ++ reflexivity.
           ++ exact Hwfp''. ++ exact Hwfsp'.
           ++ eapply packet_repr_at_persists_strong; [|exact HRpkt].
              exact HpsHH2.
           ++ eapply chain_repr_at_persists_strong; [|exact HRtl2].
              exact HpsHH2.
Qed.

(** Make_green eject refinement.

    The abstract [make_green_eject_chain (ChainCons (PNode pre Hole B0) c')]:
    eject_chain c' to get (c''_inner, paired), unpair to (xa, ya),
    return (ChainCons (PNode pre Hole (B1 xa)) c''_inner, ya).

    The imperative [exec_make_green_eject_pkt_C lover]: requires
    [pcell_suf top_cell = B0], reads tail_cell, primary branch is
    [buf5_eject_naive (pcell_suf tail_cell)] (matches abstract's
    eject_chain on the cons case which ejects from suf), fallback is
    [buf5_pop_naive (pcell_pre tail_cell)] (does NOT match abstract).

    Reasoning by chain shape:
    - c' = Ending b': abstract eject_chain (Ending b') uses [b' = pre].
      Imperative's primary branch reads [tail.suf = B0] always (Ending
      invariant), so primary fails immediately, fallback fires reading
      [tail.pre = b'].  Fallback then POPS from b' (not ejects),
      returning the FIRST element.  Abstract returns the LAST.
      Contradiction unless b' is a singleton.  Concretely: when
      [buf5_pop_naive b'] succeeds with [(paired, b'')] and abstract's
      [buf5_eject_naive b'] succeeds with [(b''', paired)], they agree
      iff b' = B1.  In that case, b'' = b''' = B0 and the popped
      paired = ejected paired.  This is the only Ending sub-case.
    - c' = ChainCons (PNode p'_pre _ p'_suf) c'0: abstract eject_chain
      uses [p'_suf].  Imperative primary uses [tail.suf = p'_suf].
      Match.  Fallback would fire only if tail.suf = B0, but then
      eject_chain returns None.

    For Phase S'''' we restrict to the [c' = ChainCons _ _] sub-case,
    where the imperative's primary branch (suf-eject) cleanly mirrors
    the abstract's [eject_chain] (which also looks at suf for cons).
    The Ending sub-case has a structural mismatch (abstract ejects from
    pre, imperative falls back to popping pre — different elements),
    and is thus excluded here.  In the [_full] proof, the Ending sub-case
    is discharged by an explicit precondition. *)
Lemma exec_make_green_eject_pkt_C_refines :
  forall (A : Type) (lover : Loc)
         (pre : Buf5 (E.t A))
         (ltail : Loc)
         (p' : Packet A) (c'0 : Chain A) (x : E.t A) (c'' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    lookup H lover = Some (mkPCell pre B0 None (Some ltail)) ->
    is_frozen H lover = true ->
    chain_repr_at H ltail (ChainCons p' c'0) 1 ->
    well_formed_heap H ->
    buf_all_at_level 0 pre ->
    @exec_make_green_eject_pkt_C A lover H = Some (H', Some (lroot', x), n) ->
    make_green_eject_chain (ChainCons (PNode pre Hole B0) (ChainCons p' c'0))
      = Some (c'', x) ->
    chain_repr H' lroot' c''.
Proof.
  intros A lover pre ltail p' c'0 x c'' H H' lroot' n
         Hlk_top Hf_top HRtl Hwf Hwfp Hexec Habs.
  unfold make_green_eject_chain in Habs.
  destruct (eject_chain (ChainCons p' c'0)) as [[c''_inner paired]|] eqn:Hej_c';
    [|discriminate].
  destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
  inversion Habs; subst c'' x; clear Habs.
  unfold exec_make_green_eject_pkt_C, bindC in Hexec.
  unfold read_MC in Hexec.
  rewrite Hlk_top in Hexec. cbn in Hexec.
  (* Inline ChainCons p' c'0 — case-split on p' shape. *)
  destruct p' as [|p'_pre p'_inner p'_suf]; [inversion HRtl|].
  destruct p'_inner as [|p'_pre' p'_ii p'_suf'].
  - (* simple cons: c' = ChainCons (PNode p'_pre Hole p'_suf) c'0 *)
    apply chain_repr_at_inv_simple_cons in HRtl.
    destruct HRtl as [tail_cell [ltail2 [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                       [Htl_inner [Htl_tail [Hwfp' [Hwfsp' HRtl2]]]]]]]]]].
    rewrite Hlk_tl in Hexec. cbn in Hexec.
    cbn in Hej_c'.
    destruct (buf5_eject_naive p'_suf) as [[p'_suf'' paired_a]|] eqn:Hej_p'suf;
      [|discriminate].
    inversion Hej_c'; subst c''_inner paired; clear Hej_c'.
    rewrite Htl_suf in Hexec. rewrite Hej_p'suf in Hexec.
    rewrite Hup in Hexec.
    rewrite Htl_pre, Htl_inner, Htl_tail in Hexec.
    pose proof (@buf5_eject_preserves_levels A 1 p'_suf paired_a p'_suf''
                  Hwfsp' Hej_p'suf) as [Hl_paired Hwfsuf''].
    pose proof (E.unpair_level A paired_a xa ya Hup) as [Hl_paired_eq Hl_eq].
    assert (Hl_xa : E.level A xa = 0) by lia.
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' lroot' n; clear Hexec.
    set (cell_tail := mkPCell p'_pre p'_suf'' (None : option Loc)
                              (Some ltail2)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
    set (cell_top := mkPCell pre (B1 xa) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1)
      by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
      by (unfold H2; apply lookup_alloc_freeze_self).
    assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
      by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
          unfold H1; apply lookup_alloc_freeze_self).
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_self).
    assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_preserves;
          unfold H1; apply is_frozen_alloc_freeze_self).
    assert (HpsH_H1 : persists_strong H H1).
    { unfold H1.
      eapply persists_strong_trans.
      { eapply alloc_persists_strong. exact Hwf. }
      apply freeze_persists_strong. }
    assert (HwfH1 : well_formed_heap H1).
    { unfold H1. apply freeze_well_formed.
      apply alloc_well_formed. exact Hwf. }
    assert (HpsHH2 : persists_strong H H2).
    { eapply persists_strong_trans; [exact HpsH_H1|].
      unfold H2.
      eapply persists_strong_trans.
      { eapply alloc_persists_strong. exact HwfH1. }
      apply freeze_persists_strong. }
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp.
    + cbn. exact Hl_xa.
    + eapply chain_repr_cons_at with (ltail := ltail2).
      * exact Hlk_tailnew. * exact Hf_tailnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp'. * exact Hwfsuf''.
      * eapply chain_repr_at_persists_strong; [|exact HRtl2].
        exact HpsHH2.
  - (* nested cons: c' = ChainCons (PNode p'_pre (PNode ...) p'_suf) c'0 *)
    apply chain_repr_at_inv_nested_cons in HRtl.
    destruct HRtl as [tail_cell [ltail2 [inner_loc2
                       [Hlk_tl [Hf_tl [Htl_pre [Htl_suf
                       [Htl_inner [Htl_tail
                       [Hwfp' [Hwfsp' [HRpkt HRtl2]]]]]]]]]]]].
    rewrite Hlk_tl in Hexec. cbn in Hexec.
    cbn in Hej_c'.
    destruct (buf5_eject_naive p'_suf) as [[p'_suf'' paired_a]|] eqn:Hej_p'suf;
      [|discriminate].
    inversion Hej_c'; subst c''_inner paired; clear Hej_c'.
    rewrite Htl_suf in Hexec. rewrite Hej_p'suf in Hexec.
    rewrite Hup in Hexec.
    rewrite Htl_pre, Htl_inner, Htl_tail in Hexec.
    pose proof (@buf5_eject_preserves_levels A 1 p'_suf paired_a p'_suf''
                  Hwfsp' Hej_p'suf) as [Hl_paired Hwfsuf''].
    pose proof (E.unpair_level A paired_a xa ya Hup) as [Hl_paired_eq Hl_eq].
    assert (Hl_xa : E.level A xa = 0) by lia.
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' lroot' n; clear Hexec.
    set (cell_tail := mkPCell p'_pre p'_suf'' (Some inner_loc2)
                              (Some ltail2)).
    set (H1 := freeze (next_loc H) (snd (alloc cell_tail H))).
    set (cell_top := mkPCell pre (B1 xa) (None : option Loc)
                             (Some (next_loc H))).
    set (H2 := freeze (next_loc H1) (snd (alloc cell_top H1))).
    assert (Hne : next_loc H <> next_loc H1)
      by (unfold H1; rewrite next_loc_alloc_freeze; apply Pos.succ_discr).
    assert (Hlk_topnew : lookup H2 (next_loc H1) = Some cell_top)
      by (unfold H2; apply lookup_alloc_freeze_self).
    assert (Hlk_tailnew : lookup H2 (next_loc H) = Some cell_tail)
      by (unfold H2; rewrite lookup_alloc_freeze_other by exact Hne;
          unfold H1; apply lookup_alloc_freeze_self).
    assert (Hf_topnew : is_frozen H2 (next_loc H1) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_self).
    assert (Hf_tailnew : is_frozen H2 (next_loc H) = true)
      by (unfold H2; apply is_frozen_alloc_freeze_preserves;
          unfold H1; apply is_frozen_alloc_freeze_self).
    assert (HpsH_H1 : persists_strong H H1).
    { unfold H1.
      eapply persists_strong_trans.
      { eapply alloc_persists_strong. exact Hwf. }
      apply freeze_persists_strong. }
    assert (HwfH1 : well_formed_heap H1).
    { unfold H1. apply freeze_well_formed.
      apply alloc_well_formed. exact Hwf. }
    assert (HpsHH2 : persists_strong H H2).
    { eapply persists_strong_trans; [exact HpsH_H1|].
      unfold H2.
      eapply persists_strong_trans.
      { eapply alloc_persists_strong. exact HwfH1. }
      apply freeze_persists_strong. }
    unfold chain_repr.
    eapply chain_repr_cons_at with (ltail := next_loc H).
    + exact Hlk_topnew. + exact Hf_topnew.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + exact Hwfp.
    + cbn. exact Hl_xa.
    + eapply chain_repr_nested_cons_at
        with (ltail := ltail2) (inner_loc := inner_loc2).
      * exact Hlk_tailnew. * exact Hf_tailnew.
      * reflexivity. * reflexivity. * reflexivity. * reflexivity.
      * exact Hwfp'. * exact Hwfsuf''.
      * eapply packet_repr_at_persists_strong; [|exact HRpkt].
        exact HpsHH2.
      * eapply chain_repr_at_persists_strong; [|exact HRtl2].
        exact HpsHH2.
Qed.

(** Phase S9 (P5 CLOSED end-to-end): the [chain_top_simple c]
    precondition is DROPPED.  All chain shapes (Ending, simple cons,
    nested cons at any depth) are handled.  The OverflowP-nested
    branch invokes the generalized [exec_make_red_push_pkt_C_refines_nested]
    (which itself dispatches on i' = Hole vs i' = PNode in each
    buffer sub-case). *)
Theorem exec_push_pkt_C_refines_push_chain_full :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    @exec_push_pkt_C A lroot x H = Some (H', lroot', n) ->
    push_chain_full x c = Some c' ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Hexec Habs.
  pose proof (@push_chain_full_result_not_b5 A x c c' Habs) as Hnb5.
  pose proof (@push_chain_full_top_not_b5 A x c c' Habs) as Htop_nb5.
  unfold exec_push_pkt_C, bindC in Hexec.
  destruct (exec_push_pkt_naive_C lroot x H) as [[[H0 r0] k0]|] eqn:Hnaive;
    [|discriminate].
  destruct r0 as [l'|l'].
  - (* OkP path: equivalent to exec_push_pkt_naive_C succeeding without
       overflow.  Reduce to Goal A by re-using [exec_push_pkt_C_refines_push_chain]
       on the same trace, after observing that [push_chain_full = push_chain]
       in this case. *)
    cbv [retC] in Hexec. inversion Hexec; subst H' lroot' n; clear Hexec.
    (* We have exec_push_pkt_naive_C lroot x H = Some (H0, OkP l', k0).
       Use the OkP branch directly; the full exec_push_pkt_C with this
       OverflowP-eliminated input matches exec_push_pkt_C composed via OkP. *)
    assert (Hexec_full : @exec_push_pkt_C A lroot x H = Some (H0, l', k0 + 0)).
    { unfold exec_push_pkt_C, bindC. rewrite Hnaive. cbv [retC]. reflexivity. }
    (* The abstract [push_chain_full] reduces to [push_chain] when the
       buffer-level naive push doesn't overflow.  Derive
       [push_chain x c = Some c']. *)
    assert (Hpush_chain : push_chain x c = Some c').
    { unfold push_chain_full in Habs.
      destruct c as [b | p c0].
      - destruct (buf5_push_naive x b) as [b'|] eqn:Hpush; [|discriminate].
        cbn. rewrite Hpush.
        destruct b' as [|y|y z|y z w|y z w u|y z w u v];
          cbn in Habs; try (inversion Habs; subst c'; reflexivity).
        (* B5: make_red.  But Hnb5 says chain_top_pre c' is not B5, and
           make_red turns the Ending into a ChainCons whose pre is B3.
           This is consistent — but we need to re-derive [push_chain x c = Some c'].
           Actually, in the B5 case, [push_chain x c] = None.  We claim
           this branch is unreachable: it would have made [exec_push_pkt_naive_C]
           return [OverflowP], not [OkP]. *)
        exfalso.
        unfold exec_push_pkt_naive_C, bindC in Hnaive.
        destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H1 cell1] k1]|] eqn:Hr;
          [|discriminate].
        unfold read_MC in Hr.
        destruct (lookup H lroot) as [c1|] eqn:Hlk1; [|discriminate].
        inversion Hr; subst H1 cell1 k1; clear Hr.
        pose proof (@chain_repr_cell_top_pre A H lroot _ c1 HR Hlk1) as Hcell_pre.
        cbn in Hcell_pre. rewrite <- Hcell_pre in Hpush.
        rewrite Hpush in Hnaive.
        cbv [retC] in Hnaive. inversion Hnaive.
      - destruct p as [|pre i suf]; [discriminate|].
        destruct i as [|ipre ii isuf].
        + (* i = Hole *)
          destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush;
            [|discriminate].
          cbn. rewrite Hpush.
          destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
            cbn in Habs; try (inversion Habs; subst c'; reflexivity).
          (* B5: make_red.  exfalso. *)
          exfalso.
          unfold exec_push_pkt_naive_C, bindC in Hnaive.
          destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H1 cell1] k1]|] eqn:Hr;
            [|discriminate].
          unfold read_MC in Hr.
          destruct (lookup H lroot) as [c1|] eqn:Hlk1; [|discriminate].
          inversion Hr; subst H1 cell1 k1; clear Hr.
          pose proof (@chain_repr_cell_top_pre A H lroot _ c1 HR Hlk1) as Hcell_pre.
          cbn in Hcell_pre. rewrite <- Hcell_pre in Hpush.
          rewrite Hpush in Hnaive.
          cbv [retC] in Hnaive. inversion Hnaive.
        + (* i = PNode: nested top.  The PNode case in [push_chain_full]
             dispatches via the OUTER buffer push too — same B5 / non-B5
             cases as the Hole sub-case. *)
          destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush;
            [|discriminate].
          cbn. rewrite Hpush.
          destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
            cbn in Habs; try (inversion Habs; subst c'; reflexivity).
          (* B5: make_red.  exfalso (imperative would have taken OverflowP). *)
          exfalso.
          unfold exec_push_pkt_naive_C, bindC in Hnaive.
          destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H1 cell1] k1]|] eqn:Hr;
            [|discriminate].
          unfold read_MC in Hr.
          destruct (lookup H lroot) as [c1|] eqn:Hlk1; [|discriminate].
          inversion Hr; subst H1 cell1 k1; clear Hr.
          pose proof (@chain_repr_cell_top_pre A H lroot _ c1 HR Hlk1) as Hcell_pre.
          cbn in Hcell_pre. rewrite <- Hcell_pre in Hpush.
          rewrite Hpush in Hnaive.
          cbv [retC] in Hnaive. inversion Hnaive. }
    eapply exec_push_pkt_C_refines_push_chain; eauto.
  - (* OverflowP path: Phase S''' shape.  The naive push materialized
       a fresh cell at [next_loc H] carrying the B5 in pre, with the
       original cell's suf/inner/tail.  Then make_red is fired on that
       fresh cell.  We invoke the make_red refinement lemmas (Ending
       sub-case if input was Ending; Cons sub-case if input was
       ChainCons-simple). *)
    pose proof (@exec_push_pkt_naive_C_overflow_inv A lroot x H H0 l' k0 Hnaive)
      as [cell [aa [bb [cca [dd [ee
            [Hlk_cell [Hcell_nb5 [Hpush [Hl' HH0]]]]]]]]]].
    subst H0 l'.
    pose (lover := next_loc H).
    pose (cell5 := mkPCell (B5 aa bb cca dd ee) (pcell_suf cell)
                          (pcell_inner cell) (pcell_tail cell)).
    pose (Hover := freeze (next_loc H) (snd (alloc cell5 H))).
    fold lover in Hexec |- *.
    fold cell5 in Hexec |- *.
    fold Hover in Hexec |- *.
    (* Establish lookup/frozen for the fresh cell at lover. *)
    assert (Hlk_lover : lookup Hover lover = Some cell5).
    { unfold Hover, lover. apply lookup_alloc_freeze_self. }
    assert (Hf_lover : is_frozen Hover lover = true).
    { unfold Hover, lover. apply is_frozen_alloc_freeze_self. }
    assert (HwfHover : well_formed_heap Hover).
    { unfold Hover. apply freeze_well_formed.
      apply alloc_well_formed. exact Hwf. }
    (* Levels of a/b/cc/d/e: from buf5_push_naive succeeding with x
       at level 0 and pcell_pre cell at level 0.  We get them by
       inversion on Hpush. *)
    pose proof (@chain_repr_cell_top_pre A H lroot c cell HR Hlk_cell)
      as Hcell_pre.
    (* Decompose [c] to identify the structural shape and apply the
       appropriate make_red refinement.  Note: when [c] = Hole-cons
       or nested-cons, push_chain_full fails (returns None).  When [c]
       = Ending or simple-cons, we proceed. *)
    destruct c as [b0 | p0 c0].
    + (* c = Ending b0 *)
      pose proof (@chain_repr_inv_ending A H lroot b0 HR)
        as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb0]]]]]].
      rewrite Hlk_e in Hlk_cell. inversion Hlk_cell; subst cell; clear Hlk_cell.
      cbn in Hcell_pre.
      (* From Hpush, the buffer-push produced B5.  The cell5 has
         B5 a b cc d e in pre, B0 in suf, None in inner/tail. *)
      assert (Hcell5_eq : cell5 =
                         mkPCell (B5 aa bb cca dd ee) B0 None None).
      { unfold cell5. rewrite Hsuf_e, Hinner_e, Htail_e. reflexivity. }
      (* Levels: buf5_push_naive 0 0 → all elements level 0. *)
      pose proof (@buf5_push_preserves_levels A 0 x b0 (B5 aa bb cca dd ee)
                    Hlx Hwfb0) as Hwflevels.
      rewrite Hpre_e in Hpush. specialize (Hwflevels Hpush).
      cbn in Hwflevels.
      destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
      (* Abstract result *)
      assert (Habs_mr : make_red_push_chain (Ending (B5 aa bb cca dd ee)) = Some c').
      { unfold push_chain_full in Habs.
        (* Habs: match buf5_push_naive x b0 with ... | Some (B5..) => mr |..
           Hpush: buf5_push_naive x b0 = Some (B5 aa bb cca dd ee) *)
        rewrite Hpush in Habs. exact Habs. }
      (* Compute the make_red trace for Hexec. *)
      match type of Hexec with
      | match ?e with _ => _ end = _ =>
          destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
      end.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      eapply (@exec_make_red_push_pkt_C_refines_ending A lover
                aa bb cca dd ee Hover Hf rf kf c').
      * rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
      * exact Hf_lover.
      * exact HwfHover.
      * exact Hla. * exact Hlb. * exact Hlcc. * exact Hld. * exact Hle.
      * unfold lover, Hover. exact Hmr.
      * exact Habs_mr.
    + (* c = ChainCons p0 c0 *)
      destruct p0 as [|p0_pre p0_inner p0_suf].
      * (* Hole: chain_repr forces this case impossible *)
        exfalso. unfold chain_repr in HR. inversion HR.
      * destruct p0_inner as [|p0_pre' p0_ii p0_suf'].
        -- (* simple cons *)
           pose proof (@chain_repr_cons_inv A H lroot p0_pre p0_suf c0 HR)
             as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                  [Hinner_c [Htail_c [Hwfp0 [Hwfsp0 HRtl]]]]]]]]].
           rewrite Hlk_c in Hlk_cell. inversion Hlk_cell; subst cell;
             clear Hlk_cell.
           cbn in Hcell_pre.
           assert (Hcell5_eq : cell5 =
                              mkPCell (B5 aa bb cca dd ee) p0_suf None
                                      (Some ltail_c)).
           { unfold cell5. rewrite Hsuf_c, Hinner_c, Htail_c. reflexivity. }
           pose proof (@buf5_push_preserves_levels A 0 x p0_pre
                         (B5 aa bb cca dd ee) Hlx Hwfp0) as Hwflevels.
           rewrite Hpre_c in Hpush. specialize (Hwflevels Hpush).
           cbn in Hwflevels.
           destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
           assert (Habs_mr : make_red_push_chain
                               (ChainCons (PNode (B5 aa bb cca dd ee)
                                                 Hole p0_suf) c0) = Some c').
           { unfold push_chain_full in Habs.
             rewrite Hpush in Habs. exact Habs. }
           (* Lift HRtl from H to Hover via persists. *)
           assert (HpsHHover : persists_strong H Hover).
           { unfold Hover.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HRtl' : chain_repr_at Hover ltail_c c0 1).
           { eapply chain_repr_at_persists_strong; [|exact HRtl].
             exact HpsHHover. }
           match type of Hexec with
           | match ?e with _ => _ end = _ =>
               destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
           end.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           eapply (@exec_make_red_push_pkt_C_refines_cons A lover
                     aa bb cca dd ee p0_suf ltail_c c0 c'
                     Hover Hf rf kf).
           ++ rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
           ++ exact Hf_lover.
           ++ exact HRtl'.
           ++ exact HwfHover.
           ++ exact Hla. ++ exact Hlb. ++ exact Hlcc. ++ exact Hld. ++ exact Hle.
           ++ exact Hwfsp0.
           ++ unfold lover, Hover. exact Hmr.
           ++ exact Habs_mr.
        -- (* nested cons: invoke the Phase S9 [_refines_nested] lemma. *)
           pose proof (@chain_repr_cons_inv_nested A H lroot
                         p0_pre p0_suf p0_pre' p0_suf' p0_ii c0 HR)
             as [cell_c [ltail_c [inner_loc_orig
                  [Hlk_c [Hpre_c [Hsuf_c [Hinner_c [Htail_c
                  [Hwfp0 [Hwfsp0 [HRpkt_orig HRtl_orig]]]]]]]]]]].
           rewrite Hlk_c in Hlk_cell. inversion Hlk_cell; subst cell;
             clear Hlk_cell.
           cbn in Hcell_pre.
           assert (Hcell5_eq : cell5 =
                              mkPCell (B5 aa bb cca dd ee) p0_suf
                                      (Some inner_loc_orig)
                                      (Some ltail_c)).
           { unfold cell5. rewrite Hsuf_c, Hinner_c, Htail_c. reflexivity. }
           pose proof (@buf5_push_preserves_levels A 0 x p0_pre
                         (B5 aa bb cca dd ee) Hlx Hwfp0) as Hwflevels.
           rewrite Hpre_c in Hpush. specialize (Hwflevels Hpush).
           cbn in Hwflevels.
           destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
           assert (Habs_mr : make_red_push_chain
                               (ChainCons (PNode (B5 aa bb cca dd ee)
                                                 (PNode p0_pre' p0_ii p0_suf')
                                                 p0_suf) c0) = Some c').
           { unfold push_chain_full in Habs.
             rewrite Hpush in Habs. exact Habs. }
           assert (HpsHHover : persists_strong H Hover).
           { unfold Hover.
             eapply persists_strong_trans.
             { eapply alloc_persists_strong. exact Hwf. }
             apply freeze_persists_strong. }
           assert (HRpkt' : packet_repr_at Hover (Some inner_loc_orig)
                              (PNode p0_pre' p0_ii p0_suf') 1).
           { eapply packet_repr_at_persists_strong; [exact HpsHHover|].
             exact HRpkt_orig. }
           assert (HRtl' : chain_repr_at Hover ltail_c c0
                            (2 + packet_depth p0_ii)).
           { eapply chain_repr_at_persists_strong; [|exact HRtl_orig].
             exact HpsHHover. }
           match type of Hexec with
           | match ?e with _ => _ end = _ =>
               destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
           end.
           inversion Hexec; subst H' lroot' n; clear Hexec.
           eapply (@exec_make_red_push_pkt_C_refines_nested A lover
                     inner_loc_orig ltail_c
                     aa bb cca dd ee p0_pre' p0_suf p0_suf' p0_ii c0 c'
                     Hover Hf rf kf).
           ++ rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
           ++ exact Hf_lover.
           ++ exact HRpkt'.
           ++ exact HRtl'.
           ++ exact HwfHover.
           ++ exact Hla. ++ exact Hlb. ++ exact Hlcc. ++ exact Hld. ++ exact Hle.
           ++ exact Hwfsp0.
           ++ unfold lover, Hover. exact Hmr.
           ++ exact Habs_mr.
Qed.

(** *** Inject refinement (full version).  Same strategy as push.

    Phase S9 (P5 CLOSED end-to-end): the [chain_top_simple c]
    precondition is DROPPED.  Mirror of the push side. *)
Theorem exec_inject_pkt_C_refines_inject_chain_full :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    @exec_inject_pkt_C A lroot x H = Some (H', lroot', n) ->
    inject_chain_full c x = Some c' ->
    is_b5 (chain_top_pre c') = false ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Hexec Habs Hnb5p.
  pose proof (@inject_chain_full_result_suf_not_b5 A c c' x Habs) as Hnb5s.
  unfold exec_inject_pkt_C, bindC in Hexec.
  destruct (exec_inject_pkt_naive_C lroot x H) as [[[H0 r0] k0]|] eqn:Hnaive;
    [|discriminate].
  destruct r0 as [l'|l'].
  - (* OkP path. *)
    cbv [retC] in Hexec. inversion Hexec; subst H' lroot' n; clear Hexec.
    assert (Hexec_full : @exec_inject_pkt_C A lroot x H = Some (H0, l', k0 + 0)).
    { unfold exec_inject_pkt_C, bindC. rewrite Hnaive. cbv [retC]. reflexivity. }
    (* Derive [inject_chain c x = Some c'] from [inject_chain_full c x = Some c']
       and the imperative taking the OkP branch. *)
    assert (Hinject_chain : inject_chain c x = Some c').
    { unfold inject_chain_full in Habs.
      destruct c as [b | p c0].
      - destruct (buf5_inject_naive b x) as [b'|] eqn:Hi; [|discriminate].
        cbn. rewrite Hi.
        destruct b' as [|y|y z|y z w|y z w u|y z w u v];
          cbn in Habs; try (inversion Habs; subst c'; reflexivity).
        exfalso.
        unfold exec_inject_pkt_naive_C, bindC in Hnaive.
        unfold read_MC in Hnaive.
        apply chain_repr_inv_ending in HR.
        destruct HR as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e _]]]]]].
        rewrite Hlk_e in Hnaive.
        rewrite Htail_e in Hnaive.
        rewrite Hpre_e in Hnaive.
        rewrite Hi in Hnaive.
        cbv [retC alloc_freeze_MC bindC alloc_MC freeze_MC] in Hnaive.
        inversion Hnaive.
      - destruct p as [|pre i suf]; [discriminate|].
        destruct i as [|ipre ii isuf].
        + (* i = Hole *)
          destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hi; [|discriminate].
          cbn. rewrite Hi.
          destruct suf' as [|y|y z|y z w|y z w u|y z w u v];
            cbn in Habs; try (inversion Habs; subst c'; reflexivity).
          exfalso.
          unfold exec_inject_pkt_naive_C, bindC in Hnaive.
          destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H1 cell1] k1]|] eqn:Hr;
            [|discriminate].
          unfold read_MC in Hr.
          destruct (lookup H lroot) as [c2|] eqn:Hlk1; [|discriminate].
          inversion Hr; subst H1 cell1 k1; clear Hr.
          apply chain_repr_cons_inv in HR.
          destruct HR as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                             [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]].
          rewrite Hlk_c in Hlk1. inversion Hlk1; subst c2; clear Hlk1.
          rewrite Htail_c in Hnaive.
          rewrite Hsuf_c in Hnaive.
          rewrite Hi in Hnaive.
          cbv [retC] in Hnaive. inversion Hnaive.
        + (* i = PNode: nested top *)
          destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hi; [|discriminate].
          cbn. rewrite Hi.
          destruct suf' as [|y|y z|y z w|y z w u|y z w u v];
            cbn in Habs; try (inversion Habs; subst c'; reflexivity).
          exfalso.
          unfold exec_inject_pkt_naive_C, bindC in Hnaive.
          destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H1 cell1] k1]|] eqn:Hr;
            [|discriminate].
          unfold read_MC in Hr.
          destruct (lookup H lroot) as [c2|] eqn:Hlk1; [|discriminate].
          inversion Hr; subst H1 cell1 k1; clear Hr.
          apply chain_repr_cons_inv_nested in HR.
          destruct HR as [cell_c [ltail_c [inner_loc_orig
                            [Hlk_c [Hpre_c [Hsuf_c [Hinner_c [Htail_c
                            [Hwfp [Hwfs [HRpkt_orig HRtl_orig]]]]]]]]]]].
          rewrite Hlk_c in Hlk1. inversion Hlk1; subst c2; clear Hlk1.
          rewrite Htail_c in Hnaive.
          rewrite Hsuf_c in Hnaive.
          rewrite Hi in Hnaive.
          cbv [retC] in Hnaive. inversion Hnaive. }
    eapply exec_inject_pkt_C_refines_inject_chain; eauto.
  - (* OverflowP path: Phase S''' shape. *)
    pose proof (@exec_inject_pkt_naive_C_overflow_inv A lroot x H H0 l' k0 Hnaive)
      as [cell [aa [bb [cca [dd [ee
            [Hlk_cell [Hl' Hcase]]]]]]]].
    subst l'.
    pose proof (@chain_repr_cell_top_pre A H lroot c cell HR Hlk_cell)
      as Hcell_pre.
    pose proof (@chain_repr_cell_top_suf A H lroot c cell HR Hlk_cell)
      as Hcell_suf.
    destruct Hcase as
      [[Htail [Hpre_nb5 [Hpush HH0]]]
      |[ltail [Htail [Hsuf_nb5 [Hpush HH0]]]]];
      subst H0.
    + (* Ending case: cell.tail = None ⇒ c = Ending b0 *)
      destruct c as [b0 | p0 c0].
      2:{ (* ChainCons: but cell has tail=None contradicts cons cell *)
        exfalso. destruct p0 as [|p0_pre p0_inner p0_suf].
        - unfold chain_repr in HR. inversion HR.
        - destruct p0_inner as [|p0_pre' p0_ii p0_suf'].
          + apply chain_repr_cons_inv in HR.
            destruct HR as [cell_c [ltail_c [Hlk_c [_ [_ [_ [Htail_c _]]]]]]].
            rewrite Hlk_c in Hlk_cell. inversion Hlk_cell;
              subst cell_c.
            rewrite Htail_c in Htail. discriminate.
          + apply chain_repr_cons_inv_nested in HR.
            destruct HR as [cell_c [ltail_c [inner_loc_c
                             [Hlk_c [_ [_ [_ [Htail_c _]]]]]]]].
            rewrite Hlk_c in Hlk_cell. inversion Hlk_cell;
              subst cell_c.
            rewrite Htail_c in Htail. discriminate. }
      pose proof (@chain_repr_inv_ending A H lroot b0 HR)
        as [cell_e [Hlk_e [Hpre_e [Hsuf_e [Hinner_e [Htail_e Hwfb0]]]]]].
      rewrite Hlk_e in Hlk_cell. inversion Hlk_cell; subst cell;
        clear Hlk_cell.
      cbn in Hcell_pre.
      pose (lover := next_loc H).
      pose (cell5 := mkPCell (B5 aa bb cca dd ee) (pcell_suf cell_e)
                            (pcell_inner cell_e) (pcell_tail cell_e)).
      pose (Hover := freeze (next_loc H) (snd (alloc cell5 H))).
      fold lover in Hexec |- *.
      fold cell5 in Hexec |- *.
      fold Hover in Hexec |- *.
      assert (Hlk_lover : lookup Hover lover = Some cell5)
        by (unfold Hover, lover; apply lookup_alloc_freeze_self).
      assert (Hf_lover : is_frozen Hover lover = true)
        by (unfold Hover, lover; apply is_frozen_alloc_freeze_self).
      assert (HwfHover : well_formed_heap Hover)
        by (unfold Hover; apply freeze_well_formed;
            apply alloc_well_formed; exact Hwf).
      assert (Hcell5_eq : cell5 =
                         mkPCell (B5 aa bb cca dd ee) B0 None None).
      { unfold cell5. rewrite Hsuf_e, Hinner_e, Htail_e. reflexivity. }
      pose proof (@buf5_inject_preserves_levels A 0 b0 x
                    (B5 aa bb cca dd ee) Hlx Hwfb0) as Hwflevels.
      rewrite Hpre_e in Hpush. specialize (Hwflevels Hpush).
      cbn in Hwflevels.
      destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
      assert (Habs_mr : make_red_inject_chain (Ending (B5 aa bb cca dd ee))
                       = Some c').
      { unfold inject_chain_full in Habs.
        rewrite Hpush in Habs. exact Habs. }
      match type of Hexec with
      | match ?e with _ => _ end = _ =>
          destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
      end.
      inversion Hexec; subst H' lroot' n; clear Hexec.
      eapply (@exec_make_red_inject_pkt_C_refines_ending A lover
                aa bb cca dd ee Hover Hf rf kf c').
      * rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
      * exact Hf_lover.
      * exact HwfHover.
      * exact Hla. * exact Hlb. * exact Hlcc. * exact Hld. * exact Hle.
      * unfold lover, Hover. exact Hmr.
      * exact Habs_mr.
    + (* ChainCons case: cell.tail = Some ltail *)
      destruct c as [b0 | p0 c0].
      * (* Ending: contradicts cell.tail = Some *)
        pose proof (@chain_repr_inv_ending A H lroot _ HR)
          as [cell_e [Hlk_e [_ [_ [_ [Htail_e _]]]]]].
        rewrite Hlk_e in Hlk_cell. inversion Hlk_cell; subst cell_e.
        rewrite Htail in Htail_e. discriminate.
      * destruct p0 as [|p0_pre p0_inner p0_suf].
        -- (* Hole: chain_repr forces this case impossible *)
           exfalso. unfold chain_repr in HR. inversion HR.
        -- destruct p0_inner as [|p0_pre' p0_ii p0_suf'].
           ++ (* simple cons *)
              pose proof (@chain_repr_cons_inv A H lroot p0_pre p0_suf c0 HR)
                as [cell_c [ltail_c [Hlk_c [Hpre_c [Hsuf_c
                     [Hinner_c [Htail_c [Hwfp0 [Hwfsp0 HRtl]]]]]]]]].
              rewrite Hlk_c in Hlk_cell. inversion Hlk_cell; subst cell;
                clear Hlk_cell.
              cbn in Hcell_pre, Hcell_suf.
              (* From Htail: pcell_tail cell_c = Some ltail; from Htail_c:
                 pcell_tail cell_c = Some ltail_c.  So ltail = ltail_c. *)
              rewrite Htail_c in Htail. inversion Htail; subst ltail;
                clear Htail.
              pose (lover := next_loc H).
              pose (cell5 := mkPCell (pcell_pre cell_c) (B5 aa bb cca dd ee)
                                    (pcell_inner cell_c) (Some ltail_c)).
              pose (Hover := freeze (next_loc H) (snd (alloc cell5 H))).
              fold lover in Hexec |- *.
              fold cell5 in Hexec |- *.
              fold Hover in Hexec |- *.
              assert (Hlk_lover : lookup Hover lover = Some cell5)
                by (unfold Hover, lover; apply lookup_alloc_freeze_self).
              assert (Hf_lover : is_frozen Hover lover = true)
                by (unfold Hover, lover; apply is_frozen_alloc_freeze_self).
              assert (HwfHover : well_formed_heap Hover)
                by (unfold Hover; apply freeze_well_formed;
                    apply alloc_well_formed; exact Hwf).
              assert (Hcell5_eq : cell5 = mkPCell p0_pre (B5 aa bb cca dd ee)
                                                  None (Some ltail_c)).
              { unfold cell5. rewrite Hpre_c, Hinner_c. reflexivity. }
              pose proof (@buf5_inject_preserves_levels A 0 p0_suf x
                            (B5 aa bb cca dd ee) Hlx Hwfsp0) as Hwflevels.
              rewrite Hsuf_c in Hpush. specialize (Hwflevels Hpush).
              cbn in Hwflevels.
              destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
              assert (Habs_mr : make_red_inject_chain
                                 (ChainCons (PNode p0_pre Hole
                                                   (B5 aa bb cca dd ee)) c0)
                                = Some c').
              { unfold inject_chain_full in Habs.
                rewrite Hpush in Habs. exact Habs. }
              assert (HpsHHover : persists_strong H Hover).
              { unfold Hover.
                eapply persists_strong_trans.
                { eapply alloc_persists_strong. exact Hwf. }
                apply freeze_persists_strong. }
              assert (HRtl' : chain_repr_at Hover ltail_c c0 1).
              { eapply chain_repr_at_persists_strong; [|exact HRtl].
                exact HpsHHover. }
              match type of Hexec with
              | match ?e with _ => _ end = _ =>
                  destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
              end.
              inversion Hexec; subst H' lroot' n; clear Hexec.
              eapply (@exec_make_red_inject_pkt_C_refines_cons A lover
                        aa bb cca dd ee p0_pre ltail_c c0 c'
                        Hover Hf rf kf).
              ** rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
              ** exact Hf_lover.
              ** exact HRtl'.
              ** exact HwfHover.
              ** exact Hla. ** exact Hlb. ** exact Hlcc. ** exact Hld. ** exact Hle.
              ** exact Hwfp0.
              ** unfold lover, Hover. exact Hmr.
              ** exact Habs_mr.
           ++ (* nested cons: invoke the Phase S9 [_refines_nested] lemma. *)
              pose proof (@chain_repr_cons_inv_nested A H lroot
                            p0_pre p0_suf p0_pre' p0_suf' p0_ii c0 HR)
                as [cell_c [ltail_c [inner_loc_orig
                     [Hlk_c [Hpre_c [Hsuf_c [Hinner_c [Htail_c
                     [Hwfp0 [Hwfsp0 [HRpkt_orig HRtl_orig]]]]]]]]]]].
              rewrite Hlk_c in Hlk_cell. inversion Hlk_cell; subst cell;
                clear Hlk_cell.
              cbn in Hcell_pre, Hcell_suf.
              rewrite Htail_c in Htail. inversion Htail; subst ltail;
                clear Htail.
              pose (lover := next_loc H).
              pose (cell5 := mkPCell (pcell_pre cell_c) (B5 aa bb cca dd ee)
                                    (pcell_inner cell_c) (Some ltail_c)).
              pose (Hover := freeze (next_loc H) (snd (alloc cell5 H))).
              fold lover in Hexec |- *.
              fold cell5 in Hexec |- *.
              fold Hover in Hexec |- *.
              assert (Hlk_lover : lookup Hover lover = Some cell5)
                by (unfold Hover, lover; apply lookup_alloc_freeze_self).
              assert (Hf_lover : is_frozen Hover lover = true)
                by (unfold Hover, lover; apply is_frozen_alloc_freeze_self).
              assert (HwfHover : well_formed_heap Hover)
                by (unfold Hover; apply freeze_well_formed;
                    apply alloc_well_formed; exact Hwf).
              assert (Hcell5_eq : cell5 =
                                  mkPCell p0_pre (B5 aa bb cca dd ee)
                                          (Some inner_loc_orig)
                                          (Some ltail_c)).
              { unfold cell5. rewrite Hpre_c, Hinner_c. reflexivity. }
              pose proof (@buf5_inject_preserves_levels A 0 p0_suf x
                            (B5 aa bb cca dd ee) Hlx Hwfsp0) as Hwflevels.
              rewrite Hsuf_c in Hpush. specialize (Hwflevels Hpush).
              cbn in Hwflevels.
              destruct Hwflevels as [Hla [Hlb [Hlcc [Hld Hle]]]].
              assert (Habs_mr : make_red_inject_chain
                                 (ChainCons (PNode p0_pre
                                                   (PNode p0_pre' p0_ii p0_suf')
                                                   (B5 aa bb cca dd ee)) c0)
                                = Some c').
              { unfold inject_chain_full in Habs.
                rewrite Hpush in Habs. exact Habs. }
              assert (HpsHHover : persists_strong H Hover).
              { unfold Hover.
                eapply persists_strong_trans.
                { eapply alloc_persists_strong. exact Hwf. }
                apply freeze_persists_strong. }
              assert (HRpkt' : packet_repr_at Hover (Some inner_loc_orig)
                                 (PNode p0_pre' p0_ii p0_suf') 1).
              { eapply packet_repr_at_persists_strong; [exact HpsHHover|].
                exact HRpkt_orig. }
              assert (HRtl' : chain_repr_at Hover ltail_c c0
                               (2 + packet_depth p0_ii)).
              { eapply chain_repr_at_persists_strong; [|exact HRtl_orig].
                exact HpsHHover. }
              match type of Hexec with
              | match ?e with _ => _ end = _ =>
                  destruct e as [[[Hf rf] kf]|] eqn:Hmr; [|discriminate]
              end.
              inversion Hexec; subst H' lroot' n; clear Hexec.
              eapply (@exec_make_red_inject_pkt_C_refines_nested A lover
                        inner_loc_orig ltail_c
                        aa bb cca dd ee p0_pre p0_pre' p0_suf' p0_ii c0 c'
                        Hover Hf rf kf).
              ** rewrite Hcell5_eq in Hlk_lover. exact Hlk_lover.
              ** exact Hf_lover.
              ** exact HRpkt'.
              ** exact HRtl'.
              ** exact HwfHover.
              ** exact Hla. ** exact Hlb. ** exact Hlcc. ** exact Hld. ** exact Hle.
              ** exact Hwfp0.
              ** unfold lover, Hover. exact Hmr.
              ** exact Habs_mr.
Qed.

(** *** Pop full refinement.  Phase S'''': handles BOTH the naive-pop
    path AND the make_green underflow path.  When the top prefix is
    non-B0 the naive path fires; when it is B0 (underflow) the
    imperative invokes [exec_make_green_pop_pkt_C] which is bridged to
    the abstract [make_green_pop_chain] via
    [exec_make_green_pop_pkt_C_refines]. *)
Theorem exec_pop_pkt_full_C_refines_pop_chain_full :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    @exec_pop_pkt_full_C A lroot H = Some (H', Some (x, lroot'), n) ->
    pop_chain_full c = Some (x, c') ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Hexec Habs.
  unfold exec_pop_pkt_full_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  pose proof (@chain_repr_cell_top_pre A H lroot c c_top HR Hlk_top) as Hcell_pre.
  destruct (buf5_pop_naive (pcell_pre c_top)) as [[xp pre']|] eqn:Hpop.
  - (* Naive pop succeeded *)
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' x lroot' n; clear Hexec.
    (* Show pop_chain c = Some (xp, c'). *)
    assert (Hpop_chain : pop_chain c = Some (xp, c')).
    { destruct c as [b | p c0].
      - cbn in Hcell_pre. rewrite Hcell_pre in Hpop.
        cbn in Habs. rewrite Hpop in Habs.
        cbn. rewrite Hpop. exact Habs.
      - destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
        destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
        cbn in Hcell_pre. rewrite Hcell_pre in Hpop.
        cbn in Habs. rewrite Hpop in Habs.
        cbn. rewrite Hpop. exact Habs. }
    (* Now reduce to Goal A. *)
    eapply exec_pop_pkt_C_refines_pop_chain; [exact HR | exact Hwf | | exact Hpop_chain].
    unfold exec_pop_pkt_C, bindC.
    unfold read_MC. rewrite Hlk_top. rewrite Hpop.
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC]. reflexivity.
  - (* Naive pop returned None ⇒ pcell_pre c_top = B0.  Underflow case:
       fire make_green_pop refinement.  c must be a simple-cons (Ending
       and nested-cons return None abstractly when pre = B0). *)
    assert (Hpcp_b0 : pcell_pre c_top = B0).
    { destruct (pcell_pre c_top) as [|y|y z|y z w|y z w u|y z w u v];
        cbn in Hpop; try discriminate; reflexivity. }
    destruct (pcell_tail c_top) as [ltail|] eqn:Htail.
    + (* fire make_green *)
      destruct c as [b | p c0].
      * (* Ending: pop_chain_full returns None when b = B0. *)
        cbn in Hcell_pre. rewrite Hpcp_b0 in Hcell_pre.
        subst b.
        cbn in Habs. discriminate.
      * destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
        destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
        cbn in Hcell_pre. rewrite Hpcp_b0 in Hcell_pre. subst pre.
        assert (Habs_mg : make_green_pop_chain
                            (ChainCons (PNode B0 Hole suf) c0) = Some (x, c')).
        { cbn in Habs. exact Habs. }
        unfold chain_repr in HR.
        apply chain_repr_at_inv_simple_cons in HR.
        destruct HR as [cell_c [ltail_c [Hlk_c [Hf_c [Hpre_c [Hsuf_c
                           [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]]].
        rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst cell_c;
          clear Hlk_top.
        rewrite Htail_c in Htail. inversion Htail; subst ltail_c;
          clear Htail.
        (* The cell c_top has pre=B0, suf=suf, inner=None, tail=Some ltail.
           Build the canonical lookup form for the make_green refinement. *)
        assert (Hcell_eq : c_top = mkPCell B0 suf None (Some ltail)).
        { destruct c_top as [pre' suf' inner' tail']; cbn in *.
          subst. reflexivity. }
        destruct (exec_make_green_pop_pkt_C lroot H) as [[[Hmg rmg] kmg]|]
          eqn:Hexec_mg; [|discriminate].
        injection Hexec as EH En Er. subst Hmg rmg.
        eapply (@exec_make_green_pop_pkt_C_refines A lroot suf ltail c0 x c'
                  H H' lroot' kmg).
        -- rewrite Hlk_c. rewrite Hcell_eq. reflexivity.
        -- exact Hf_c.
        -- exact HRtl.
        -- exact Hwf.
        -- exact Hwfs.
        -- exact Hexec_mg.
        -- exact Habs_mg.
    + (* tail = None: imperative returns None, contradicts Hexec. *)
      cbv [retC] in Hexec. discriminate Hexec.
Qed.

(** *** Eject full refinement.  Phase S'''': handles BOTH the naive-eject
    path AND the make_green underflow path.  When the relevant buffer
    is non-B0 the naive path fires; when it is B0 (underflow) the
    imperative invokes [exec_make_green_eject_pkt_C] which is bridged
    to the abstract [make_green_eject_chain] via
    [exec_make_green_eject_pkt_C_refines] (for ChainCons inner chains;
    the Ending inner-chain sub-case is discharged by computation
    showing the imperative — gated by [pcell_tail tail_cell <> None]
    in Footprint.v — returns None, making the refinement vacuous). *)
Theorem exec_eject_pkt_full_C_refines_eject_chain_full :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    @exec_eject_pkt_full_C A lroot H = Some (H', Some (lroot', x), n) ->
    eject_chain_full c = Some (c', x) ->
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Hexec Habs.
  unfold exec_eject_pkt_full_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c_top|] eqn:Hlk_top; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  pose proof (@chain_repr_cell_top_pre A H lroot c c_top HR Hlk_top) as Hcell_pre.
  pose proof (@chain_repr_cell_top_suf A H lroot c c_top HR Hlk_top) as Hcell_suf.
  destruct (pcell_tail c_top) as [ltail|] eqn:Htail.
  - (* Some tail: ChainCons case (cell has a tail pointer). *)
    destruct (buf5_eject_naive (pcell_suf c_top)) as [[suf' xp]|] eqn:Hej.
    + (* Naive eject succeeded *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' x n; clear Hexec.
      assert (Heject_chain : eject_chain c = Some (c', xp)).
      { destruct c as [b | p c0].
        - (* Ending: contradicts Htail (would force tail=None). *)
          apply chain_repr_inv_ending in HR.
          destruct HR as [cell_e [Hlk_e [_ [_ [_ [Htail_e _]]]]]].
          rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst cell_e.
          rewrite Htail_e in Htail. discriminate.
        - destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
          destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
          cbn in Hcell_suf. rewrite Hcell_suf in Hej.
          cbn in Habs. rewrite Hej in Habs. cbn. rewrite Hej. exact Habs. }
      eapply exec_eject_pkt_C_refines_eject_chain;
        [exact HR | exact Hwf | | exact Heject_chain].
      unfold exec_eject_pkt_C, bindC.
      unfold read_MC. rewrite Hlk_top. rewrite Htail. rewrite Hej.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC]. reflexivity.
    + (* Naive eject on suf returned None ⇒ suf = B0.  Underflow case:
         fire make_green_eject refinement.  c must be a simple-cons. *)
      assert (Hsuf_b0 : pcell_suf c_top = B0).
      { destruct (pcell_suf c_top) as [|y|y z|y z w|y z w u|y z w u v];
          cbn in Hej; try discriminate; reflexivity. }
      destruct c as [b | p c0].
      * (* Ending: but pcell_tail = Some contradicts Ending invariant. *)
        apply chain_repr_inv_ending in HR.
        destruct HR as [cell_e [Hlk_e [_ [_ [_ [Htail_e _]]]]]].
        rewrite Hlk_e in Hlk_top. inversion Hlk_top; subst cell_e.
        rewrite Htail_e in Htail. discriminate.
      * destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
        destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
        cbn in Hcell_suf. rewrite Hsuf_b0 in Hcell_suf. subst suf.
        (* Habs becomes: eject_chain_full (ChainCons (PNode pre Hole B0) c0)
           = Some (c', x), which (since buf5_eject_naive B0 = None) is
           make_green_eject_chain (ChainCons (PNode pre Hole B0) c0)
           = Some (c', x). *)
        assert (Habs_mg : make_green_eject_chain
                            (ChainCons (PNode pre Hole B0) c0) = Some (c', x)).
        { cbn in Habs. exact Habs. }
        unfold chain_repr in HR.
        apply chain_repr_at_inv_simple_cons in HR.
        destruct HR as [cell_c [ltail_c [Hlk_c [Hf_c [Hpre_c [Hsuf_c
                           [Hinner_c [Htail_c [Hwfp [Hwfs HRtl]]]]]]]]]].
        rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst cell_c;
          clear Hlk_top.
        rewrite Htail_c in Htail. inversion Htail; subst ltail_c;
          clear Htail.
        assert (Hcell_eq : c_top = mkPCell pre B0 None (Some ltail)).
        { destruct c_top as [pre' suf' inner' tail']; cbn in *.
          subst. reflexivity. }
        (* Now case-split on c0 (the inner chain at level 1).
           If c0 = Ending b0: with Footprint fix, imperative returns None,
           contradicting Hexec.
           If c0 = ChainCons p' c'0: apply make_green_eject refinement. *)
        destruct c0 as [b0 | p' c'0].
        -- (* c0 = Ending b0: imperative fallback gated by tail.tail.
              tail_cell decodes (Ending b0), so tail_cell.tail = None.
              Imperative returns None, contradicts Hexec. *)
           exfalso.
           apply chain_repr_at_inv_ending in HRtl.
           destruct HRtl as [tcell [Hlk_t [Hf_t [Htpre [Htsuf
                              [Htinner [Httail _]]]]]]].
           unfold exec_make_green_eject_pkt_C in Hexec.
           unfold bindC at 1 in Hexec.
           unfold read_MC in Hexec.
           rewrite Hlk_c in Hexec. cbn in Hexec.
           rewrite Hsuf_c in Hexec. cbn in Hexec.
           rewrite Htail_c in Hexec.
           unfold bindC at 1 in Hexec.
           unfold read_MC in Hexec.
           rewrite Hlk_t in Hexec. cbn in Hexec.
           rewrite Htsuf in Hexec. cbn in Hexec.
           rewrite Httail in Hexec.
           cbv [retC] in Hexec.
           discriminate Hexec.
        -- (* c0 = ChainCons p' c'0: apply the refinement lemma. *)
           destruct (exec_make_green_eject_pkt_C lroot H)
             as [[[Hmg rmg] kmg]|] eqn:Hexec_mg; [|discriminate].
           injection Hexec as EH En Er. subst Hmg rmg.
           eapply (@exec_make_green_eject_pkt_C_refines A lroot pre ltail
                     p' c'0 x c' H H' lroot' kmg).
           ++ rewrite Hlk_c. rewrite Hcell_eq. reflexivity.
           ++ exact Hf_c.
           ++ exact HRtl.
           ++ exact Hwf.
           ++ exact Hwfp.
           ++ exact Hexec_mg.
           ++ exact Habs_mg.
  - (* None tail: Ending case. *)
    destruct (buf5_eject_naive (pcell_pre c_top)) as [[pre' xp]|] eqn:Hej.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' lroot' x n; clear Hexec.
      assert (Heject_chain : eject_chain c = Some (c', xp)).
      { destruct c as [b | p c0].
        - cbn in Hcell_pre. rewrite Hcell_pre in Hej.
          cbn in Habs. rewrite Hej in Habs. cbn. rewrite Hej. exact Habs.
        - (* ChainCons: but pcell_tail = None ⇒ contradicts cons cell having tail. *)
          destruct p as [|pre i suf]; [cbn in Habs; discriminate|].
          destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
          apply chain_repr_cons_inv in HR.
          destruct HR as [cell_c [ltail_c [Hlk_c [_ [_ [_ [Htail_c [_ [_ _]]]]]]]]].
          rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst cell_c.
          rewrite Htail_c in Htail. discriminate. }
      eapply exec_eject_pkt_C_refines_eject_chain;
        [exact HR | exact Hwf | | exact Heject_chain].
      unfold exec_eject_pkt_C, bindC.
      unfold read_MC. rewrite Hlk_top. rewrite Htail. rewrite Hej.
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC]. reflexivity.
    + (* tail = None, naive eject on pre returns None ⇒ pre = B0.
         For Ending b: b = B0, abstract eject_chain_full returns None
         (truly empty), contradicts Habs. *)
      cbv [retC] in Hexec.
      destruct c as [b | p c0].
      * (* c = Ending b: pcell_pre c_top = b *)
        cbn in Hcell_pre.
        assert (Hpre_b0 : pcell_pre c_top = B0).
        { destruct (pcell_pre c_top) as [|y|y z|y z w|y z w u|y z w u v];
            cbn in Hej; try discriminate; reflexivity. }
        rewrite Hpre_b0 in Hcell_pre. subst b.
        cbn in Habs. discriminate.
      * (* c = ChainCons _ _: but tail = None contradicts cons. *)
        destruct p as [|pre0 i suf0]; [cbn in Habs; discriminate|].
        destruct i as [|ipre ii isuf]; [|cbn in Habs; discriminate].
        apply chain_repr_cons_inv in HR.
        destruct HR as [cell_c [ltail_c [Hlk_c [_ [_ [_ [Htail_c [_ [_ _]]]]]]]]].
        rewrite Hlk_c in Hlk_top. inversion Hlk_top; subst cell_c.
        rewrite Htail_c in Htail. discriminate.
Qed.

(** ** Combined: cost + sequence + heap-repr theorems for the
    [_full] ops.

    Phase S9 (P5 CLOSED end-to-end): the [chain_top_simple c]
    precondition is dropped from all four [_full] correctness
    theorems.  Cost / sequence / heap-repr all hold without
    restriction on the chain shape. *)
Theorem packet_push_full_correct_O1_repr :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    push_chain_full x c = Some c' ->
    exec_push_pkt_C lroot x H = Some (H', lroot', n) ->
    n <= NF_PUSH_PKT_FULL /\
    chain_to_list c' = E.to_list A x ++ chain_to_list c /\
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Habs Hexec.
  split; [|split].
  - eapply exec_push_pkt_C_cost; eauto.
  - eapply push_chain_full_seq; eauto.
  - eapply exec_push_pkt_C_refines_push_chain_full; eauto.
Qed.

Theorem packet_inject_full_correct_O1_repr :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    E.level A x = 0 ->
    well_formed_heap H ->
    inject_chain_full c x = Some c' ->
    is_b5 (chain_top_pre c') = false ->
    exec_inject_pkt_C lroot x H = Some (H', lroot', n) ->
    n <= NF_PUSH_PKT_FULL /\
    chain_to_list c' = chain_to_list c ++ E.to_list A x /\
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hlx Hwf Habs Hnb5p Hexec.
  split; [|split].
  - eapply exec_inject_pkt_C_cost; eauto.
  - eapply inject_chain_full_seq; eauto.
  - eapply exec_inject_pkt_C_refines_inject_chain_full; eauto.
Qed.

Theorem packet_pop_full_correct_O1_repr :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    pop_chain_full c = Some (x, c') ->
    exec_pop_pkt_full_C lroot H = Some (H', Some (x, lroot'), n) ->
    n <= NF_POP_PKT_FULL /\
    chain_to_list c = E.to_list A x ++ chain_to_list c' /\
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Habs Hexec.
  split; [|split].
  - eapply exec_pop_pkt_full_C_cost; eauto.
  - eapply pop_chain_full_seq; eauto.
  - eapply exec_pop_pkt_full_C_refines_pop_chain_full; eauto.
Qed.

Theorem packet_eject_full_correct_O1_repr :
  forall (A : Type) (lroot : Loc) (x : E.t A) (c c' : Chain A)
         (H H' : HeapP (E.t A)) (lroot' : Loc) (n : nat),
    chain_repr H lroot c ->
    well_formed_heap H ->
    eject_chain_full c = Some (c', x) ->
    exec_eject_pkt_full_C lroot H = Some (H', Some (lroot', x), n) ->
    n <= NF_POP_PKT_FULL /\
    chain_to_list c = chain_to_list c' ++ E.to_list A x /\
    chain_repr H' lroot' c'.
Proof.
  intros A lroot x c c' H H' lroot' n HR Hwf Habs Hexec.
  split; [|split].
  - eapply exec_eject_pkt_full_C_cost; eauto.
  - eapply eject_chain_full_seq; eauto.
  - eapply exec_eject_pkt_full_C_refines_eject_chain_full; eauto.
Qed.

(** ** Phase S' / S'' / S''' status block.

    What is fully closed (cumulative through Phase S'''):

    - Stage 1 (F4/P6, from Phase S): [chain_repr_at] carries the
      [chain_repr_nested_cons_at] constructor;
      [packet_repr_at_persists_strong] /
      [chain_repr_at_persists_strong] updated.
    - Goal A (P2 closure for the four no-overflow refinement
      theorems): the [chain_top_simple c] precondition that Phase S
      added is now DROPPED.  The four theorems
      [exec_{push,inject,pop,eject}_pkt_C_refines_{push,inject,pop,eject}_chain]
      now handle BOTH the simple-cons case (i = Hole) AND the nested-cons
      case (i = PNode ...) via [chain_repr_cons_inv] and
      [chain_repr_cons_inv_nested].
    - Goal B (P3 closure for the [_full] versions):
      - [exec_push_pkt_C_refines_push_chain_full]: full push refinement
        with BOTH the OkP path (buffer-level non-overflow) AND the
        OverflowP path (make_red repair) closed.
      - [exec_inject_pkt_C_refines_inject_chain_full]: dual of push,
        both paths closed.
      - [exec_pop_pkt_full_C_refines_pop_chain_full]: pop refinement
        — Phase S'''' DROPS the [is_b0 (chain_top_pre c) = false]
        precondition.  Both the naive-pop path and the make_green
        underflow path are closed.
      - [exec_eject_pkt_full_C_refines_eject_chain_full]: dual eject
        refinement — Phase S'''' DROPS the no-underflow precondition.
        Both the naive-eject path and the make_green underflow path
        are closed.
    - Combined cost+sequence+heap-repr theorems for each of the four
      [_full] ops.
    - Stage 4 (F2): the [kt_pop] / [kt_eject] side-fallback branches
      are confirmed unreachable on the public API test corpus.
    - Phase S'' polish: vacuous [is_b5] preconditions on the [_full]
      headline theorems are dropped.  [push_chain_full_result_not_b5]
      proves [push_chain_full]'s result has non-[B5] top prefix in
      every reachable case.  Similarly [inject_chain_full_result_suf_not_b5].

    - Phase S''' closure: the OverflowP path of
      [exec_{push,inject}_pkt_C_refines_{push,inject}_chain_full] is
      CLOSED via four make_red refinement lemmas:
        [exec_make_red_push_pkt_C_refines_ending]
        [exec_make_red_push_pkt_C_refines_cons]
        [exec_make_red_inject_pkt_C_refines_ending]
        [exec_make_red_inject_pkt_C_refines_cons]
      Cost bounds preserved: [NF_PUSH_PKT = 3], [NF_MAKE_RED_PKT = 6],
      [NF_PUSH_PKT_FULL = 9].  WC O(1) invariant per CLAUDE.md.

    - **Phase S'''' closure (this commit)**: the underflow path of
      [exec_{pop,eject}_pkt_full_C_refines_{pop,eject}_chain_full] is
      now CLOSED via two make_green refinement lemmas:
        [exec_make_green_pop_pkt_C_refines]
        [exec_make_green_eject_pkt_C_refines]
      Helper: [pop_chain_None_from_pre_B0] discharges the imperative's
      pop-side fallback as unreachable (Yann's insight: when fallback
      fires, the abstract pop_chain inspects the same B0 buffer and
      returns None, contradicting the abstract-success hypothesis).

      Footprint.v fix for the eject side: [exec_make_green_eject_pkt_C]
      now gates its tail-pre-pop fallback by [pcell_tail tail_cell <>
      None].  This eliminates the structural mismatch that arose when
      tail_cell was an Ending: the abstract [eject_chain (Ending b)]
      uses [b] (= tail.pre) for the LAST element, while the imperative
      fallback popped the FIRST.  With the gate, the Ending sub-case
      returns None imperatively, making the refinement vacuous (the
      [Hexec] hypothesis cannot be satisfied) and closing the
      asymmetry.

      The [exec_make_green_eject_pkt_C_refines] lemma is restricted to
      the [c' = ChainCons _ _] case of the inner chain; the Ending
      case is discharged in the [_full] proof by computation showing
      the imperative returns None.

      Cost bounds preserved: [NF_MAKE_GREEN_PKT = 6], [NF_POP_PKT_FULL
      = 9].  WC O(1) invariant per CLAUDE.md.

    - **Phase S''''' partial closure (P5 abstract spec)**: the
      abstract repair primitives [make_red_push_chain] and
      [make_red_inject_chain] mirror Viennot's three-case
      [green_of_red] structure:
        Case 1 (Ending B5): pre-existing.
        Case 2 (ChainCons (PNode B5 Hole _) _): pre-existing.
        Case 3 (ChainCons (PNode B5 (PNode pre' i' suf') _) _):
          NEW.  Pairs (d,e) at the next level, pushes pde onto the
          INNER packet's pre' (without recursing into the chain
          tail), and promotes the inner packet to a fresh chain
          link with the original chain tail as its tail.

      Sequence preservation: [make_red_push_chain_seq] /
      [make_red_inject_chain_seq] cover all three cases via
      [buf5_push_naive_seq] / [buf5_inject_naive_seq] +
      [E.to_list_pair].

    - **Phase S6 progress (this commit, P5 wiring + regularity)**:
      [push_chain_full] / [inject_chain_full] now actively dispatch
      on the depth-2 nested-top input shape, replacing the previous
      [PNode _ (PNode _ _ _) _ => None] catch-all.  When the outer
      buffer's naive push/inject overflows to B5, the nested branch
      invokes [make_red_push_chain] / [make_red_inject_chain] with
      the full nested chain as input — Case 3 fires and the chain
      reshapes per Viennot.

      Regularity invariant extended (Choice A: depth-2 only):
      [absorbable_chain] gains [abs_nested]; [regular_chain] gains
      [reg_ch_nested]; [regular_top_chain] gains [rtc_nested].  All
      existing preservation theorems extended with the nested case:
        [absorbable_pop], [absorbable_eject],
        [pop_chain_regular], [eject_chain_regular],
        [push_chain_absorbable_to_regular],
        [inject_chain_absorbable_to_regular],
        [push_chain_full_regular], [inject_chain_full_regular],
        [absorbable_chain_implies_regular],
        [absorbable_chain_implies_regular_top],
        [regular_chain_implies_regular_top].

      Sequence preservation extended for the wired cases:
        [push_chain_full_seq] / [inject_chain_full_seq] now cover
        the depth-2 nested-top branch.

      Refinement layer (Footprint side) NOT yet wired through to
      Case 3 — the imperative [exec_make_red_push_pkt_C] /
      [exec_make_red_inject_pkt_C] still implement Case 2 only
      (push/inject pde onto the chain-tail's buffer rather than the
      inner packet's buffer).  Until that imperative dispatch and
      the [exec_make_red_push_pkt_C_refines_nested] lemma land, the
      [_full] refinement theorems
      ([exec_push_pkt_C_refines_push_chain_full],
       [exec_inject_pkt_C_refines_inject_chain_full],
       [packet_push_full_correct_O1_repr],
       [packet_inject_full_correct_O1_repr]) carry an additional
      [chain_top_simple c] precondition restricting them to the
      Hole-inner top-packet sub-case.  The cost / sequence sub-
      claims of the combined theorems hold without restriction.

      Cost bounds: unchanged ([NF_MAKE_RED_PKT = 6], [NF_PUSH_PKT_FULL
      = 9] still proven).  WC O(1) invariant per CLAUDE.md preserved.

    - **Phase S7 partial progress (this commit, P5 imperative wiring)**:
      The imperative [exec_make_red_push_pkt_C] /
      [exec_make_red_inject_pkt_C] are extended to dispatch on
      [pcell_inner top_cell].  When [pcell_inner = Some inner_loc]
      (depth-2 nested top), the imperative reads the inner cell,
      pushes/injects [pde] onto the inner packet's prefix/suffix,
      and allocates a new chain link (promoted inner packet) +
      a new top with [B3] / Hole inner.  Cost bound preserved
      ([NF_MAKE_RED_PKT = 6]: 1 read top + 1 read inner + 2
      alloc-freeze new_link + 2 alloc-freeze new_top = 6).

      Cost lemmas [exec_make_red_push_pkt_C_cost] /
      [exec_make_red_inject_pkt_C_cost] extended with the new
      [pcell_inner = Some _] branch.

      The corresponding refinement lemma
      [exec_make_red_push_pkt_C_refines_nested] is NOT YET
      proved.  Investigation revealed a structural mismatch
      between the abstract [make_red_push_chain] Case 3 output
      shape and the [chain_repr_at] level encoding: Case 3
      produces a chain [ChainCons P0 (ChainCons P1 c')] where
      [c'] sits at chain-depth 2 (= [chain_repr_at] level 2),
      but the input had [c'] at chain-depth 1 (= level 1).
      Coq's [chain_repr_at] forces [c'] at level [S k] per
      [ChainCons], which makes the abstract Case 3 produce an
      output requiring [c'] at a strictly deeper level than the
      input — unrepresentable in general (only level-trivial
      [c'], e.g. [Ending B0], satisfies both).

      The [chain_top_simple c] precondition on the four [_full]
      theorems is NOT dropped in Phase S7; it remains pending
      Phase S8 / a redesign of [chain_repr_at] (or a constraining
      hypothesis on [c']).  Imperative + cost extensions land
      and remain reachable from a future S8 closure that
      addresses the level encoding.

    - **Phase S8 partial progress (this commit, P5 chain_repr_at
      level redesign + nested refinement lemmas)**: addressed the
      Phase S7 semantic wall by redesigning the [chain_repr_at]
      level encoding to match Viennot's element-pairing semantics.

      Changes:
        + Model.v: added [packet_depth] ([Hole = 0],
          [PNode _ i _ = S (packet_depth i)]).
        + Footprint.v: [chain_repr_nested_cons_at] now requires
          [chain_repr_at H ltail c' (S (S k) + packet_depth i')]
          instead of [(S k)].  For [i' = Hole] (the production
          depth-2 case under regularity): tail at level [S (S k)],
          matching make_red Case 3's output structure.  The
          simple-cons constructor is unchanged (its tail level
          [S k] equals [k + packet_depth (PNode _ Hole _)]).
        + Correctness.v: [chain_repr_cons_inv_nested] now returns
          tail at level [(2 + packet_depth i')];
          [chain_repr_at_inv_nested_cons] returns level
          [S (S k) + packet_depth i'].
        + Correctness.v: two new refinement lemmas
          [exec_make_red_push_pkt_C_refines_nested] and
          [exec_make_red_inject_pkt_C_refines_nested] (depth-2,
          i' = Hole; 4 buffer-shape sub-cases each: B1/B2/B3/B4).

      All existing [_refines_*] proofs that case-split on the
      nested-cons branch continue to type-check unchanged.

      What S8 did NOT close: the [chain_top_simple c] precondition
      remains on the four [_full] theorems.  Closing requires a
      depth-3+ refinement lemma (i' = PNode ...) — Case 3 of
      make_red has no abstract restriction on i', but in production
      the regularity invariant restricts to i' = Hole.  A Phase S9
      would either (a) prove the depth-3+ refinement lemma, or
      (b) carry a regularity precondition to dispatch the depth-3+
      case as exfalso.  S8 attempted (a) and reverted: the depth-3+
      lemma adds another factor in the case-split (4 buffer shapes
      × 2 inner-inner shapes × 2 ops = 16 sub-cases), exceeding
      this phase's scope.

      Cost bounds: unchanged.  WC O(1) invariant per CLAUDE.md
      preserved.  Build clean throughout; zero admits.

    - **Phase S9 closure (this commit) — P5 CLOSED end-to-end**:
      The [chain_top_simple c] precondition is DROPPED from all
      four [_full] theorems.

      Strategy: GENERALIZE the Phase S8 [_refines_nested] lemmas
      from "i' = Hole only" to "any i'", then dispatch in the
      [_full] theorems' OverflowP-nested branch.

      Changes:
        + The [_refines_nested] lemmas (push and inject) now take
          a [packet_repr_at H (Some inner_loc) (PNode pre' i' suf') 1]
          hypothesis instead of a literal [lookup H inner_loc =
          Some (mkPCell pre' suf' None None)], and forall over [i'].
          The chain tail hypothesis becomes
          [chain_repr_at H ltail c' (2 + packet_depth i')], matching
          the Phase S8 chain_repr_at level encoding.
        + Inside each of the 4 buffer-shape branches (B1/B2/B3/B4),
          the inner [chain_repr_cons_at] reconstruction becomes a
          [destruct i' as [|i'_pre i'_inner i'_suf]]:
          - Hole sub-case: simple-cons new_link (as in S8); the
            [pcell_inner = None] follows from the Hole branch of
            HRpkt_inner (via inversion).
          - PNode sub-case: nested-cons new_link, lifted via
            [packet_repr_at_persists_strong] to the post-alloc heap
            and connected via [chain_repr_nested_cons_at] with
            chain tail at level
            [S (S 1) + packet_depth i'_inner = 2 + packet_depth (PNode i'_pre i'_inner i'_suf)]
            (closed by [cbn; lia]).
        + Total: 4 buffer × 2 i' = 8 sub-cases per side, 16 total.
          All closed.  Cost bound preserved ([NF_MAKE_RED_PKT = 6]).
        + The four [_full] theorems
          ([exec_push_pkt_C_refines_push_chain_full],
           [exec_inject_pkt_C_refines_inject_chain_full],
           [packet_push_full_correct_O1_repr],
           [packet_inject_full_correct_O1_repr]) drop the
          [chain_top_simple c] precondition.  The OverflowP-nested
          branches (previously [cbn in Hsimple. contradiction]) now
          extract the inner packet via [chain_repr_cons_inv_nested]
          and invoke the generalized [_refines_nested] lemma.  The
          OkP-nested branches reuse the simple-cons-OkP logic
          ([push_chain] / [inject_chain] handle nested input
          identically to simple-cons input on a non-overflow buffer
          push/inject; only the [PNode pre i suf] outermost match
          matters, not the [i] sub-shape).

      Cost bounds: unchanged ([NF_PUSH_PKT_FULL = 9]).  WC O(1)
      invariant per CLAUDE.md preserved.  Build clean; zero admits.
      C tests pass.
*)
