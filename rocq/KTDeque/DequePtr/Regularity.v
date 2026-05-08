(** * Module: KTDeque.DequePtr.Regularity -- regularity invariant +
    preservation theorems for the abstract chain ops.

    ## Status

    This file defines regularity for the *older* colour-less [Chain]
    type ([Model.v]).  The *production* regularity invariant is
    [regular_kt] in [OpsKTRegular.v], defined over the colour-tagged
    [KChain] type.  The [KChain] formulation is local (a chain is
    regular iff every [KCons]'s colour is consistent with its tail's
    top colour); this older formulation is extrinsic and global.

    Why the older formulation is still maintained: some refinement
    proofs target [Chain] rather than [KChain], so the abstract
    cost-bounds story in [Footprint.v] still depends on this file's
    regularity definition.  The two are equivalent on chains that
    arise from public ops, modulo the colour tag.

    For the intuition story (why regularity is the load-bearing fact
    in WC O(1) at all), read [kb/spec/why-bounded-cascade.md] §2.

    ## What regularity means here

    The Kaplan-Tarjan worst-case O(1) bound requires a regularity
    invariant preserved by every operation.  In the packet/chain
    representation, regularity has two components:

    1. **No-overflow at top.**  The top-level buffer (in [Ending b],
       the single buffer; in [ChainCons (PNode pre _ suf) _], the
       prefix and suffix) must not be [B5] — otherwise the next push
       would immediately overflow.

    2. **Absorbable chain spine.**  Every link below the top must be
       able to absorb a [make_red] overflow without itself
       overflowing — i.e. its prefix and suffix must be of size ≤ 3
       (not [B4] and not [B5]).

    Together, these guarantee that a push or inject either produces a
    non-overflowing top, OR fires [make_red] which lands the overflow
    pair at the next chain link, where it (by item 2) leaves that link
    at size ≤ 4, which is again [buf_not_full] — preserving the
    surface invariant.

    A stronger version, [regular_chain_strict], requires the *whole*
    chain (including the top) to be absorbable.  This is needed to
    prove that a single push from a regular-strict chain yields
    another regular chain (full preservation under push/inject).

    This module:
    - Defines [regular_packet], [regular_chain], [absorbable_chain],
      [regular_chain_strict] inductively.
    - Proves preservation under [push_chain_full],
      [inject_chain_full], [pop_chain], [eject_chain].

    Cross-references:
    - [kb/spec/why-bounded-cascade.md]   -- the intuition layer.
    - [KTDeque/DequePtr/OpsKTRegular.v]  -- the production [regular_kt]
                                            for colour-tagged chains.
    - [KTDeque/DequePtr/OpsAbstract.v]   -- the abstract ops preserved
                                            here.
    - [kb/spec/section4-repair-cases.md] -- the abstract repair design.
*)

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model OpsAbstract.

(** ** Buffer-level predicates.

    [buf_not_full b]: [b] is not [B5] (a push won't immediately overflow).
    [buf_can_absorb_one b]: [b] has size ≤ 3, so a push lands at size
                              ≤ 4 (still [buf_not_full]). *)

Definition buf_not_full {X : Type} (b : Buf5 X) : Prop :=
  match b with
  | B5 _ _ _ _ _ => False
  | _            => True
  end.

Definition buf_can_absorb_one {X : Type} (b : Buf5 X) : Prop :=
  match b with
  | B4 _ _ _ _ | B5 _ _ _ _ _ => False
  | _                          => True
  end.

(** Decidability of these predicates. *)
Lemma buf_not_full_dec : forall (X : Type) (b : Buf5 X),
    {buf_not_full b} + {~ buf_not_full b}.
Proof.
  intros X b. destruct b; cbn; auto.
Qed.

Lemma buf_can_absorb_one_dec : forall (X : Type) (b : Buf5 X),
    {buf_can_absorb_one b} + {~ buf_can_absorb_one b}.
Proof.
  intros X b. destruct b; cbn; auto.
Qed.

(** [buf_can_absorb_one b] -> [buf_not_full b]. *)
Lemma buf_can_absorb_one_implies_not_full :
  forall (X : Type) (b : Buf5 X),
    buf_can_absorb_one b -> buf_not_full b.
Proof.
  intros X b H. destruct b; cbn in *; trivial; contradiction.
Qed.

(** Naive ops on [buf_not_full] buffers always succeed. *)
Lemma buf5_push_naive_not_full :
  forall (X : Type) (x : X) (b : Buf5 X),
    buf_not_full b ->
    exists b', buf5_push_naive x b = Some b'.
Proof.
  intros X x b Hnf. destruct b; cbn in *; eauto; contradiction.
Qed.

Lemma buf5_inject_naive_not_full :
  forall (X : Type) (x : X) (b : Buf5 X),
    buf_not_full b ->
    exists b', buf5_inject_naive b x = Some b'.
Proof.
  intros X x b Hnf. destruct b; cbn in *; eauto; contradiction.
Qed.

(** ** Buffer-level preservation lemmas. *)

Lemma buf5_push_naive_preserves_not_full_3 :
  forall (X : Type) (x : X) (b b' : Buf5 X),
    buf_can_absorb_one b ->
    buf5_push_naive x b = Some b' ->
    buf_not_full b'.
Proof.
  intros X x b b' Hca Hp.
  destruct b; cbn in Hca, Hp; inversion Hp; subst; cbn; trivial; contradiction.
Qed.

Lemma buf5_inject_naive_preserves_not_full_3 :
  forall (X : Type) (x : X) (b b' : Buf5 X),
    buf_can_absorb_one b ->
    buf5_inject_naive b x = Some b' ->
    buf_not_full b'.
Proof.
  intros X x b b' Hca Hp.
  destruct b; cbn in Hca, Hp; inversion Hp; subst; cbn; trivial; contradiction.
Qed.

Lemma buf5_pop_naive_preserves_not_full :
  forall (X : Type) (b b' : Buf5 X) (x : X),
    buf5_pop_naive b = Some (x, b') ->
    buf_not_full b'.
Proof.
  intros X b b' x Hp.
  destruct b; cbn in Hp; inversion Hp; subst; cbn; trivial.
Qed.

Lemma buf5_eject_naive_preserves_not_full :
  forall (X : Type) (b b' : Buf5 X) (x : X),
    buf5_eject_naive b = Some (b', x) ->
    buf_not_full b'.
Proof.
  intros X b b' x Hp.
  destruct b; cbn in Hp; inversion Hp; subst; cbn; trivial.
Qed.

Lemma buf5_pop_naive_preserves_can_absorb :
  forall (X : Type) (b b' : Buf5 X) (x : X),
    buf_can_absorb_one b ->
    buf5_pop_naive b = Some (x, b') ->
    buf_can_absorb_one b'.
Proof.
  intros X b b' x Hca Hp.
  destruct b; cbn in Hca, Hp; inversion Hp; subst; cbn; trivial; contradiction.
Qed.

Lemma buf5_eject_naive_preserves_can_absorb :
  forall (X : Type) (b b' : Buf5 X) (x : X),
    buf_can_absorb_one b ->
    buf5_eject_naive b = Some (b', x) ->
    buf_can_absorb_one b'.
Proof.
  intros X b b' x Hca Hp.
  destruct b; cbn in Hca, Hp; inversion Hp; subst; cbn; trivial; contradiction.
Qed.

(** ** Regularity for packets and chains. *)

(** [regular_packet p]: structural regularity of a [Packet].

    For now, we restrict to the "simple-packet" case [Hole | PNode _ Hole _]
    -- this matches what [chain_repr_at] in [Footprint.v] requires. *)
Inductive regular_packet {A : Type} : Packet A -> Prop :=
| reg_pkt_hole : regular_packet Hole
| reg_pkt_node : forall pre suf,
    regular_packet (PNode pre Hole suf).

(** [absorbable_chain c]: every link in [c] has [buf_can_absorb_one]
    on both prefix and suffix.  This is the "ready to absorb a
    make_red overflow" invariant for the spine below the top.

    Phase S6 (P5 closure): [absc_nested] admits depth-2 nested top
    chains — a [PNode pre1 (PNode pre2 Hole suf2) suf1] packet whose
    inner is itself a packet (with [Hole] terminator).  This is the
    shape that arises when the abstract operations have aggregated
    two yellow levels into a single packet allocation.  All four
    buffers must be [buf_can_absorb_one] for full absorbability. *)
Inductive absorbable_chain {A : Type} : Chain A -> Prop :=
| abs_ending : forall b,
    buf_can_absorb_one b ->
    absorbable_chain (Ending b)
| abs_cons : forall pre suf c',
    buf_can_absorb_one pre ->
    buf_can_absorb_one suf ->
    absorbable_chain c' ->
    absorbable_chain (ChainCons (PNode pre Hole suf) c')
| abs_nested : forall pre1 suf1 pre2 suf2 c',
    buf_can_absorb_one pre1 ->
    buf_can_absorb_one suf1 ->
    buf_can_absorb_one pre2 ->
    buf_can_absorb_one suf2 ->
    absorbable_chain c' ->
    absorbable_chain
      (ChainCons (PNode pre1 (PNode pre2 Hole suf2) suf1) c').

(** [regular_chain c]: the top buffers are [buf_not_full] (size ≤ 4),
    every packet is "simple" ([Hole] inner) or "nested-top" (depth-2),
    and the chain spine below the top is [absorbable_chain] (size ≤ 3
    throughout).

    This is the abstract analogue of the "alternating G/Y" invariant
    of KT99: when a top buffer hits B5 (red) and fires make_red, the
    pair lands at the next link's pre/suf which has size ≤ 3, taking
    it to size ≤ 4 — preserving the surface non-full invariant.

    Phase S6 (P5 closure): [reg_ch_nested] admits depth-2 nested top
    so [make_red_push_chain] / [make_red_inject_chain] Case 3 can fire
    without breaking regularity preservation.  The outer top buffers
    are [buf_not_full]; the inner buffers (pre2, suf2) must be
    [buf_can_absorb_one] (so the make_red Case 3 pair-push lands
    safely without B5 overflow); and [c'] is [absorbable_chain]. *)
Inductive regular_chain {A : Type} : Chain A -> Prop :=
| reg_ch_ending : forall b,
    buf_not_full b ->
    regular_chain (Ending b)
| reg_ch_cons : forall pre suf c',
    buf_not_full pre ->
    buf_not_full suf ->
    absorbable_chain c' ->
    regular_chain (ChainCons (PNode pre Hole suf) c')
| reg_ch_nested : forall pre1 suf1 pre2 suf2 c',
    buf_not_full pre1 ->
    buf_not_full suf1 ->
    buf_can_absorb_one pre2 ->
    buf_can_absorb_one suf2 ->
    absorbable_chain c' ->
    regular_chain
      (ChainCons (PNode pre1 (PNode pre2 Hole suf2) suf1) c').

(** [regular_chain_strict c]: a stronger invariant where the WHOLE
    chain (top included) is absorbable.  This is the "ready for any
    push or inject without overflow" invariant.  After one push, the
    result is [regular_chain] (top might be [B4]). *)
Definition regular_chain_strict {A : Type} (c : Chain A) : Prop :=
  absorbable_chain c.

#[export] Hint Constructors regular_packet absorbable_chain regular_chain : ktdeque.

(** [absorbable_chain c] is strictly stronger than [regular_chain c]. *)
Lemma absorbable_chain_implies_regular :
  forall (A : Type) (c : Chain A),
    absorbable_chain c -> regular_chain c.
Proof.
  intros A c HR. inversion HR; subst.
  - apply reg_ch_ending. eapply buf_can_absorb_one_implies_not_full; eauto.
  - apply reg_ch_cons; trivial; eapply buf_can_absorb_one_implies_not_full; eauto.
  - apply reg_ch_nested; trivial;
      eapply buf_can_absorb_one_implies_not_full; eauto.
Qed.

Lemma regular_chain_strict_implies_regular :
  forall (A : Type) (c : Chain A),
    regular_chain_strict c -> regular_chain c.
Proof. exact absorbable_chain_implies_regular. Qed.

(** ** Preservation of [absorbable_chain] under pop/eject. *)

Lemma absorbable_pop :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    absorbable_chain c ->
    pop_chain c = Some (x, c') ->
    absorbable_chain c'.
Proof.
  intros A c c' x HR Hpop.
  destruct c as [b | p c0]; cbn in Hpop.
  - destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hp; [|discriminate].
    inversion Hpop; subst x c'.
    inversion HR; subst.
    apply abs_ending.
    eapply buf5_pop_naive_preserves_can_absorb; [eassumption|eassumption].
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hp; [|discriminate].
    inversion Hpop; subst xp c'.
    inversion HR; subst.
    + (* abs_cons: simple inner *)
      match goal with
      | [ Hca : buf_can_absorb_one pre |- _ ] =>
          apply abs_cons; [eapply buf5_pop_naive_preserves_can_absorb;
                           [exact Hca | exact Hp]
                          | assumption | assumption ]
      end.
    + (* abs_nested: depth-2 inner *)
      match goal with
      | [ Hca : buf_can_absorb_one pre |- _ ] =>
          apply abs_nested;
            [eapply buf5_pop_naive_preserves_can_absorb;
             [exact Hca | exact Hp]
            | assumption | assumption | assumption | assumption ]
      end.
Qed.

Lemma absorbable_eject :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    absorbable_chain c ->
    eject_chain c = Some (c', x) ->
    absorbable_chain c'.
Proof.
  intros A c c' x HR Hej.
  destruct c as [b | p c0]; cbn in Hej.
  - destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hp; [|discriminate].
    inversion Hej; subst c' x.
    inversion HR; subst.
    apply abs_ending.
    eapply buf5_eject_naive_preserves_can_absorb; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hp; [|discriminate].
    inversion Hej; subst xp c'.
    inversion HR; subst.
    + (* abs_cons: simple inner *)
      match goal with
      | [ Hca : buf_can_absorb_one suf |- _ ] =>
          apply abs_cons;
            [ assumption
            | eapply buf5_eject_naive_preserves_can_absorb;
              [exact Hca | exact Hp]
            | assumption ]
      end.
    + (* abs_nested: depth-2 inner *)
      match goal with
      | [ Hca : buf_can_absorb_one suf |- _ ] =>
          apply abs_nested;
            [ assumption
            | eapply buf5_eject_naive_preserves_can_absorb;
              [exact Hca | exact Hp]
            | assumption | assumption | assumption ]
      end.
Qed.

(** ** Pop / eject preservation theorems. *)

Theorem pop_chain_regular :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    regular_chain c ->
    pop_chain c = Some (x, c') ->
    regular_chain c'.
Proof.
  intros A c x c' HR Hpop.
  destruct c as [b | p c0]; cbn in Hpop.
  - (* Ending *)
    destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hp; [|discriminate].
    inversion Hpop; subst x c'.
    apply reg_ch_ending.
    eapply buf5_pop_naive_preserves_not_full; eauto.
  - (* ChainCons *)
    destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hp; [|discriminate].
    inversion Hpop; subst xp c'.
    inversion HR; subst.
    + apply reg_ch_cons; trivial.
      eapply buf5_pop_naive_preserves_not_full; eauto.
    + apply reg_ch_nested; trivial.
      eapply buf5_pop_naive_preserves_not_full; eauto.
Qed.

Theorem eject_chain_regular :
  forall (A : Type) (c : Chain A) (c' : Chain A) (x : E.t A),
    regular_chain c ->
    eject_chain c = Some (c', x) ->
    regular_chain c'.
Proof.
  intros A c c' x HR Hej.
  destruct c as [b | p c0]; cbn in Hej.
  - destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hp; [|discriminate].
    inversion Hej; subst c' x.
    apply reg_ch_ending.
    eapply buf5_eject_naive_preserves_not_full; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hp; [|discriminate].
    inversion Hej; subst xp c'.
    inversion HR; subst.
    + apply reg_ch_cons; trivial.
      eapply buf5_eject_naive_preserves_not_full; eauto.
    + apply reg_ch_nested; trivial.
      eapply buf5_eject_naive_preserves_not_full; eauto.
Qed.

(** ** Push / inject preservation: from [absorbable_chain] (size ≤ 3
    everywhere) to [regular_chain] (top size ≤ 4, spine size ≤ 3). *)

Theorem push_chain_absorbable_to_regular :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    absorbable_chain c ->
    push_chain x c = Some c' ->
    regular_chain c'.
Proof.
  intros A x c c' HR Hpush.
  destruct c as [b | p c0]; cbn in Hpush.
  - destruct (buf5_push_naive x b) as [b'|] eqn:Hp; [|discriminate].
    inversion Hpush; subst c'; clear Hpush.
    inversion HR; subst.
    apply reg_ch_ending.
    destruct b; cbn in Hp, H0;
      try (inversion Hp; subst; cbn; trivial; fail);
      try contradiction.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_push_naive x pre) as [pre'|] eqn:Hp; [|discriminate].
    inversion Hpush; subst c'; clear Hpush.
    inversion HR; subst.
    + (* abs_cons: simple inner Hole *)
      match goal with
      | [ Hcap : buf_can_absorb_one pre,
          Hcas : buf_can_absorb_one suf,
          Habs : absorbable_chain c0 |- _ ] =>
          apply reg_ch_cons;
            [ destruct pre; cbn in Hp, Hcap;
              try (inversion Hp; subst; cbn; trivial; fail);
              try contradiction
            | destruct suf; cbn in Hcas; trivial; contradiction
            | exact Habs ]
      end.
    + (* abs_nested: depth-2 inner *)
      match goal with
      | [ Hcap1 : buf_can_absorb_one pre,
          Hcas1 : buf_can_absorb_one suf,
          Hcap2 : buf_can_absorb_one ?pre2,
          Hcas2 : buf_can_absorb_one ?suf2,
          Habs : absorbable_chain c0 |- _ ] =>
          apply reg_ch_nested;
            [ destruct pre; cbn in Hp, Hcap1;
              try (inversion Hp; subst; cbn; trivial; fail);
              try contradiction
            | destruct suf; cbn in Hcas1; trivial; contradiction
            | exact Hcap2
            | exact Hcas2
            | exact Habs ]
      end.
Qed.

Theorem inject_chain_absorbable_to_regular :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    absorbable_chain c ->
    inject_chain c x = Some c' ->
    regular_chain c'.
Proof.
  intros A c x c' HR Hinj.
  destruct c as [b | p c0]; cbn in Hinj.
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hp; [|discriminate].
    inversion Hinj; subst c'; clear Hinj.
    inversion HR; subst.
    apply reg_ch_ending.
    destruct b; cbn in Hp, H0;
      try (inversion Hp; subst; cbn; trivial; fail);
      try contradiction.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hp; [|discriminate].
    inversion Hinj; subst c'; clear Hinj.
    inversion HR; subst.
    + (* abs_cons *)
      match goal with
      | [ Hcap : buf_can_absorb_one pre,
          Hcas : buf_can_absorb_one suf,
          Habs : absorbable_chain c0 |- _ ] =>
          apply reg_ch_cons;
            [ destruct pre; cbn in Hcap; trivial; contradiction
            | destruct suf; cbn in Hp, Hcas;
              try (inversion Hp; subst; cbn; trivial; fail);
              try contradiction
            | exact Habs ]
      end.
    + (* abs_nested *)
      match goal with
      | [ Hcap1 : buf_can_absorb_one pre,
          Hcas1 : buf_can_absorb_one suf,
          Hcap2 : buf_can_absorb_one ?pre2,
          Hcas2 : buf_can_absorb_one ?suf2,
          Habs : absorbable_chain c0 |- _ ] =>
          apply reg_ch_nested;
            [ destruct pre; cbn in Hcap1; trivial; contradiction
            | destruct suf; cbn in Hp, Hcas1;
              try (inversion Hp; subst; cbn; trivial; fail);
              try contradiction
            | exact Hcap2
            | exact Hcas2
            | exact Habs ]
      end.
Qed.

(** ** Push / Inject (full version, including make_red) preservation.

    Headline theorems: [push_chain_full] and [inject_chain_full] take a
    [regular_chain] to a [regular_chain].

    The key argument: in the no-overflow case, the result top is at
    most [B4] (still [buf_not_full]).  In the make_red case (input top
    was [B4], push yielded [B5]), we split [B5 → B3 + pair]:
    - the new outer top is [B3] (which is [buf_not_full] AND
      [buf_can_absorb_one], so we can also call it absorbable),
    - the pair lands at the next chain link, where by [absorbable_chain]
      its prefix has size ≤ 3, becoming size ≤ 4 after push (so
      [buf_not_full] but not necessarily [buf_can_absorb_one]).

    So the result has [B3] at top, and [c0''] just below — but [c0'']
    has [buf_not_full] top, not necessarily absorbable.  Hence the
    result is in general only [regular_chain] in the surface sense,
    but the spine below the new top might NOT be [absorbable_chain].

    To honestly state the theorem: a single push from a regular chain
    yields a chain whose top is [buf_not_full] AND simple-packet
    structured, but the deeper spine may have lost its absorbability.
    For the imperative tier this is sufficient (the four cost theorems
    + four refinement theorems use [chain_repr_at], which doesn't
    require absorbability).

    Per the agentic-dev-kit philosophy, we make the strong claim
    explicit: [push_chain_full] + [inject_chain_full] preserve a
    weaker [regular_top] invariant (top is buf_not_full, structure is
    valid).  See [regular_top_chain] below. *)

(** [regular_top_chain c]: the top buffer(s) are [buf_not_full] and
    every packet is a simple-packet (Hole inner) or a depth-2 nested
    packet.  Strictly weaker than [regular_chain] in that we drop the
    absorbability requirement on the spine below the top.

    Phase S6 (P5 closure): admits a nested-top constructor mirroring
    [regular_chain]'s [reg_ch_nested]. *)
Inductive regular_top_chain {A : Type} : Chain A -> Prop :=
| rtc_ending : forall b,
    buf_not_full b ->
    regular_top_chain (Ending b)
| rtc_cons : forall pre suf c',
    buf_not_full pre ->
    buf_not_full suf ->
    regular_top_chain c' ->
    regular_top_chain (ChainCons (PNode pre Hole suf) c')
| rtc_nested : forall pre1 suf1 pre2 suf2 c',
    buf_not_full pre1 ->
    buf_not_full suf1 ->
    buf_not_full pre2 ->
    buf_not_full suf2 ->
    regular_top_chain c' ->
    regular_top_chain
      (ChainCons (PNode pre1 (PNode pre2 Hole suf2) suf1) c').

#[export] Hint Constructors regular_top_chain : ktdeque.

Lemma absorbable_chain_implies_regular_top :
  forall (A : Type) (c : Chain A),
    absorbable_chain c -> regular_top_chain c.
Proof.
  intros A c HR.
  induction HR.
  - apply rtc_ending. eapply buf_can_absorb_one_implies_not_full; eauto.
  - apply rtc_cons; trivial; eapply buf_can_absorb_one_implies_not_full; eauto.
  - apply rtc_nested; trivial;
      eapply buf_can_absorb_one_implies_not_full; eauto.
Qed.

Lemma regular_chain_implies_regular_top :
  forall (A : Type) (c : Chain A),
    regular_chain c -> regular_top_chain c.
Proof.
  intros A c HR.
  inversion HR; subst.
  - apply rtc_ending; trivial.
  - apply rtc_cons; trivial.
    eapply absorbable_chain_implies_regular_top; eauto.
  - apply rtc_nested; trivial.
    + eapply buf_can_absorb_one_implies_not_full; eauto.
    + eapply buf_can_absorb_one_implies_not_full; eauto.
    + eapply absorbable_chain_implies_regular_top; eauto.
Qed.

(** *** Push (full) preserves [regular_top_chain]. *)
Theorem push_chain_full_regular :
  forall (A : Type) (x : E.t A) (c : Chain A) (c' : Chain A),
    regular_chain c ->
    push_chain_full x c = Some c' ->
    regular_top_chain c'.
Proof.
  intros A x c c' HR Hpush.
  unfold push_chain_full in Hpush.
  destruct c as [b | p c0].
  - (* Ending b *)
    inversion HR; subst.
    destruct (buf5_push_naive x b) as [b'|] eqn:Hp; [|discriminate].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + inversion Hpush; subst c'; clear Hpush.
      apply rtc_ending. cbn; trivial.
    + inversion Hpush; subst c'; clear Hpush.
      apply rtc_ending. cbn; trivial.
    + inversion Hpush; subst c'; clear Hpush.
      apply rtc_ending. cbn; trivial.
    + inversion Hpush; subst c'; clear Hpush.
      apply rtc_ending. cbn; trivial.
    + inversion Hpush; subst c'; clear Hpush.
      apply rtc_ending. cbn; trivial.
    + (* B5: make_red on Ending *)
      cbn in Hpush.
      destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
        [|discriminate].
      inversion Hpush; subst c'; clear Hpush.
      apply rtc_cons; cbn; trivial.
      apply rtc_ending; cbn; trivial.
  - (* ChainCons *)
    destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: simple-packet path *)
      inversion HR; subst.
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hp; [|discriminate].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * (* B5: make_red fires; pushes pair onto c0 *)
        cbn in Hpush.
        destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
          [|discriminate].
        destruct (push_chain (E.pair A u v eq) c0) as [c0''|] eqn:Hpush0;
          [|discriminate].
        inversion Hpush; subst c'; clear Hpush.
        apply rtc_cons; cbn; trivial.
        apply regular_chain_implies_regular_top.
        eapply push_chain_absorbable_to_regular; eauto.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      (* HR : regular_chain (ChainCons (PNode pre (PNode ipre ii isuf) suf) c0).
         Only [reg_ch_nested] applies, with [ii = Hole]. *)
      inversion HR as [|? ? ? ? ? ?|? ? ? ? ? Hpre1 Hsuf1 Hpre2 Hsuf2 Habsc0]; subst.
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hp; [|discriminate].
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * (* B0 impossible *) destruct pre; cbn in Hp; inversion Hp.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hpush; subst c'; clear Hpush.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * (* B5: make_red Case 3 fires *)
        cbn in Hpush.
        destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
          [|discriminate].
        destruct (buf5_push_naive (E.pair A u v eq) ipre) as [pre''|] eqn:Hpush2;
          [|discriminate].
        destruct pre'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv].
        -- (* B0 impossible from buf5_push_naive *)
           destruct ipre; cbn in Hpush2; inversion Hpush2.
        -- inversion Hpush; subst c'; clear Hpush.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hpush; subst c'; clear Hpush.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hpush; subst c'; clear Hpush.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hpush; subst c'; clear Hpush.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- (* B5 impossible since ipre absorb_one *)
           exfalso.
           assert (Hnf : @buf_not_full (E.t A) (B5 py pz pw pu pv))
             by (eapply buf5_push_naive_preserves_not_full_3;
                 [ exact Hpre2 | exact Hpush2 ]).
           cbn in Hnf; exact Hnf.
Qed.

(** *** Inject (full) preserves [regular_top_chain]. *)
Theorem inject_chain_full_regular :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    regular_chain c ->
    inject_chain_full c x = Some c' ->
    regular_top_chain c'.
Proof.
  intros A c x c' HR Hinj.
  unfold inject_chain_full in Hinj.
  destruct c as [b | p c0].
  - (* Ending *)
    inversion HR; subst.
    destruct (buf5_inject_naive b x) as [b'|] eqn:Hp; [|discriminate].
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + inversion Hinj; subst c'; clear Hinj.
      apply rtc_ending. cbn; trivial.
    + inversion Hinj; subst c'; clear Hinj.
      apply rtc_ending. cbn; trivial.
    + inversion Hinj; subst c'; clear Hinj.
      apply rtc_ending. cbn; trivial.
    + inversion Hinj; subst c'; clear Hinj.
      apply rtc_ending. cbn; trivial.
    + inversion Hinj; subst c'; clear Hinj.
      apply rtc_ending. cbn; trivial.
    + (* B5: make_red on Ending *)
      cbn in Hinj.
      destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
        [|discriminate].
      inversion Hinj; subst c'; clear Hinj.
      apply rtc_cons; cbn; trivial.
      apply rtc_ending; cbn; trivial.
  - (* ChainCons *)
    destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: simple-packet path *)
      inversion HR; subst.
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hp; [|discriminate].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        eapply absorbable_chain_implies_regular_top; eauto.
      * (* B5: make_red fires *)
        cbn in Hinj.
        destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
          [|discriminate].
        destruct (inject_chain c0 (E.pair A y z eq)) as [c0''|] eqn:Hinj0;
          [|discriminate].
        inversion Hinj; subst c'; clear Hinj.
        apply rtc_cons; cbn; trivial.
        apply regular_chain_implies_regular_top.
        eapply inject_chain_absorbable_to_regular; eauto.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      inversion HR as [|? ? ? ? ? ?|? ? ? ? ? Hpre1 Hsuf1 Hpre2 Hsuf2 Habsc0]; subst.
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hp; [|discriminate].
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * (* B0 impossible *) destruct suf; cbn in Hp; inversion Hp.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * inversion Hinj; subst c'; clear Hinj.
        apply rtc_nested; cbn; trivial;
          try (eapply buf_can_absorb_one_implies_not_full; eassumption);
          eapply absorbable_chain_implies_regular_top; eassumption.
      * (* B5: make_red Case 3 dual fires *)
        cbn in Hinj.
        destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
          [|discriminate].
        destruct (buf5_inject_naive isuf (E.pair A y z eq)) as [suf''|] eqn:Hinj2;
          [|discriminate].
        destruct suf'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv].
        -- destruct isuf; cbn in Hinj2; inversion Hinj2.
        -- inversion Hinj; subst c'; clear Hinj.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hinj; subst c'; clear Hinj.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hinj; subst c'; clear Hinj.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- inversion Hinj; subst c'; clear Hinj.
           apply rtc_cons; cbn; trivial.
           apply rtc_cons; cbn; trivial.
           ++ eapply buf_can_absorb_one_implies_not_full; eassumption.
           ++ eapply absorbable_chain_implies_regular_top; eassumption.
        -- (* B5 impossible since isuf absorb_one *)
           exfalso.
           assert (Hnf : @buf_not_full (E.t A) (B5 py pz pw pu pv))
             by (eapply buf5_inject_naive_preserves_not_full_3;
                 [ exact Hsuf2 | exact Hinj2 ]).
           cbn in Hnf; exact Hnf.
Qed.

(** ** Sanity examples. *)

Example empty_regular :
  regular_chain (A := nat) (empty_chain nat).
Proof. unfold empty_chain. apply reg_ch_ending. cbn; trivial. Qed.

Example singleton_regular :
  regular_chain (A := nat) (Ending (B1 (E.base nat 7))).
Proof. apply reg_ch_ending. cbn; trivial. Qed.

(** Pushing onto a single-element [Ending] yields a [regular_top_chain]
    (the result is [Ending (B2 _ _)], a green buffer, [buf_not_full]). *)
Example push_into_singleton_regular :
  forall (c' : Chain nat),
    push_chain_full (E.base nat 1) (Ending (B1 (E.base nat 2))) = Some c' ->
    regular_top_chain (A := nat) c'.
Proof.
  intros c' Heq.
  apply push_chain_full_regular with (c := Ending (B1 (E.base nat 2))) (x := E.base nat 1);
    [|exact Heq].
  apply reg_ch_ending. cbn; trivial.
Qed.

(** ** Pop / eject (full version, with make_green refill) preservation.

    Symmetric to [push_chain_full_regular] / [inject_chain_full_regular].
    These take a [regular_chain] to a [regular_top_chain].

    In the no-refill case, the result top is one smaller than the input
    top — still [buf_not_full].  In the make_green-refill case, the new
    top is built as [B1 _] (a single element popped from the unpaired
    pair), which is [buf_not_full].  The deeper spine may have lost its
    absorbability, but the outer top is preserved. *)

Theorem pop_chain_full_regular :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    regular_chain c ->
    pop_chain_full c = Some (x, c') ->
    regular_top_chain c'.
Proof.
  intros A c x c' HR Hpop.
  unfold pop_chain_full in Hpop.
  destruct c as [b | p c0].
  - (* Ending *)
    inversion HR; subst.
    destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hp; [|discriminate].
    inversion Hpop; subst x c'; clear Hpop.
    apply rtc_ending.
    eapply buf5_pop_naive_preserves_not_full; eauto.
  - (* ChainCons *)
    destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf]; [|discriminate].
    inversion HR as [|? ? ? Hnf_pre Hnf_suf Habsc'|? ? ? ? ? ? ? ? ?]; subst.
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hp.
    + (* Naive pop succeeded *)
      inversion Hpop; subst xp c'; clear Hpop.
      apply rtc_cons; trivial.
      * eapply buf5_pop_naive_preserves_not_full; eauto.
      * eapply absorbable_chain_implies_regular_top; eauto.
    + (* Underflow: fire make_green *)
      unfold make_green_pop_chain in Hpop.
      destruct (pop_chain c0) as [[paired c0'']|] eqn:Hpop_c0; [|discriminate].
      destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
      inversion Hpop; subst x c'; clear Hpop.
      apply rtc_cons; cbn; trivial.
      (* Need: regular_top_chain c0''.  We have absorbable_chain c0
         and pop_chain c0 = Some (paired, c0'').  By absorbable_pop,
         c0'' is absorbable, hence regular_top. *)
      eapply absorbable_chain_implies_regular_top.
      eapply absorbable_pop; eauto.
Qed.

Theorem eject_chain_full_regular :
  forall (A : Type) (c : Chain A) (c' : Chain A) (x : E.t A),
    regular_chain c ->
    eject_chain_full c = Some (c', x) ->
    regular_top_chain c'.
Proof.
  intros A c c' x HR Hej.
  unfold eject_chain_full in Hej.
  destruct c as [b | p c0].
  - inversion HR; subst.
    destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hp; [|discriminate].
    inversion Hej; subst c' x; clear Hej.
    apply rtc_ending.
    eapply buf5_eject_naive_preserves_not_full; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf]; [|discriminate].
    inversion HR as [|? ? ? Hnf_pre Hnf_suf Habsc'|? ? ? ? ? ? ? ? ?]; subst.
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hp.
    + inversion Hej; subst c' xp; clear Hej.
      apply rtc_cons; trivial.
      * eapply buf5_eject_naive_preserves_not_full; eauto.
      * eapply absorbable_chain_implies_regular_top; eauto.
    + unfold make_green_eject_chain in Hej.
      destruct (eject_chain c0) as [[c0'' paired]|] eqn:Hej_c0; [|discriminate].
      destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
      inversion Hej; subst c' x; clear Hej.
      apply rtc_cons; cbn; trivial.
      eapply absorbable_chain_implies_regular_top.
      eapply absorbable_eject; eauto.
Qed.
