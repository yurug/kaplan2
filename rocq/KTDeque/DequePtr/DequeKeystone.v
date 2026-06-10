(** * KTDeque.DequePtr.DequeKeystone — Gate-B deque keystone (Phase 4a).

    The unconditional worst-case-O(1) statement for the non-catenable deque,
    built TOP-DOWN per kb/spec/deque-reachable-invariant.md and the rebuild
    plan's methodology rule 6.

    The invariant is
      [I_kt c := regular_kt_top c /\ colors_consistent c /\ well_leveled c].

    The per-operation obligation lemmas ([*_total], [*_preserves_I_kt]) are
    [Admitted] SCAFFOLDING on the [rebuild] branch.  The headline theorems
    [deque_wc_o1_*] are proven FROM those obligations + the already-closed cost
    lemmas ([*_green_calls_le_1]), which validates the architecture end to end.

    The remaining admits ARE the to-do list — see [Print Assumptions] at the
    bottom.  CLOSURE of Phase 4a = zero admits + clean Print Assumptions
    (rebuild plan rules 5b/5c).  Admits never reach [main].

    Discharge order (hardest last):
      [ ] empty_I_kt                  -- proven below (not admitted)
      [ ] push_kt4_total / preserves_I_kt
      [ ] inject_kt4_total / preserves_I_kt
      [ ] pop_kt4_total / preserves_I_kt
      [ ] eject_kt4_total / preserves_I_kt
    Each [*_total]/[*_preserves_I_kt] decomposes via the crux lemma
    (green_of_red_k total + I_kt-preserving on regular, colour-consistent,
    well-levelled red chains) into the buffer-op lemmas. *)

From KTDeque.Common Require Import Prelude Color Buf5 Buf5Ops Element.
From KTDeque.DequePtr Require Import Model OpsKT OpsKTRegular OpsAbstract
  PublicTheorems.

Module E := OpsKT.E.

(* ========================================================================== *)
(* The invariant I_kt.                                                         *)
(* ========================================================================== *)

(** Colour-consistency inside a packet's yellow run: every nested level is
    not-red (the yellow run sits above the green/red boundary). *)
Fixpoint cc_yellow_run {A : Type} (p : Packet A) : Prop :=
  match p with
  | Hole => True
  | PNode pre i suf =>
      buf5_is_not_red_shape pre /\ buf5_is_not_red_shape suf /\ cc_yellow_run i
  end.

(** Colour-tag consistency at every chain link: a Green link has green-shaped
    (B2/B3) buffers, a Yellow link has not-red (B1..B4) buffers; the inner
    yellow run is not-red throughout.  (The Red-link buffer condition is left
    permissive here and will be tightened while discharging the obligations.) *)
(** A link's buffers match its colour tag: Green => green-shaped (B2/B3);
    Yellow => not-red (B1..B4); Red is permissive (transient, top excluded by
    [regular_kt_top]). *)
Definition cc_color_shape {X : Type} (col : color) (pre suf : Buf5 X) : Prop :=
  match col with
  | Green  => buf5_is_green_shape pre /\ buf5_is_green_shape suf
  | Yellow => buf5_is_not_red_shape pre /\ buf5_is_not_red_shape suf
  | Red    => True
  end.

(** Green-readiness of the level directly below a single (Hole-inner) link:
    that tail must be an [Ending], or a [KCons] whose packet has green-shaped
    outer buffers.  This is exactly what [green_of_red_k]'s Case-2 repair
    needs ([green_of_red_k_ready_at]).  It is NOT a clause of the invariant —
    it is DERIVED ([tail_green_ready_of_cc]) for Yellow/Red links from the
    tail-colour discipline below.  (Making it a clause of every Hole-inner
    link is too strong: the repair's Case 3 legitimately outputs a Green link
    over a fresh Red inner whose buffers are not green-shaped — the precise
    wall the prior [*_ready_state] accretion hit.) *)
Definition tail_green_ready {A : Type} (tail : KChain A) : Prop :=
  match tail with
  | KEnding _ => True
  | KCons _ (PNode pre2 _ suf2) _ =>
      buf5_is_green_shape pre2 /\ buf5_is_green_shape suf2
  | KCons _ Hole _ => False
  end.

(** Tail-colour discipline (KT99 §4 made local):
    - Yellow links occur only at the top: every link's tail is non-Yellow.
    - A Yellow or Red link sits over a Green link (or the Ending) — the
      "first non-yellow below is green" rule.  This is what makes the link
      repairable when it degrades.
    - A Green link may sit over Green or RED (the repair's Case 3 creates
      Green-over-fresh-Red; the wrap path repairs that Red before the Green
      ever degrades). *)
Definition cc_tail_color {A : Type} (col : color) (tail : KChain A) : Prop :=
  match tail with
  | KEnding _ => True
  | KCons tc _ _ =>
      match col with
      | Green => tc <> Yellow
      | _ => tc = Green
      end
  end.

Fixpoint colors_consistent {A : Type} (c : KChain A) : Prop :=
  match c with
  | KEnding _ => True
  | KCons col (PNode pre i suf) tail =>
      cc_color_shape col pre suf /\
      cc_yellow_run i /\
      cc_tail_color col tail /\
      colors_consistent tail
  | KCons _ Hole _ => False
  end.

(** The derived green-readiness: a non-Green link's tail is Green-topped (or
    Ending), and the tail's own Green clause supplies the green shapes. *)
Lemma tail_green_ready_of_cc :
  forall A col (tail : KChain A),
    col <> Green ->
    cc_tail_color col tail ->
    colors_consistent tail ->
    tail_green_ready tail.
Proof.
  intros A col tail Hcol Htc Hcc.
  destruct tail as [b | tc [|pre2 i2 suf2] tail2]; cbn; [exact I | |].
  - cbn in Hcc. contradiction.
  - destruct col; [congruence | |];
      cbn in Htc; subst tc;
      cbn in Hcc; destruct Hcc as [[Hg1 Hg2] _]; exact (conj Hg1 Hg2).
Qed.

(** [packet_depth p]: number of [PNode] layers — how many levels the yellow
    run bundles.  The chain link below a packet sits [packet_depth p] levels
    deeper, NOT one level deeper: Model.v's [chain_levels] hard-codes [S k]
    per link, which is wrong for nested (depth ≥ 2) packets (e.g. the
    Overflow/Overflow case of [make_small] puts the ending two levels down). *)
Fixpoint packet_depth {A : Type} (p : Packet A) : nat :=
  match p with
  | Hole => 0
  | PNode _ i _ => S (packet_depth i)
  end.

(** Depth-aware levels invariant for [Chain] (used for [make_small] outputs). *)
Fixpoint chain_levels_d {A : Type} (k : nat) (c : Chain A) : Prop :=
  match c with
  | Ending b => buf_all_at_level k b
  | ChainCons p c' => packet_levels k p /\ chain_levels_d (packet_depth p + k) c'
  end.

(** Level-consistency: buffers at chain-depth [k] hold level-[k] elements.
    Lifts Model.v's [buf_all_at_level]/[packet_levels] to [KChain], with the
    depth-aware tail index.  Over the production instance [E = ElementTree],
    positive-level elements are unpairable (a theorem, not an axiom), which is
    what the repair's underflow arms need. *)
Fixpoint well_leveled_at {A : Type} (k : nat) (c : KChain A) : Prop :=
  match c with
  | KEnding b => buf_all_at_level k b
  | KCons _ p tail => packet_levels k p /\ well_leveled_at (packet_depth p + k) tail
  end.

Definition well_leveled {A : Type} (c : KChain A) : Prop := well_leveled_at 0 c.

Definition I_kt {A : Type} (c : KChain A) : Prop :=
  regular_kt_top c /\ colors_consistent c /\ well_leveled c.

(** The empty deque satisfies the invariant. *)
Lemma empty_I_kt : forall A, I_kt (@empty_kchain A).
Proof.
  intros A. unfold I_kt, regular_kt_top, well_leveled, empty_kchain.
  split.
  - split.
    + cbn. discriminate.
    + apply reg_kt_ending.
  - split.
    + cbn. exact I.
    + cbn. exact I.
Qed.

(* ========================================================================== *)
(* Reusable machinery: connect I_kt to the existing green_of_red_k readiness.  *)
(* ========================================================================== *)

(** [colors_consistent] + [well_leveled_at] at a link give the prior work's
    [green_of_red_k_context_ready_at] for that link's (inner, tail). *)
Lemma context_ready_of_consistent :
  forall A k col (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
         (tail : KChain A),
    col <> Green ->
    colors_consistent (KCons col (PNode pre i suf) tail) ->
    well_leveled_at k (KCons col (PNode pre i suf) tail) ->
    green_of_red_k_context_ready_at k i tail.
Proof.
  intros A k col pre i suf tail Hcol Hcc Hwl.
  cbn in Hcc. destruct Hcc as [_Hshape [Hyr [Htc Htail]]].
  pose proof (@tail_green_ready_of_cc A col tail Hcol Htc Htail) as Hgr.
  cbn in Hwl. destruct Hwl as [Hpkt Hwltail].
  destruct i as [|ipre ichild isuf].
  - (* i = Hole *)
    unfold green_of_red_k_context_ready_at.
    destruct tail as [b | col2 [|tpre tchild tsuf] tail2].
    + (* KEnding b *) cbn in Hwltail |- *. exact Hwltail.
    + (* KCons col2 Hole tail2 *) cbn in Hgr. contradiction.
    + (* KCons col2 (PNode tpre tchild tsuf) tail2 *)
      cbn in Hgr, Hwltail |- *.
      destruct Hgr as [Hp2 Hs2]. destruct Hwltail as [Hpkt2 _].
      repeat split; assumption.
  - (* i = PNode *)
    unfold green_of_red_k_context_ready_at.
    cbn in Hyr. destruct Hyr as [Hp2 [Hs2 _]].
    inversion Hpkt as [|? ? ? ? _ Hinner _]; subst.
    repeat split; assumption.
Qed.

(** Lift context-readiness to [green_of_red_k_ready_at] for any prefix buffer. *)
Lemma ready_at_of_consistent :
  forall A k col (pre pre' : Buf5 (E.t A)) (i : Packet A)
         (suf suf' : Buf5 (E.t A)) (tail : KChain A),
    col <> Green ->
    colors_consistent (KCons col (PNode pre i suf) tail) ->
    well_leveled_at k (KCons col (PNode pre i suf) tail) ->
    green_of_red_k_ready_at k (PNode pre' i suf') tail.
Proof.
  intros A k col pre pre' i suf suf' tail Hcol Hcc Hwl.
  apply green_of_red_k_ready_at_from_context.
  eapply context_ready_of_consistent; eassumption.
Qed.

(** A consistent, well-levelled, Red-topped chain is repairable. *)
Lemma green_of_red_k_some_of_consistent :
  forall A k (c : KChain A),
    colors_consistent c ->
    well_leveled_at k c ->
    kchain_top_color c = Red ->
    exists c', green_of_red_k c = Some c'.
Proof.
  intros A k c Hcc Hwl Htop.
  destruct c as [b | col [|pre i suf] tail].
  - cbn in Htop. discriminate.
  - cbn in Hcc. contradiction.
  - cbn in Htop. subst col.
    pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [Hpkt _].
    eapply green_of_red_k_total_under_ready_levels.
    + exact Hpkt.
    + eapply ready_at_of_consistent; [| eassumption | eassumption].
      discriminate.
Qed.

(** The Green-link push precondition: a consistent well-levelled tail is
    [yellow_wrap_pr]-ready (repairable if Red-topped). *)
Lemma yellow_wrap_pr_total_pre_of_consistent :
  forall A k (tail : KChain A),
    colors_consistent tail ->
    well_leveled_at k tail ->
    yellow_wrap_pr_total_pre tail.
Proof.
  intros A k tail Hcc Hwl.
  destruct tail as [b | col p tail']; cbn -[green_of_red_k]; [exact I|].
  destruct col; cbn -[green_of_red_k]; [exact I | exact I |].
  eapply green_of_red_k_some_of_consistent; [exact Hcc | exact Hwl | reflexivity].
Qed.

(* ========================================================================== *)
(* make_small helper level lemmas (toward make_small_preserves_levels, which   *)
(* is needed for green_of_red_k Case 1 in well_leveled preservation).          *)
(* ========================================================================== *)

Lemma prefix23_levels :
  forall A k (opt : option (E.t A)) (b c : E.t A),
    match opt with None => True | Some a => E.level A a = k end ->
    E.level A b = k -> E.level A c = k ->
    buf_all_at_level k (prefix23 opt (b, c)).
Proof. intros A k opt b c Hopt Hb Hc. destruct opt; cbn; auto. Qed.

Lemma suffix23_levels :
  forall A k (opt : option (E.t A)) (b c : E.t A),
    E.level A b = k -> E.level A c = k ->
    match opt with None => True | Some a => E.level A a = k end ->
    buf_all_at_level k (suffix23 (b, c) opt).
Proof. intros A k opt b c Hb Hc Hopt. destruct opt; cbn; auto. Qed.

Lemma suffix12_levels :
  forall A k (x : E.t A) (opt : option (E.t A)),
    E.level A x = k ->
    match opt with None => True | Some a => E.level A a = k end ->
    buf_all_at_level k (suffix12 x opt).
Proof. intros A k x opt Hx Hopt. destruct opt; cbn; auto. Qed.

Lemma mk_ending_from_options_levels :
  forall A k (p1 : option (E.t A)) (mid : option (E.t A * E.t A))
         (s1 : option (E.t A)),
    match p1 with None => True | Some a => E.level A a = k end ->
    match mid with None => True | Some (a, b) => E.level A a = k /\ E.level A b = k end ->
    match s1 with None => True | Some a => E.level A a = k end ->
    chain_levels_d k (mk_ending_from_options p1 mid s1).
Proof.
  intros A k p1 mid s1 Hp1 Hmid Hs1.
  destruct p1 as [a1|]; destruct mid as [[a2 b2]|]; destruct s1 as [a3|];
    cbn in Hp1, Hmid, Hs1 |- *;
    try (destruct Hmid);
    repeat split; auto.
Qed.

Lemma buffer_push_chain_levels :
  forall A k (x : E.t A) (b : Buf5 (E.t A)),
    E.level A x = k -> buf_all_at_level k b ->
    chain_levels_d k (buffer_push_chain x b).
Proof.
  intros A k x b Hx Hb.
  destruct b; cbn in Hb |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto;
    constructor; cbn; repeat split; auto using pl_hole.
Qed.

Lemma buffer_inject_chain_levels :
  forall A k (x : E.t A) (b : Buf5 (E.t A)),
    E.level A x = k -> buf_all_at_level k b ->
    chain_levels_d k (buffer_inject_chain b x).
Proof.
  intros A k x b Hx Hb.
  destruct b; cbn in Hb |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; auto;
    constructor; cbn; repeat split; auto using pl_hole.
Qed.

Lemma buffer_unsandwich_levels :
  forall A k (b : Buf5 (E.t A)),
    buf_all_at_level k b ->
    match buffer_unsandwich b with
    | BS_alone None => True
    | BS_alone (Some x) => E.level A x = k
    | BS_sandwich a rest c =>
        E.level A a = k /\ buf_all_at_level k rest /\ E.level A c = k
    end.
Proof.
  intros A k b Hb. destruct b; cbn in Hb |- *; intuition.
Qed.

(** A positive-level element unpairs into two elements one level down. *)
Lemma element_unpair_at_s_levels :
  forall A k (e : E.t A),
    E.level A e = S k ->
    exists x y, E.unpair A e = Some (x, y) /\ E.level A x = k /\ E.level A y = k.
Proof.
  intros A k e He.
  destruct (@element_unpair_succeeds_at_s A k e He) as [x [y Hup]].
  pose proof (@E.unpair_level A e x y Hup) as [Hlvl Hxy].
  rewrite He in Hlvl. injection Hlvl as Hlvl.
  exists x, y. split; [exact Hup|].
  split; [symmetry; exact Hlvl | rewrite <- Hxy; symmetry; exact Hlvl].
Qed.

Lemma suffix_rot_preserves_levels :
  forall A k (b b' : Buf5 (E.t A)) (x a : E.t A),
    buf_all_at_level k b -> E.level A x = k ->
    suffix_rot b x = (a, b') ->
    E.level A a = k /\ buf_all_at_level k b'.
Proof.
  intros A k b b' x a Hb Hx Heq.
  destruct b; cbn in Hb, Heq |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    inversion Heq; subst; cbn; repeat split; auto.
Qed.

Lemma prefix_rot_preserves_levels :
  forall A k (x : E.t A) (b b' : Buf5 (E.t A)) (last : E.t A),
    E.level A x = k -> buf_all_at_level k b ->
    prefix_rot x b = (b', last) ->
    buf_all_at_level k b' /\ E.level A last = k.
Proof.
  intros A k x b b' last Hx Hb Heq.
  destruct b; cbn in Hb, Heq |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    inversion Heq; subst; cbn; repeat split; auto.
Qed.

Lemma prefix_decompose_levels :
  forall A k (b : Buf5 (E.t A)),
    buf_all_at_level k b ->
    match prefix_decompose b with
    | BD_pre_underflow None => True
    | BD_pre_underflow (Some x) => E.level A x = k
    | BD_pre_ok b' => buf_all_at_level k b'
    | BD_pre_overflow b' c d =>
        buf_all_at_level k b' /\ E.level A c = k /\ E.level A d = k
    end.
Proof.
  intros A k b Hb. destruct b; cbn in Hb |- *; intuition.
Qed.

Lemma suffix_decompose_levels :
  forall A k (b : Buf5 (E.t A)),
    buf_all_at_level k b ->
    match suffix_decompose b with
    | BD_suf_underflow None => True
    | BD_suf_underflow (Some x) => E.level A x = k
    | BD_suf_ok b' => buf_all_at_level k b'
    | BD_suf_overflow b' a c =>
        buf_all_at_level k b' /\ E.level A a = k /\ E.level A c = k
    end.
Proof.
  intros A k b Hb. destruct b; cbn in Hb |- *; intuition.
Qed.

(** make_small produces a depth-aware well-levelled chain
    (green_of_red_k Case 1).  Structured: destruct the two decompose results
    (9 cases) and handle b2's single operation per case via its helper lemma,
    WITHOUT destructing b2. *)
(** Reduce the goal while keeping the make_small building blocks folded, so
    each scrutinee stays syntactically visible for [destruct]. *)
Local Ltac ms_reduce :=
  cbn -[E.level E.pair E.unpair prefix23 suffix23 suffix12
        mk_ending_from_options buffer_unsandwich buf5_pop_naive
        buf5_eject_naive buf5_push_naive buf5_inject_naive suffix_rot
        prefix_rot buffer_halve pair_each_buf buffer_push_chain
        buffer_inject_chain Nat.eq_dec].

Lemma make_small_preserves_levels :
  forall A k (b1 b2 b3 : Buf5 (E.t A)) (c : Chain A),
    buf_all_at_level k b1 ->
    buf_all_at_level (S k) b2 ->
    buf_all_at_level k b3 ->
    make_small b1 b2 b3 = Some c ->
    chain_levels_d k c.
Proof.
  intros A k b1 b2 b3 c Hb1 Hb2 Hb3.
  unfold make_small.
  pose proof (@prefix_decompose_levels A k b1 Hb1) as Hpd.
  pose proof (@suffix_decompose_levels A k b3 Hb3) as Hsd.
  revert Hpd Hsd.
  destruct (prefix_decompose b1) as [p1opt|p1'|p1' c0 d0];
    destruct (suffix_decompose b3) as [s1opt|s1'|s1' a0 e0];
    intros Hpd Hsd; cbn in Hpd, Hsd; ms_reduce.
  - (* underflow / underflow *)
    destruct (buffer_unsandwich b2) as [midopt|ab rest cd] eqn:Hus; ms_reduce;
      pose proof (@buffer_unsandwich_levels A (S k) b2 Hb2) as Hbu;
      rewrite Hus in Hbu; cbn -[E.level] in Hbu.
    + destruct midopt as [elem|].
      * destruct (E.unpair A elem) as [[x y]|] eqn:Hu; ms_reduce;
          [| intros Hbad; discriminate].
        pose proof (@E.unpair_level A elem x y Hu) as [Hlv Hxy].
        rewrite Hbu in Hlv; injection Hlv as Hlv.
        intros Hmake; injection Hmake as Hc; subst c.
        apply mk_ending_from_options_levels;
          [exact Hpd | split; congruence | exact Hsd].
      * intros Hmake; injection Hmake as Hc; subst c.
        apply mk_ending_from_options_levels;
          [exact Hpd | exact I | exact Hsd].
    + destruct Hbu as [Hab [Hrest Hcd]].
      destruct (E.unpair A ab) as [[xa ya]|] eqn:Hua; ms_reduce;
        [| intros Hbad; discriminate].
      destruct (E.unpair A cd) as [[xc yc]|] eqn:Huc; ms_reduce;
        [| intros Hbad; discriminate].
      pose proof (@E.unpair_level A ab xa ya Hua) as [Hla Hxya].
      pose proof (@E.unpair_level A cd xc yc Huc) as [Hlc Hxyc].
      rewrite Hab in Hla; injection Hla as Hla.
      rewrite Hcd in Hlc; injection Hlc as Hlc.
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce. split.
      * constructor;
          [ apply prefix23_levels; [exact Hpd|congruence|congruence]
          | apply pl_hole
          | apply suffix23_levels; [congruence|congruence|exact Hsd] ].
      * exact Hrest.
  - (* underflow / ok *)
    destruct (buf5_pop_naive b2) as [[cd rest]|] eqn:Hpop; ms_reduce.
    + pose proof (@buf5_pop_preserves_levels A (S k) b2 cd rest Hb2 Hpop)
        as [Hcd Hrest].
      destruct (E.unpair A cd) as [[x y]|] eqn:Hu; ms_reduce;
        [| intros Hbad; discriminate].
      pose proof (@E.unpair_level A cd x y Hu) as [Hlv Hxy].
      rewrite Hcd in Hlv; injection Hlv as Hlv.
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce. split.
      * constructor;
          [ apply prefix23_levels; [exact Hpd|congruence|congruence]
          | apply pl_hole
          | exact Hsd ].
      * exact Hrest.
    + destruct p1opt as [x|].
      * destruct (buf5_push_naive x s1') as [s1''|] eqn:Hpush; ms_reduce;
          [| intros Hbad; discriminate].
        intros Hmake; injection Hmake as Hc; subst c.
        ms_reduce. eapply buf5_push_preserves_levels; eauto.
      * intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact Hsd.
  - (* underflow / overflow *)
    destruct Hsd as [Hs1' [Ha0 He0]].
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [e|ne];
      ms_reduce; [|congruence].
    assert (Hpl : E.level A (E.pair A a0 e0 e) = S k)
      by (rewrite E.level_pair; congruence).
    destruct (suffix_rot b2 (E.pair A a0 e0 e)) as [cd_paired center] eqn:Hrot;
      ms_reduce.
    pose proof (@suffix_rot_preserves_levels A (S k) b2 center
                  (E.pair A a0 e0 e) cd_paired Hb2 Hpl Hrot) as [Hcdp Hcen].
    destruct (E.unpair A cd_paired) as [[x y]|] eqn:Hu; ms_reduce;
      [| intros Hbad; discriminate].
    pose proof (@E.unpair_level A cd_paired x y Hu) as [Hlv Hxy].
    rewrite Hcdp in Hlv; injection Hlv as Hlv.
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor;
        [ apply prefix23_levels; [exact Hpd|congruence|congruence]
        | apply pl_hole
        | exact Hs1' ].
    + exact Hcen.
  - (* ok / underflow *)
    destruct (buf5_eject_naive b2) as [[rest ab]|] eqn:Hej; ms_reduce.
    + pose proof (@buf5_eject_preserves_levels A (S k) b2 ab rest Hb2 Hej)
        as [Hab Hrest].
      destruct (E.unpair A ab) as [[x y]|] eqn:Hu; ms_reduce;
        [| intros Hbad; discriminate].
      pose proof (@E.unpair_level A ab x y Hu) as [Hlv Hxy].
      rewrite Hab in Hlv; injection Hlv as Hlv.
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce. split.
      * constructor;
          [ exact Hpd
          | apply pl_hole
          | apply suffix23_levels; [congruence|congruence|exact Hsd] ].
      * exact Hrest.
    + destruct s1opt as [x|].
      * destruct (buf5_inject_naive p1' x) as [p1''|] eqn:Hinj; ms_reduce;
          [| intros Hbad; discriminate].
        intros Hmake; injection Hmake as Hc; subst c.
        ms_reduce. eapply buf5_inject_preserves_levels; eauto.
      * intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact Hpd.
  - (* ok / ok *)
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor; [exact Hpd | apply pl_hole | exact Hsd].
    + exact Hb2.
  - (* ok / overflow *)
    destruct Hsd as [Hs1' [Ha0 He0]].
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [e|ne];
      ms_reduce; [|congruence].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor; [exact Hpd | apply pl_hole | exact Hs1'].
    + apply buffer_inject_chain_levels;
        [rewrite E.level_pair; congruence | exact Hb2].
  - (* overflow / underflow *)
    destruct Hpd as [Hp1' [Hc0 Hd0]].
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [e|ne];
      ms_reduce; [|congruence].
    assert (Hpl : E.level A (E.pair A c0 d0 e) = S k)
      by (rewrite E.level_pair; congruence).
    destruct (prefix_rot (E.pair A c0 d0 e) b2) as [center ab_paired] eqn:Hrot;
      ms_reduce.
    pose proof (@prefix_rot_preserves_levels A (S k) (E.pair A c0 d0 e) b2
                  center ab_paired Hpl Hb2 Hrot) as [Hcen Hab].
    destruct (E.unpair A ab_paired) as [[x y]|] eqn:Hu; ms_reduce;
      [| intros Hbad; discriminate].
    pose proof (@E.unpair_level A ab_paired x y Hu) as [Hlv Hxy].
    rewrite Hab in Hlv; injection Hlv as Hlv.
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor;
        [ exact Hp1'
        | apply pl_hole
        | apply suffix23_levels; [congruence|congruence|exact Hsd] ].
    + exact Hcen.
  - (* overflow / ok *)
    destruct Hpd as [Hp1' [Hc0 Hd0]].
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [e|ne];
      ms_reduce; [|congruence].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor; [exact Hp1' | apply pl_hole | exact Hsd].
    + apply buffer_push_chain_levels;
        [rewrite E.level_pair; congruence | exact Hb2].
  - (* overflow / overflow *)
    destruct Hpd as [Hp1' [Hc0 Hd0]].
    destruct Hsd as [Hs1' [Ha0 He0]].
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [ecd|n1];
      ms_reduce; [|congruence].
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [eab|n2];
      ms_reduce; [|congruence].
    destruct (buffer_halve b2) as [midopt rest_pairs] eqn:Hh; ms_reduce.
    destruct (pair_each_buf rest_pairs) as [rest|] eqn:Hpe; ms_reduce;
      [| intros Hbad; discriminate].
    pose proof (@pair_each_buf_after_halve_preserves_levels A k b2 midopt
                  rest_pairs rest Hb2 Hh Hpe) as [Hmid Hrest].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. split.
    + constructor.
      * exact Hp1'.
      * constructor.
        -- apply suffix12_levels; [rewrite E.level_pair; congruence | exact Hmid].
        -- apply pl_hole.
        -- cbn -[E.level E.pair]. rewrite E.level_pair. congruence.
      * exact Hs1'.
    + exact Hrest.
Qed.

(** Index rewriting for [well_leveled_at] (the depth bookkeeping across a
    repair moves [S]s between the packet depth and the chain index). *)
Lemma well_leveled_at_eq :
  forall A i j (c : KChain A),
    i = j -> well_leveled_at i c -> well_leveled_at j c.
Proof. intros A i j c Hij H; subst; exact H. Qed.

(** Lifting [make_small]'s output levels through the Green tagging. *)
Lemma chain_to_kchain_g_well_leveled :
  forall A (c : Chain A) (k : nat),
    chain_levels_d k c ->
    well_leveled_at k (chain_to_kchain_g c).
Proof.
  intros A c. induction c as [b | p c' IH]; intros k Hc.
  - exact Hc.
  - cbn in Hc |- *. destruct Hc as [Hp Hc'].
    split; [exact Hp | apply IH; exact Hc'].
Qed.

(** Reduce while keeping the repair's building blocks folded. *)
Local Ltac gor_reduce :=
  cbn -[E.level E.pair E.unpair make_small green_prefix_concat
        green_suffix_concat prefix_concat suffix_concat chain_to_kchain_g].

(** The repair preserves depth-aware well-levelledness.  Needs
    [colors_consistent] for the Case-3 not-red shapes consumed by the
    yellow-variant concat level lemmas. *)
Lemma green_of_red_k_preserves_well_leveled :
  forall A k (c c' : KChain A),
    colors_consistent c ->
    well_leveled_at k c ->
    green_of_red_k c = Some c' ->
    well_leveled_at k c'.
Proof.
  intros A k c c' Hcc Hwl.
  unfold green_of_red_k.
  destruct c as [b | col [|pre1 i1 suf1] tail].
  - intros Hg; discriminate.
  - destruct col; intros Hg; discriminate.
  - destruct col; [intros Hg; discriminate | intros Hg; discriminate |].
    (* col = Red *)
    cbn in Hcc. destruct Hcc as [_ [Hyr [Hihole _Htailcc]]].
    cbn in Hwl. destruct Hwl as [Hpkt Hwltail].
    destruct i1 as [|pre2 child suf2]; gor_reduce.
    + (* Hole inner *)
      destruct tail as [b | col2 [|pre2 child suf2] c2]; gor_reduce.
      * (* Case 1: Ending tail *)
        destruct (make_small pre1 b suf1) as [cm|] eqn:Hms; gor_reduce;
          [| intros Hg; discriminate].
        intros Hg; injection Hg as Hg; subst c'.
        inversion Hpkt as [|? ? ? ? Hpre1 _ Hsuf1]; subst.
        cbn in Hwltail.
        apply chain_to_kchain_g_well_leveled.
        eapply make_small_preserves_levels;
          [exact Hpre1 | exact Hwltail | exact Hsuf1 | exact Hms].
      * (* Hole-packet tail: unreachable *)
        intros Hg; discriminate.
      * (* Case 2: ChainCons tail *)
        destruct (green_prefix_concat pre1 pre2) as [[pre1' pre2']|] eqn:Hgp;
          gor_reduce; [| intros Hg; discriminate].
        destruct (green_suffix_concat suf2 suf1) as [[suf2' suf1']|] eqn:Hgs;
          gor_reduce; [| intros Hg; discriminate].
        intros Hg; injection Hg as Hg; subst c'.
        inversion Hpkt as [|? ? ? ? Hpre1 _ Hsuf1]; subst.
        cbn in Hwltail. destruct Hwltail as [Hpkt2 Hwlc2].
        inversion Hpkt2 as [|? ? ? ? Hpre2 Hchild Hsuf2]; subst.
        pose proof (@green_prefix_concat_success_preserves_green_outer_levels
                      A k pre1 pre2 pre1' pre2' Hpre1 Hpre2 Hgp)
          as [_ [Hpre1' Hpre2']].
        pose proof (@green_suffix_concat_success_preserves_green_outer_levels
                      A k suf2 suf1 suf2' suf1' Hsuf2 Hsuf1 Hgs)
          as [Hsuf2' [_ Hsuf1']].
        gor_reduce. split.
        -- constructor;
             [ exact Hpre1'
             | constructor; [exact Hpre2' | exact Hchild | exact Hsuf2']
             | exact Hsuf1' ].
        -- eapply well_leveled_at_eq; [| exact Hwlc2]. lia.
    + (* Case 3: PNode inner *)
      cbn in Hyr. destruct Hyr as [Hpre2shape [Hsuf2shape _]].
      destruct (prefix_concat pre1 pre2) as [[pre1' pre2']|] eqn:Hpc;
        gor_reduce; [| intros Hg; discriminate].
      destruct (suffix_concat suf2 suf1) as [[suf2' suf1']|] eqn:Hsc;
        gor_reduce; [| intros Hg; discriminate].
      intros Hg; injection Hg as Hg; subst c'.
      inversion Hpkt as [|? ? ? ? Hpre1 Hinner Hsuf1]; subst.
      inversion Hinner as [|? ? ? ? Hpre2 Hchild Hsuf2]; subst.
      cbn in Hwltail.
      pose proof (@prefix_concat_preserves_outer_green_levels
                    A k pre1 pre2 pre1' pre2' Hpre1 Hpre2 Hpre2shape Hpc)
        as [_ [Hpre1' Hpre2']].
      pose proof (@suffix_concat_preserves_outer_green_levels
                    A k suf2 suf1 suf2' suf1' Hsuf2 Hsuf1 Hsuf2shape Hsc)
        as [Hsuf2' [_ Hsuf1']].
      gor_reduce. split.
      * constructor; [exact Hpre1' | apply pl_hole | exact Hsuf1'].
      * split.
        -- constructor; [exact Hpre2' | exact Hchild | exact Hsuf2'].
        -- eapply well_leveled_at_eq; [| exact Hwltail]. lia.
Qed.

(* ========================================================================== *)
(* Colour-consistency of make_small outputs (green_of_red_k Case 1).           *)
(* The shapes are STRUCTURAL: no level premises needed.                        *)
(* ========================================================================== *)

Lemma prefix23_green_shape :
  forall X (opt : option X) (p : X * X),
    buf5_is_green_shape (prefix23 opt p).
Proof. intros X opt [b c]; destruct opt; cbn; exact I. Qed.

Lemma suffix23_green_shape :
  forall X (p : X * X) (opt : option X),
    buf5_is_green_shape (suffix23 p opt).
Proof. intros X [b c] opt; destruct opt; cbn; exact I. Qed.

Lemma suffix12_not_red :
  forall X (x : X) (opt : option X),
    buf5_is_not_red_shape (suffix12 x opt).
Proof. intros X x opt; destruct opt; cbn; exact I. Qed.

Lemma prefix_decompose_shapes :
  forall X (b : Buf5 X),
    match prefix_decompose b with
    | BD_pre_underflow _ => True
    | BD_pre_ok b' => buf5_is_green_shape b'
    | BD_pre_overflow b' _ _ => buf5_is_green_shape b'
    end.
Proof. intros X b; destruct b; cbn; exact I. Qed.

Lemma suffix_decompose_shapes :
  forall X (b : Buf5 X),
    match suffix_decompose b with
    | BD_suf_underflow _ => True
    | BD_suf_ok b' => buf5_is_green_shape b'
    | BD_suf_overflow b' _ _ => buf5_is_green_shape b'
    end.
Proof. intros X b; destruct b; cbn; exact I. Qed.

Lemma mk_ending_colors :
  forall A (p1 : option (E.t A)) (mid : option (E.t A * E.t A))
         (s1 : option (E.t A)),
    colors_consistent (chain_to_kchain_g (mk_ending_from_options p1 mid s1)).
Proof.
  intros A p1 mid s1.
  destruct p1; destruct mid as [[? ?]|]; destruct s1; cbn; exact I.
Qed.

Lemma cc_tail_color_green_g :
  forall A (c : Chain A), cc_tail_color Green (chain_to_kchain_g c).
Proof.
  intros A c. destruct c; cbn; [exact I | discriminate].
Qed.

Lemma buffer_push_chain_colors :
  forall A (x : E.t A) (b : Buf5 (E.t A)),
    colors_consistent (chain_to_kchain_g (buffer_push_chain x b)).
Proof.
  intros A x b. destruct b; cbn; repeat split; try exact I; discriminate.
Qed.

Lemma buffer_inject_chain_colors :
  forall A (b : Buf5 (E.t A)) (x : E.t A),
    colors_consistent (chain_to_kchain_g (buffer_inject_chain b x)).
Proof.
  intros A b x. destruct b; cbn; repeat split; try exact I; discriminate.
Qed.

Lemma make_small_colors_consistent :
  forall A (b1 b2 b3 : Buf5 (E.t A)) (c : Chain A),
    make_small b1 b2 b3 = Some c ->
    colors_consistent (chain_to_kchain_g c).
Proof.
  intros A b1 b2 b3 c.
  unfold make_small.
  pose proof (@prefix_decompose_shapes (E.t A) b1) as Hps.
  pose proof (@suffix_decompose_shapes (E.t A) b3) as Hss.
  revert Hps Hss.
  destruct (prefix_decompose b1) as [p1opt|p1'|p1' c0 d0];
    destruct (suffix_decompose b3) as [s1opt|s1'|s1' a0 e0];
    intros Hps Hss; cbn in Hps, Hss; ms_reduce.
  - (* underflow / underflow *)
    destruct (buffer_unsandwich b2) as [midopt|ab rest cd]; ms_reduce.
    + destruct midopt as [elem|].
      * destruct (E.unpair A elem) as [[x y]|]; ms_reduce;
          [| intros Hbad; discriminate].
        intros Hmake; injection Hmake as Hc; subst c.
        destruct p1opt; destruct s1opt; cbn; exact I.
      * intros Hmake; injection Hmake as Hc; subst c.
        destruct p1opt; destruct s1opt; cbn; exact I.
    + destruct (E.unpair A ab) as [[xa ya]|]; ms_reduce;
        [| intros Hbad; discriminate].
      destruct (E.unpair A cd) as [[xc yc]|]; ms_reduce;
        [| intros Hbad; discriminate].
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce.
      repeat split;
        [destruct p1opt; exact I | destruct s1opt; exact I].
  - (* underflow / ok *)
    destruct (buf5_pop_naive b2) as [[cd rest]|]; ms_reduce.
    + destruct (E.unpair A cd) as [[x y]|]; ms_reduce;
        [| intros Hbad; discriminate].
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce.
      repeat split; [destruct p1opt; exact I | exact Hss].
    + destruct p1opt as [x|].
      * destruct (buf5_push_naive x s1') as [s1''|]; ms_reduce;
          [| intros Hbad; discriminate].
        intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact I.
      * intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact I.
  - (* underflow / overflow *)
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [e|ne]; ms_reduce;
      [| intros Hbad; discriminate].
    destruct (suffix_rot b2 (E.pair A a0 e0 e)) as [cd_paired center];
      ms_reduce.
    destruct (E.unpair A cd_paired) as [[x y]|]; ms_reduce;
      [| intros Hbad; discriminate].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce.
    repeat split; [destruct p1opt; exact I | exact Hss].
  - (* ok / underflow *)
    destruct (buf5_eject_naive b2) as [[rest ab]|]; ms_reduce.
    + destruct (E.unpair A ab) as [[x y]|]; ms_reduce;
        [| intros Hbad; discriminate].
      intros Hmake; injection Hmake as Hc; subst c.
      ms_reduce.
      repeat split; [exact Hps | destruct s1opt; exact I].
    + destruct s1opt as [x|].
      * destruct (buf5_inject_naive p1' x) as [p1''|]; ms_reduce;
          [| intros Hbad; discriminate].
        intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact I.
      * intros Hmake; injection Hmake as Hc; subst c. ms_reduce. exact I.
  - (* ok / ok *)
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce. repeat split; [exact Hps | exact Hss].
  - (* ok / overflow *)
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [e|ne]; ms_reduce;
      [| intros Hbad; discriminate].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce.
    repeat split;
      [ exact Hps | exact Hss
      | destruct b2; cbn; try exact I; discriminate
      | destruct b2; cbn; repeat split ].
  - (* overflow / underflow *)
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [e|ne]; ms_reduce;
      [| intros Hbad; discriminate].
    destruct (prefix_rot (E.pair A c0 d0 e) b2) as [center ab_paired];
      ms_reduce.
    destruct (E.unpair A ab_paired) as [[x y]|]; ms_reduce;
      [| intros Hbad; discriminate].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce.
    repeat split; [exact Hps | destruct s1opt; exact I].
  - (* overflow / ok *)
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [e|ne]; ms_reduce;
      [| intros Hbad; discriminate].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce.
    repeat split;
      [ exact Hps | exact Hss
      | destruct b2; cbn; try exact I; discriminate
      | destruct b2; cbn; repeat split ].
  - (* overflow / overflow *)
    destruct (Nat.eq_dec (E.level A c0) (E.level A d0)) as [ecd|n1]; ms_reduce;
      [| intros Hbad; discriminate].
    destruct (Nat.eq_dec (E.level A a0) (E.level A e0)) as [eab|n2]; ms_reduce;
      [| intros Hbad; discriminate].
    destruct (buffer_halve b2) as [midopt rest_pairs]; ms_reduce.
    destruct (pair_each_buf rest_pairs) as [rest|]; ms_reduce;
      [| intros Hbad; discriminate].
    intros Hmake; injection Hmake as Hc; subst c.
    ms_reduce.
    repeat split; [exact Hps | exact Hss | destruct midopt; exact I].
Qed.

(* ========================================================================== *)
(* Per-operation obligations (Admitted scaffolding — the to-do list).          *)
(* ========================================================================== *)

Lemma push_kt4_total :
  forall A (x : E.t A) (c : KChain A),
    I_kt c -> E.level A x = 0 -> exists c', push_kt4 x c = PushOk c'.
Proof.
  intros A x c HI Hx.
  destruct HI as [Hreg [Hcc Hwl]].
  destruct c as [b | col [|pre i suf] tail].
  - destruct b; cbn -[yellow_wrap_pr green_of_red_k]; eexists; reflexivity.
  - cbn in Hcc; contradiction.
  - destruct col.
    + (* Green: pre is B2/B3; push goes through yellow_wrap_pr *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [_Hpkt Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole Htail]]].
      destruct pre; destruct Hshape as [Hp _Hs]; cbn in Hp; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k];
        (eapply yellow_wrap_pr_total;
         eapply yellow_wrap_pr_total_pre_of_consistent; [exact Htail | exact Hwltail]).
    + (* Yellow: B1/B2/B3 direct; B4 fires one bounded repair *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [Hpkt _Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole _Htail]]].
      destruct pre; destruct Hshape as [Hp _Hs]; cbn in Hp; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k].
      * eexists; reflexivity.
      * eexists; reflexivity.
      * eexists; reflexivity.
      * edestruct yellow_push_red_repair_witness_from_ready as [crep Hrep].
        -- exact Hx.
        -- exact Hpkt.
        -- eapply ready_at_of_consistent; [| exact Hcc | exact Hwl].
           discriminate.
        -- rewrite Hrep. eexists; reflexivity.
    + (* Red top contradicts regular_kt_top *)
      destruct Hreg as [Htop _]. cbn in Htop. congruence.
Qed.

(** Preservation of the new (colour + level) clauses — the genuine residue.
    The regular_kt_top clause is discharged below by reusing the proven
    [*_preserves_regular_top]. *)
Lemma push_kt4_preserves_colors_leveled :
  forall A (x : E.t A) (c c' : KChain A),
    I_kt c -> push_kt4 x c = PushOk c' -> colors_consistent c' /\ well_leveled c'.
Proof. Admitted.

Lemma push_kt4_preserves_I_kt :
  forall A (x : E.t A) (c c' : KChain A),
    I_kt c -> push_kt4 x c = PushOk c' -> I_kt c'.
Proof.
  intros A x c c' HI Hp.
  destruct (@push_kt4_preserves_colors_leveled A x c c' HI Hp) as [Hcc' Hwl'].
  destruct HI as [Hreg _].
  split; [ eapply push_kt4_preserves_regular_top; [exact Hreg | exact Hp]
         | split; [exact Hcc' | exact Hwl'] ].
Qed.

Lemma inject_kt4_total :
  forall A (c : KChain A) (x : E.t A),
    I_kt c -> E.level A x = 0 -> exists c', inject_kt4 c x = PushOk c'.
Proof.
  intros A c x HI Hx.
  destruct HI as [Hreg [Hcc Hwl]].
  destruct c as [b | col [|pre i suf] tail].
  - destruct b; cbn -[yellow_wrap_pr green_of_red_k]; eexists; reflexivity.
  - cbn in Hcc; contradiction.
  - destruct col.
    + (* Green: suf is B2/B3 *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [_Hpkt Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole Htail]]].
      destruct suf; destruct Hshape as [_Hp Hs]; cbn in Hs; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k];
        (eapply yellow_wrap_pr_total;
         eapply yellow_wrap_pr_total_pre_of_consistent; [exact Htail | exact Hwltail]).
    + (* Yellow: suf B1/B2/B3 direct; B4 fires one bounded repair *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [Hpkt _Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole _Htail]]].
      destruct suf; destruct Hshape as [_Hp Hs]; cbn in Hs; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k].
      * eexists; reflexivity.
      * eexists; reflexivity.
      * eexists; reflexivity.
      * edestruct yellow_inject_red_repair_witness_from_ready as [crep Hrep].
        -- exact Hx.
        -- exact Hpkt.
        -- eapply ready_at_of_consistent; [| exact Hcc | exact Hwl].
           discriminate.
        -- rewrite Hrep. eexists; reflexivity.
    + destruct Hreg as [Htop _]. cbn in Htop. congruence.
Qed.

Lemma inject_kt4_preserves_colors_leveled :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> inject_kt4 c x = PushOk c' -> colors_consistent c' /\ well_leveled c'.
Proof. Admitted.

Lemma inject_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> inject_kt4 c x = PushOk c' -> I_kt c'.
Proof.
  intros A c c' x HI Hp.
  destruct (@inject_kt4_preserves_colors_leveled A c c' x HI Hp) as [Hcc' Hwl'].
  destruct HI as [Hreg _].
  split; [ eapply inject_kt4_preserves_regular_top; [exact Hreg | exact Hp]
         | split; [exact Hcc' | exact Hwl'] ].
Qed.

Lemma pop_kt4_total :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c -> exists x c', pop_kt4 c = PopOk x c'.
Proof.
  intros A c HI Hne.
  destruct HI as [Hreg [Hcc Hwl]].
  destruct c as [b | col [|pre i suf] tail].
  - destruct b; cbn in Hne; try contradiction;
      cbn -[yellow_wrap_pr green_of_red_k]; repeat eexists; reflexivity.
  - cbn in Hcc; contradiction.
  - destruct col.
    + (* Green: pre B2/B3 *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [_Hpkt Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole Htail]]].
      destruct pre; destruct Hshape as [Hp _Hs]; cbn in Hp; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k];
        (edestruct yellow_wrap_pr_total as [crep Hrep];
         [ eapply yellow_wrap_pr_total_pre_of_consistent; [exact Htail | exact Hwltail]
         | rewrite Hrep; repeat eexists; reflexivity ]).
    + (* Yellow: B2/B3/B4 direct; B1 fires one bounded repair *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [Hpkt _Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole _Htail]]].
      destruct pre; destruct Hshape as [Hp _Hs]; cbn in Hp; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k].
      * edestruct yellow_pop_red_repair_witness_from_ready as [crep Hrep].
        -- exact Hpkt.
        -- eapply ready_at_of_consistent; [| exact Hcc | exact Hwl].
           discriminate.
        -- rewrite Hrep. repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
    + destruct Hreg as [Htop _]. cbn in Htop. congruence.
Qed.

Lemma pop_kt4_preserves_colors_leveled :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> pop_kt4 c = PopOk x c' -> colors_consistent c' /\ well_leveled c'.
Proof. Admitted.

Lemma pop_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> pop_kt4 c = PopOk x c' -> I_kt c'.
Proof.
  intros A c c' x HI Hp.
  destruct (@pop_kt4_preserves_colors_leveled A c c' x HI Hp) as [Hcc' Hwl'].
  destruct HI as [Hreg _].
  split; [ eapply pop_kt4_preserves_regular_top; [exact Hreg | exact Hp]
         | split; [exact Hcc' | exact Hwl'] ].
Qed.

Lemma eject_kt4_total :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c -> exists x c', eject_kt4 c = PopOk x c'.
Proof.
  intros A c HI Hne.
  destruct HI as [Hreg [Hcc Hwl]].
  destruct c as [b | col [|pre i suf] tail].
  - destruct b; cbn in Hne; try contradiction;
      cbn -[yellow_wrap_pr green_of_red_k]; repeat eexists; reflexivity.
  - cbn in Hcc; contradiction.
  - destruct col.
    + (* Green: suf B2/B3 *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [_Hpkt Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole Htail]]].
      destruct suf; destruct Hshape as [_Hp Hs]; cbn in Hs; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k];
        (edestruct yellow_wrap_pr_total as [crep Hrep];
         [ eapply yellow_wrap_pr_total_pre_of_consistent; [exact Htail | exact Hwltail]
         | rewrite Hrep; repeat eexists; reflexivity ]).
    + (* Yellow: suf B2/B3/B4 direct; B1 fires one bounded repair *)
      pose proof Hwl as Hwl0. cbn in Hwl0. destruct Hwl0 as [Hpkt _Hwltail].
      pose proof Hcc as Hcc0. cbn in Hcc0.
      destruct Hcc0 as [Hshape [_Hyr [_Hihole _Htail]]].
      destruct suf; destruct Hshape as [_Hp Hs]; cbn in Hs; try contradiction;
        cbn -[yellow_wrap_pr green_of_red_k].
      * edestruct yellow_eject_red_repair_witness_from_ready as [crep Hrep].
        -- exact Hpkt.
        -- eapply ready_at_of_consistent; [| exact Hcc | exact Hwl].
           discriminate.
        -- rewrite Hrep. repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
      * repeat eexists; reflexivity.
    + destruct Hreg as [Htop _]. cbn in Htop. congruence.
Qed.

Lemma eject_kt4_preserves_colors_leveled :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> eject_kt4 c = PopOk x c' -> colors_consistent c' /\ well_leveled c'.
Proof. Admitted.

Lemma eject_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> eject_kt4 c = PopOk x c' -> I_kt c'.
Proof.
  intros A c c' x HI Hp.
  destruct (@eject_kt4_preserves_colors_leveled A c c' x HI Hp) as [Hcc' Hwl'].
  destruct HI as [Hreg _].
  split; [ eapply eject_kt4_preserves_regular_top; [exact Hreg | exact Hp]
         | split; [exact Hcc' | exact Hwl'] ].
Qed.

(* ========================================================================== *)
(* The keystone: unconditional WC O(1) per operation on I_kt states.           *)
(* Cost clause reuses the already-closed [*_green_calls_le_1].                  *)
(* ========================================================================== *)

Theorem deque_wc_o1_push :
  forall A (x : E.t A) (c : KChain A),
    I_kt c -> E.level A x = 0 ->
    exists c',
      push_kt4 x c = PushOk c' /\ I_kt c' /\ push_kt4_green_calls x c <= 1.
Proof.
  intros A x c HI Hx.
  destruct (@push_kt4_total A x c HI Hx) as [c' Hc'].
  exists c'. split; [exact Hc'|]. split.
  - exact (@push_kt4_preserves_I_kt A x c c' HI Hc').
  - apply push_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_inject :
  forall A (c : KChain A) (x : E.t A),
    I_kt c -> E.level A x = 0 ->
    exists c',
      inject_kt4 c x = PushOk c' /\ I_kt c' /\ inject_kt4_green_calls c x <= 1.
Proof.
  intros A c x HI Hx.
  destruct (@inject_kt4_total A c x HI Hx) as [c' Hc'].
  exists c'. split; [exact Hc'|]. split.
  - exact (@inject_kt4_preserves_I_kt A c c' x HI Hc').
  - apply inject_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_pop :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c ->
    exists x c',
      pop_kt4 c = PopOk x c' /\ I_kt c' /\ pop_kt4_green_calls c <= 1.
Proof.
  intros A c HI Hne.
  destruct (@pop_kt4_total A c HI Hne) as [x [c' Hc']].
  exists x, c'. split; [exact Hc'|]. split.
  - exact (@pop_kt4_preserves_I_kt A c c' x HI Hc').
  - apply pop_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_eject :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c ->
    exists x c',
      eject_kt4 c = PopOk x c' /\ I_kt c' /\ eject_kt4_green_calls c <= 1.
Proof.
  intros A c HI Hne.
  destruct (@eject_kt4_total A c HI Hne) as [x [c' Hc']].
  exists x, c'. split; [exact Hc'|]. split.
  - exact (@eject_kt4_preserves_I_kt A c c' x HI Hc').
  - apply eject_kt4_green_calls_le_1.
Qed.

(* The admit list IS the to-do list.  Closure = these report "Closed under the
   global context". *)
Print Assumptions deque_wc_o1_push.
Print Assumptions deque_wc_o1_inject.
Print Assumptions deque_wc_o1_pop.
Print Assumptions deque_wc_o1_eject.
