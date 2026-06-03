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

From KTDeque.Common Require Import Prelude Color Buf5 Element.
From KTDeque.DequePtr Require Import Model OpsKT OpsKTRegular PublicTheorems.

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
    outer buffers.  This is KT99's "the first non-yellow below is green"
    localised: it is exactly what [green_of_red_k]'s Case-2 repair needs
    ([green_of_red_k_ready_at]), and is the recursive clause the prior
    [*_ready_state] accretion never closed. *)
Definition tail_green_ready {A : Type} (tail : KChain A) : Prop :=
  match tail with
  | KEnding _ => True
  | KCons _ (PNode pre2 _ suf2) _ =>
      buf5_is_green_shape pre2 /\ buf5_is_green_shape suf2
  | KCons _ Hole _ => False
  end.

Fixpoint colors_consistent {A : Type} (c : KChain A) : Prop :=
  match c with
  | KEnding _ => True
  | KCons col (PNode pre i suf) tail =>
      cc_color_shape col pre suf /\
      cc_yellow_run i /\
      (match i with Hole => tail_green_ready tail | _ => True end) /\
      colors_consistent tail
  | KCons _ Hole _ => False
  end.

(** Level-consistency: buffers at chain-depth [k] hold level-[k] elements.
    Lifts Model.v's [buf_all_at_level]/[packet_levels] to [KChain].  Over the
    production instance [E = ElementTree], positive-level elements are
    unpairable (a theorem, not an axiom), which is what the repair's underflow
    arms need. *)
Fixpoint well_leveled_at {A : Type} (k : nat) (c : KChain A) : Prop :=
  match c with
  | KEnding b => buf_all_at_level k b
  | KCons _ p tail => packet_levels k p /\ well_leveled_at (S k) tail
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
    colors_consistent (KCons col (PNode pre i suf) tail) ->
    well_leveled_at k (KCons col (PNode pre i suf) tail) ->
    green_of_red_k_context_ready_at k i tail.
Proof.
  intros A k col pre i suf tail Hcc Hwl.
  cbn in Hcc. destruct Hcc as [_Hshape [Hyr [Hihole _Htail]]].
  cbn in Hwl. destruct Hwl as [Hpkt Hwltail].
  destruct i as [|ipre ichild isuf].
  - (* i = Hole *)
    unfold green_of_red_k_context_ready_at.
    destruct tail as [b | col2 [|tpre tchild tsuf] tail2].
    + (* KEnding b *) cbn in Hwltail |- *. exact Hwltail.
    + (* KCons col2 Hole tail2 *) cbn in Hihole. contradiction.
    + (* KCons col2 (PNode tpre tchild tsuf) tail2 *)
      cbn in Hihole, Hwltail |- *.
      destruct Hihole as [Hp2 Hs2]. destruct Hwltail as [Hpkt2 _].
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
    colors_consistent (KCons col (PNode pre i suf) tail) ->
    well_leveled_at k (KCons col (PNode pre i suf) tail) ->
    green_of_red_k_ready_at k (PNode pre' i suf') tail.
Proof.
  intros A k col pre pre' i suf suf' tail Hcc Hwl.
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
    + eapply ready_at_of_consistent; eassumption.
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
    chain_levels k (mk_ending_from_options p1 mid s1).
Proof.
  intros A k p1 mid s1 Hp1 Hmid Hs1.
  destruct p1 as [a1|]; destruct mid as [[a2 b2]|]; destruct s1 as [a3|];
    cbn in Hp1, Hmid, Hs1 |- *;
    try (destruct Hmid);
    constructor; cbn; repeat split; auto.
Qed.

Lemma buffer_push_chain_levels :
  forall A k (x : E.t A) (b : Buf5 (E.t A)),
    E.level A x = k -> buf_all_at_level k b ->
    chain_levels k (buffer_push_chain x b).
Proof.
  intros A k x b Hx Hb.
  destruct b; cbn in Hb |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat constructor; cbn in *; auto.
Qed.

Lemma buffer_inject_chain_levels :
  forall A k (x : E.t A) (b : Buf5 (E.t A)),
    E.level A x = k -> buf_all_at_level k b ->
    chain_levels k (buffer_inject_chain b x).
Proof.
  intros A k x b Hx Hb.
  destruct b; cbn in Hb |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat constructor; cbn in *; auto.
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
        -- eapply ready_at_of_consistent; [exact Hcc | exact Hwl].
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
        -- eapply ready_at_of_consistent; [exact Hcc | exact Hwl].
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
        -- eapply ready_at_of_consistent; [exact Hcc | exact Hwl].
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
        -- eapply ready_at_of_consistent; [exact Hcc | exact Hwl].
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
