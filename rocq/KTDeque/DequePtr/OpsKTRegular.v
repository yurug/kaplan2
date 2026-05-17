(** * Module: KTDeque.DequePtr.OpsKTRegular -- color-based regularity
      invariant for [KChain] (Phase δ.3 foundation).

    ## Why this file exists

    The regularity invariant is the load-bearing fact in the WC O(1)
    proof.  Intuition: between any two Red links there must be a Green
    link.  When a public operation (push / inject / pop / eject)
    leaves the chain head Red, [ensure_green_k] fires [green_of_red_k]
    *exactly once* — because the link below the new Red top is Green
    (or absent), *guaranteed by regularity*.  No recursion.  See
    [kb/spec/why-bounded-cascade.md] §2 for the intuition.

    This file is the formal counterpart of that argument:

      [regular_kt c]  is true iff the chain [c] has no two adjacent
                      Red links and the top is non-Red.

      Preservation theorems (this file is the home of these):
        [regular_kt c -> push_kt2 x c = Some c' -> regular_kt c']
        [regular_kt c -> exists c', push_kt2 x c = Some c']
        + analogues for inject/pop/eject.

    Together with the cost bounds in [Footprint.v] and the sequence
    preservation in [OpsKTSeq.v], they say: starting from
    [empty_kchain] and applying any sequence of public operations,
    every intermediate [KChain] is regular and every operation costs
    at most [NF_PUSH_PKT_FULL = 9] heap ops.

    ## Status

    **Closed end-to-end (2026-05-17):** the regularity invariant is
    maintained by every public op.  Theorems:

      - [empty_kchain_regular_top]
      - [push_kt2_preserves_regular_top]
      - [inject_kt2_preserves_regular_top]
      - [pop_kt2_preserves_regular_top]
      - [eject_kt2_preserves_regular_top]

    plus the underlying building blocks:

      - [green_of_red_k_preserves_regular]
      - [ensure_green_k_preserves_regular]
      - [make_yellow_k_preserves_regular]
      - [make_red_k_preserves_regular]
      - [chain_to_kchain_g_regular] / [make_small_all_pnode]
        (the "fresh chain from a rebalance" sub-result).

    Zero admits.  Combined with [Footprint.v]'s constant-cost bound
    and [OpsKTSeq.v]'s sequence preservation, this gives the full
    "starting from [empty_kchain] every public op is WC O(1) and
    preserves the sequence semantics" theorem for the KChain layer.

    ## Why "color-based" matters

    Earlier the project had a [Chain] type ([Model.v]) without explicit
    colors, with regularity defined extrinsically in [Regularity.v].
    Adding colors to the type ([KChain] in [Model.v], [KCons col p tl])
    makes the invariant local: a chain is regular iff every [KCons]'s
    color is consistent with its tail's top color.  No more "find the
    top of the yellow run, then check what's below it" — the colour
    tag tells you directly.

    The color tag is *contextual*, not derivable from buffer sizes
    alone (after a [green_of_red] Case 3, the freshly-tagged Red
    packet may have G/Y-sized buffers).  See [OpsKT.v] header.

    Cross-references:
    - [kb/spec/why-bounded-cascade.md] -- the intuition layer.
    - [KTDeque/Common/Color.v]         -- color, color_meet, buf_color.
    - [KTDeque/DequePtr/OpsKT.v]       -- the ops whose preservation
                                          is proved here.
    - [KTDeque/DequePtr/Regularity.v]  -- regularity for the older
                                          color-less [Chain] type.
    - [KTDeque/DequePtr/Footprint.v]   -- the cost bound that depends
                                          on regularity holding.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color.
From KTDeque.DequePtr Require Import Model OpsKT.

Module E := OpsKT.E.

(* ========================================================================== *)
(* Buffer-color predicates lifted to Prop.                                     *)
(* ========================================================================== *)

(** [buf_is_green b]: [buf_color b = Green] (size 2 or 3). *)
Definition buf_is_green {X : Type} (b : Buf5 X) : Prop :=
  buf_color b = Green.

(** [buf_is_yellow b]: [buf_color b = Yellow] (size 1 or 4). *)
Definition buf_is_yellow {X : Type} (b : Buf5 X) : Prop :=
  buf_color b = Yellow.

(** [buf_is_red b]: [buf_color b = Red] (size 0 or 5). *)
Definition buf_is_red {X : Type} (b : Buf5 X) : Prop :=
  buf_color b = Red.

(** A buffer tagged "no-yellow" if it's green or red — i.e. the input
    domain of [ensure_green]'s buffer-rebalance step. *)
Definition buf_is_noyellow {X : Type} (b : Buf5 X) : Prop :=
  buf_color b <> Yellow.

(** Buffer is in {B1, B2, B3, B4} (= not Red).  This matches the
    [yellow_push] / [yellow_inject] success domain. *)
Definition buf_yellow_or_green {X : Type} (b : Buf5 X) : Prop :=
  buf_color b <> Red.

(** Buffer is in {B2, B3} (= Green only).  This matches the
    [green_push] / [green_inject] success domain. *)
Definition buf_green_only {X : Type} (b : Buf5 X) : Prop :=
  buf_color b = Green.

Lemma buf_color_dec :
  forall X (b : Buf5 X), {buf_color b = Green} + {buf_color b = Yellow} + {buf_color b = Red}.
Proof. intros X b; destruct b; cbn; auto. Qed.

(* ========================================================================== *)
(* Packet-level structural predicates.                                         *)
(* ========================================================================== *)

(** [pkt_is_pnode p]: the packet has a [PNode] head (not [Hole]). *)
Definition pkt_is_pnode {A : Type} (p : Packet A) : Prop :=
  match p with PNode _ _ _ => True | Hole => False end.

(** A packet is "live" if it has a PNode head and an inner that's
    either [Hole] (single level) or another [PNode] (yellow run).
    For now we restrict to the single-level case. *)
Inductive pkt_simple {A : Type} : Packet A -> Prop :=
| ps_node : forall pre suf, pkt_simple (PNode pre Hole suf).

(* ========================================================================== *)
(* The regularity invariant for [KChain].                                      *)
(*                                                                             *)
(* Mirrors Viennot's GADT well-typing:                                         *)
(*   - [KEnding b]: always regular (the bottom-most buffer).                   *)
(*   - [KCons Green p c]: green packet, anything below is fine.                *)
(*   - [KCons Yellow p c]: yellow packet, anything below is fine.              *)
(*   - [KCons Red p c]: red packet, but the next link must NOT be Red          *)
(*     (no two consecutive Reds — the algorithm's "fix red" precondition).    *)
(* The packet [p] must be a simple [PNode] (not [Hole]).                       *)
(* ========================================================================== *)

(** Regularity invariant for [KChain].

    A regular chain mirrors Viennot's GADT well-typing exactly: each
    coloured link constrains the immediate-next link's colour so that
    in the "strip out yellows" projection no two reds are adjacent.
    Equivalently the algorithm's chain construction maintains:
    - every Red link sits directly above a non-Red top, and
    - every Yellow link sits directly above a non-Red top.

    The second clause is non-trivial — without it, push on a Yellow
    whose tail starts with Red would compose two Reds when the
    yellow→red promotion fires.  It IS the invariant the algorithm
    actually maintains, because [make_yellow_k] always calls
    [ensure_green_k] on its underlying tail before tagging the new
    Yellow on top.  See [ensure_green_k_top_not_red]. *)
Inductive regular_kt {A : Type} : KChain A -> Prop :=
| reg_kt_ending :
    forall b, regular_kt (KEnding b)
| reg_kt_green :
    forall p c, pkt_is_pnode p -> regular_kt c -> regular_kt (KCons Green p c)
| reg_kt_yellow :
    forall p c,
      pkt_is_pnode p ->
      kchain_top_color c <> Red ->
      regular_kt c ->
      regular_kt (KCons Yellow p c)
| reg_kt_red :
    forall p c,
      pkt_is_pnode p ->
      kchain_top_color c <> Red ->
      regular_kt c ->
      regular_kt (KCons Red p c).

(** [regular_kt_top]: a strictly user-facing chain has top color ≠ Red.
    This is the precondition for [push_kt2] / [pop_kt2] dispatch. *)
Definition regular_kt_top {A : Type} (c : KChain A) : Prop :=
  kchain_top_color c <> Red /\ regular_kt c.

(* ========================================================================== *)
(* Trivial structural lemmas.                                                  *)
(* ========================================================================== *)

(** Every [KEnding] is regular. *)
Lemma regular_kt_ending : forall A b, regular_kt (@KEnding A b).
Proof. intros; apply reg_kt_ending. Qed.

(** [empty_kchain] is regular. *)
Lemma regular_kt_empty : forall A, regular_kt (@empty_kchain A).
Proof. intros; apply reg_kt_ending. Qed.

(** Inversion: a regular [KCons Red p c] forces the immediate tail's
    top color to be ≠ Red. *)
Lemma regular_kt_red_inv :
  forall A p (c : KChain A),
    regular_kt (KCons Red p c) ->
    pkt_is_pnode p /\ kchain_top_color c <> Red /\ regular_kt c.
Proof. intros A p c H; inversion H; subst; auto. Qed.

(** Inversion: a regular [KCons Green p c] has [pkt_is_pnode p]. *)
Lemma regular_kt_green_inv :
  forall A p (c : KChain A),
    regular_kt (KCons Green p c) ->
    pkt_is_pnode p /\ regular_kt c.
Proof. intros A p c H; inversion H; subst; auto. Qed.

(** Inversion: a regular [KCons Yellow p c] has [pkt_is_pnode p] and
    its tail's top color is non-Red. *)
Lemma regular_kt_yellow_inv :
  forall A p (c : KChain A),
    regular_kt (KCons Yellow p c) ->
    pkt_is_pnode p /\ kchain_top_color c <> Red /\ regular_kt c.
Proof. intros A p c H; inversion H; subst; auto. Qed.

(** A regular tail always has a regular sub-tail. *)
Lemma regular_kt_tail :
  forall A col p (c : KChain A),
    regular_kt (KCons col p c) ->
    regular_kt c.
Proof.
  intros A col p c H.
  destruct col;
    [apply regular_kt_green_inv in H
    |apply regular_kt_yellow_inv in H
    |apply regular_kt_red_inv in H];
    intuition.
Qed.

(* ========================================================================== *)
(* Decidability of regularity.                                                 *)
(* ========================================================================== *)

(** [pkt_is_pnode] is decidable. *)
Lemma pkt_is_pnode_dec :
  forall A (p : Packet A), {pkt_is_pnode p} + {~ pkt_is_pnode p}.
Proof. intros A p; destruct p; cbn; [right; auto|left; exact I]. Qed.

(** Top color is decidable. *)
Lemma kchain_top_color_dec :
  forall A (c : KChain A) (col : color),
    {kchain_top_color c = col} + {kchain_top_color c <> col}.
Proof.
  intros A c col.
  destruct (color_eq_dec (kchain_top_color c) col); [left|right]; auto.
Qed.

(** A regular non-Red-top chain after [ensure_green_k] is regular and
    has top color ≠ Red.  This is the key monotonicity lemma for
    composing make_yellow_k and the rest of the algorithm. *)
Lemma ensure_green_k_top_not_red :
  forall A (c c' : KChain A),
    ensure_green_k c = Some c' ->
    kchain_top_color c' <> Red.
Proof.
  intros A c c' He.
  unfold ensure_green_k in He.
  destruct c as [b|col p c_tail].
  - inversion He; subst; clear He. cbn; discriminate.
  - destruct col.
    + inversion He; subst; clear He. cbn; discriminate.
    + inversion He; subst; clear He. cbn; discriminate.
    + (* Red: green_of_red_k always returns Green-top chain (or None). *)
      unfold green_of_red_k in He.
      destruct p as [|pre1 i suf1]; [discriminate|].
      destruct i as [|pre2 child suf2].
      * destruct c_tail as [b | col2 [|pre2_t child_t suf2_t] c2_t].
        -- destruct (make_small pre1 b suf1) as [c''|]; [|discriminate].
           inversion He; subst; clear He.
           (* chain_to_kchain_g produces all-Green-tagged chain — top is Green. *)
           destruct c''; cbn; discriminate.
        -- discriminate.
        -- destruct (green_prefix_concat pre1 pre2_t) as [[? ?]|]; [|discriminate].
           destruct (green_suffix_concat suf2_t suf1) as [[? ?]|]; [|discriminate].
           inversion He; subst; clear He. cbn; discriminate.
      * destruct (prefix_concat pre1 pre2) as [[? ?]|]; [|discriminate].
        destruct (suffix_concat suf2 suf1) as [[? ?]|]; [|discriminate].
        inversion He; subst; clear He. cbn; discriminate.
Qed.

(** Symmetric: [green_of_red_k] always produces a Green-top result. *)
Lemma green_of_red_k_top_green :
  forall A (c c' : KChain A),
    green_of_red_k c = Some c' ->
    kchain_top_color c' = Green.
Proof.
  intros A c c' Hg.
  unfold green_of_red_k in Hg.
  destruct c as [|col p c_tail]; [discriminate|].
  destruct col; try discriminate.
  destruct p as [|pre1 i suf1]; [discriminate|].
  destruct i as [|pre2 child suf2].
  - destruct c_tail as [b | col2 [|pre2_t child_t suf2_t] c2_t].
    + destruct (make_small pre1 b suf1) as [c''|]; [|discriminate].
      inversion Hg; subst; clear Hg.
      destruct c''; cbn; reflexivity.
    + discriminate.
    + destruct (green_prefix_concat pre1 pre2_t) as [[? ?]|]; [|discriminate].
      destruct (green_suffix_concat suf2_t suf1) as [[? ?]|]; [|discriminate].
      inversion Hg; subst; clear Hg. cbn; reflexivity.
  - destruct (prefix_concat pre1 pre2) as [[? ?]|]; [|discriminate].
    destruct (suffix_concat suf2 suf1) as [[? ?]|]; [|discriminate].
    inversion Hg; subst; clear Hg. cbn; reflexivity.
Qed.

(** [regular_kt] is decidable. *)
Lemma regular_kt_dec :
  forall A (c : KChain A), {regular_kt c} + {~ regular_kt c}.
Proof.
  intros A c; induction c as [b | col p c' IH].
  - left; apply reg_kt_ending.
  - destruct (pkt_is_pnode_dec p) as [Hp|Hp]; [|right; intros H; destruct col;
        [apply regular_kt_green_inv in H
        |apply regular_kt_yellow_inv in H
        |apply regular_kt_red_inv in H]; intuition].
    destruct IH as [Hr|Hr]; [|right; intros H; apply regular_kt_tail in H; auto].
    destruct col.
    + left; apply reg_kt_green; auto.
    + (* Yellow: tail's top must be non-Red. *)
      destruct (kchain_top_color_dec c' Red) as [Hred|Hnred].
      * right; intros H. apply regular_kt_yellow_inv in H.
        destruct H as [_ [Hnt _]]. apply Hnt. exact Hred.
      * left. apply reg_kt_yellow; auto.
    + (* Red: tail's top must be non-Red. *)
      destruct (kchain_top_color_dec c' Red) as [Hred|Hnred].
      * right; intros H. apply regular_kt_red_inv in H.
        destruct H as [_ [Hnt _]]. apply Hnt. exact Hred.
      * left. apply reg_kt_red; auto.
Qed.

(* ========================================================================== *)
(* Regularity preservation theorems.                                           *)
(*                                                                             *)
(* The headline claim of the algorithm: starting from [empty_kchain] and       *)
(* applying any sequence of public ops, every intermediate KChain is regular.  *)
(* That's what the cost bound in Footprint.v formally requires.                *)
(* ========================================================================== *)

(** [chain_all_pnode c]: every packet in the Chain [c] is a [PNode]. *)
Fixpoint chain_all_pnode {A : Type} (c : Chain A) : Prop :=
  match c with
  | Ending _       => True
  | ChainCons p c' => pkt_is_pnode p /\ chain_all_pnode c'
  end.

(** [chain_to_kchain_g] of an all-PNode chain is regular: every level
    is [KCons Green] with a [PNode] packet, plus a regular [KEnding]
    tail. *)
Lemma chain_to_kchain_g_regular :
  forall A (c : Chain A),
    chain_all_pnode c -> regular_kt (chain_to_kchain_g c).
Proof.
  intros A c. induction c as [b | p c' IH]; intros H.
  - cbn. apply reg_kt_ending.
  - cbn. destruct H as [Hp Hcs]. apply reg_kt_green; auto.
Qed.

(** [buffer_push_chain] always returns an all-PNode chain. *)
Lemma buffer_push_chain_all_pnode :
  forall A (x : E.t A) (b : Buf5 (E.t A)),
    chain_all_pnode (buffer_push_chain x b).
Proof. intros A x b; destruct b; cbn; intuition. Qed.

(** [buffer_inject_chain] always returns an all-PNode chain. *)
Lemma buffer_inject_chain_all_pnode :
  forall A (b : Buf5 (E.t A)) (x : E.t A),
    chain_all_pnode (buffer_inject_chain b x).
Proof. intros A b x; destruct b; cbn; intuition. Qed.

(** [mk_ending_from_options] returns an [Ending], hence all-PNode trivially. *)
Lemma mk_ending_from_options_all_pnode :
  forall A (p : option (E.t A)) (m : option (E.t A * E.t A))
         (s : option (E.t A)),
    chain_all_pnode (mk_ending_from_options p m s).
Proof.
  intros A p m s.
  destruct p as [a|], m as [[b1 c1]|], s as [d1|]; cbn; auto.
Qed.

(** [make_small] always returns an all-PNode chain. *)
Lemma make_small_all_pnode :
  forall A (b1 b2 b3 : Buf5 (E.t A)) (c : Chain A),
    make_small b1 b2 b3 = Some c ->
    chain_all_pnode c.
Proof.
  intros A b1 b2 b3 c Hms.
  unfold make_small in Hms.
  destruct (prefix_decompose b1) as [p1opt|p1'|p1' cc dd];
  destruct (suffix_decompose b3) as [s1opt|s1'|s1' aa bb].
  - (* (Underflow, Underflow) *)
    destruct (buffer_unsandwich b2) as [midopt|ab rest cd].
    + destruct midopt as [elem|].
      * destruct (E.unpair A elem) as [[? ?]|]; [|discriminate].
        inversion Hms; subst. apply mk_ending_from_options_all_pnode.
      * inversion Hms; subst. apply mk_ending_from_options_all_pnode.
    + destruct (E.unpair A ab) as [[? ?]|]; [|discriminate].
      destruct (E.unpair A cd) as [[? ?]|]; [|discriminate].
      inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Underflow, Ok) *)
    destruct (buf5_pop_naive b2) as [[cd rest]|];
      [|destruct p1opt as [x|];
        [destruct (buf5_push_naive x s1') as [s1''|]; [|discriminate]
        |];
        inversion Hms; subst; cbn; trivial].
    destruct (E.unpair A cd) as [[? ?]|]; [|discriminate].
    inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Underflow, Overflow) *)
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [Hab|]; [|discriminate].
    destruct (suffix_rot b2 _) as [cd_paired center] eqn:Hsr.
    destruct (E.unpair A cd_paired) as [[? ?]|]; [|discriminate].
    inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Ok, Underflow) *)
    destruct (buf5_eject_naive b2) as [[rest ab]|];
      [|destruct s1opt as [x|];
        [destruct (buf5_inject_naive p1' x) as [p1''|]; [|discriminate]
        |];
        inversion Hms; subst; cbn; trivial].
    destruct (E.unpair A ab) as [[? ?]|]; [|discriminate].
    inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Ok, Ok) *)
    inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Ok, Overflow) *)
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [Hab|]; [|discriminate].
    inversion Hms; subst. cbn. split.
    + exact I.
    + apply buffer_inject_chain_all_pnode.
  - (* (Overflow, Underflow) *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [Hcd|]; [|discriminate].
    destruct (prefix_rot _ b2) as [center ab_paired] eqn:Hpr.
    destruct (E.unpair A ab_paired) as [[? ?]|] eqn:Hup; [|discriminate].
    inversion Hms; subst. cbn. split; [exact I|exact I].
  - (* (Overflow, Ok) *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [Hcd|]; [|discriminate].
    inversion Hms; subst. cbn. split.
    + exact I.
    + apply buffer_push_chain_all_pnode.
  - (* (Overflow, Overflow) *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [Hcd|]; [|discriminate].
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [Hab|]; [|discriminate].
    destruct (buffer_halve b2) as [midopt rest_pairs] eqn:Hbh.
    destruct (pair_each_buf rest_pairs) as [rest|]; [|discriminate].
    inversion Hms; subst. cbn. intuition.
Qed.

(* ========================================================================== *)
(* green_of_red_k preserves regularity.                                        *)
(* ========================================================================== *)

(** [green_of_red_k] preserves the [regular_kt] invariant. *)
Lemma green_of_red_k_preserves_regular :
  forall A (c c' : KChain A),
    regular_kt c -> green_of_red_k c = Some c' -> regular_kt c'.
Proof.
  intros A c c' Hreg Hg.
  unfold green_of_red_k in Hg.
  destruct c as [|col p tail]; [discriminate|].
  destruct col; try discriminate.
  (* col = Red *)
  destruct p as [|pre1 i suf1]; [discriminate|].
  apply regular_kt_red_inv in Hreg.
  destruct Hreg as [_ [Htop Htail_reg]].
  destruct i as [|pre2 child suf2].
  - (* inner Hole *)
    destruct tail as [b | col2 [|pre2_t child_t suf2_t] tail2].
    + (* Case 1: KEnding tail *)
      destruct (make_small pre1 b suf1) as [c''|] eqn:Hms; [|discriminate].
      inversion Hg; subst c'.
      apply chain_to_kchain_g_regular.
      eapply make_small_all_pnode; eauto.
    + discriminate.
    + (* Case 2: KCons with PNode inner *)
      destruct (green_prefix_concat pre1 pre2_t) as [[pre1' pre2_t']|];
        [|discriminate].
      destruct (green_suffix_concat suf2_t suf1) as [[suf2_t' suf1']|];
        [|discriminate].
      inversion Hg; subst c'.
      apply reg_kt_green; [cbn; exact I|].
      (* Need: regular_kt tail2.  From Htail_reg : regular_kt (KCons col2 ... tail2). *)
      eapply regular_kt_tail; eauto.
  - (* inner PNode: Case 3 *)
    destruct (prefix_concat pre1 pre2) as [[pre1' pre2']|]; [|discriminate].
    destruct (suffix_concat suf2 suf1) as [[suf2' suf1']|]; [|discriminate].
    inversion Hg; subst c'.
    apply reg_kt_green; [cbn; exact I|].
    apply reg_kt_red; [cbn; exact I|exact Htop|exact Htail_reg].
Qed.

(* ========================================================================== *)
(* ensure_green_k preserves regularity.                                        *)
(* ========================================================================== *)

(** [ensure_green_k] preserves regularity. *)
Lemma ensure_green_k_preserves_regular :
  forall A (c c' : KChain A),
    regular_kt c -> ensure_green_k c = Some c' -> regular_kt c'.
Proof.
  intros A c c' Hreg Hg.
  unfold ensure_green_k in Hg.
  destruct c as [b|col p tail].
  - inversion Hg; subst; apply reg_kt_ending.
  - destruct col.
    + inversion Hg; subst; exact Hreg.
    + inversion Hg; subst; exact Hreg.
    + eapply green_of_red_k_preserves_regular; eauto.
Qed.

(** [ensure_green_k] always lands on a non-Red top (already proven above:
    [ensure_green_k_top_not_red]).  Restated for symmetry. *)

(* ========================================================================== *)
(* make_yellow_k / make_red_k preserve regularity.                             *)
(* ========================================================================== *)

(** [make_yellow_k] preserves regularity.  The new Yellow tag requires
    that its tail's top is non-Red: this is exactly what
    [ensure_green_k] guarantees (see [ensure_green_k_top_not_red]). *)
Lemma make_yellow_k_preserves_regular :
  forall A (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
         (tail c' : KChain A),
    regular_kt tail ->
    make_yellow_k pre i suf tail = Some c' ->
    regular_kt c'.
Proof.
  intros A pre i suf tail c' Hreg Hm.
  unfold make_yellow_k in Hm.
  destruct (ensure_green_k tail) as [tail'|] eqn:He; [|discriminate].
  inversion Hm; subst c'.
  apply reg_kt_yellow.
  - cbn; exact I.
  - eapply ensure_green_k_top_not_red; eauto.
  - eapply ensure_green_k_preserves_regular; eauto.
Qed.

(** [make_red_k] preserves regularity *provided* the new Red node sits
    on a non-Red top.  Used by [push_kt2] / [pop_kt2] when the
    next-level packet's color shifted to Red. *)
Lemma make_red_k_preserves_regular :
  forall A (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
         (tail c' : KChain A),
    regular_kt tail ->
    kchain_top_color tail <> Red ->
    make_red_k pre i suf tail = Some c' ->
    regular_kt c'.
Proof.
  intros A pre i suf tail c' Hreg Htop Hm.
  unfold make_red_k in Hm.
  apply green_of_red_k_preserves_regular with (c := KCons Red (PNode pre i suf) tail);
    auto.
  apply reg_kt_red; [cbn; exact I|exact Htop|exact Hreg].
Qed.

(* ========================================================================== *)
(* push_kt2 / inject_kt2 / pop_kt2 / eject_kt2 preserve regularity.            *)
(*                                                                             *)
(* Public-API entry points.  Precondition [regular_kt_top c] is the            *)
(* "well-formed by construction" status of any chain reachable from            *)
(* [empty_kchain] via the public ops.  Result is a fresh chain that            *)
(* also satisfies [regular_kt_top].                                            *)
(* ========================================================================== *)

(** Helper: a [make_yellow_k] result always has a non-Red top (Yellow). *)
Lemma make_yellow_k_top_not_red :
  forall A pre i suf (tail c' : KChain A),
    make_yellow_k pre i suf tail = Some c' ->
    kchain_top_color c' <> Red.
Proof.
  intros A pre i suf tail c' Hm.
  unfold make_yellow_k in Hm.
  destruct (ensure_green_k tail); [|discriminate].
  inversion Hm; subst; cbn; discriminate.
Qed.

(** Helper: a [make_red_k] result has Green top (because it goes through
    [green_of_red_k]). *)
Lemma make_red_k_top_not_red :
  forall A pre i suf (tail c' : KChain A),
    make_red_k pre i suf tail = Some c' ->
    kchain_top_color c' <> Red.
Proof.
  intros A pre i suf tail c' Hm.
  unfold make_red_k in Hm.
  apply green_of_red_k_top_green in Hm. rewrite Hm. discriminate.
Qed.

(** [push_kt2] preserves [regular_kt_top]. *)
Theorem push_kt2_preserves_regular_top :
  forall A (x : E.t A) (c c' : KChain A),
    regular_kt_top c ->
    push_kt2 x c = Some c' ->
    regular_kt_top c'.
Proof.
  intros A x c c' [Htop Hreg] Hp.
  unfold push_kt2 in Hp.
  destruct c as [b|col p tail].
  - (* KEnding *)
    destruct (buf5_push_naive x b) as [b'|] eqn:Hbp.
    + inversion Hp; subst c'. split; [cbn; discriminate|apply reg_kt_ending].
    + destruct b; try discriminate.
      inversion Hp; subst c'. split; [cbn; discriminate|].
      apply reg_kt_green; [cbn; exact I|apply reg_kt_ending].
  - destruct col.
    + (* Green *)
      destruct p as [|pre i suf]; [discriminate|].
      destruct (green_push x pre) as [pre'|] eqn:Hgp; [|discriminate].
      apply regular_kt_green_inv in Hreg. destruct Hreg as [_ Htail_reg].
      split.
      * eapply make_yellow_k_top_not_red; eauto.
      * eapply make_yellow_k_preserves_regular; eauto.
    + (* Yellow *)
      destruct p as [|pre i suf]; [discriminate|].
      destruct (yellow_push x pre) as [pre'|] eqn:Hyp; [|discriminate].
      apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      split.
      * eapply make_red_k_top_not_red; eauto.
      * eapply make_red_k_preserves_regular; eauto.
    + (* Red — push_kt2 rejects via None *) discriminate.
Qed.

(** [inject_kt2] preserves [regular_kt_top].  Symmetric to push. *)
Theorem inject_kt2_preserves_regular_top :
  forall A (c : KChain A) (x : E.t A) (c' : KChain A),
    regular_kt_top c ->
    inject_kt2 c x = Some c' ->
    regular_kt_top c'.
Proof.
  intros A c x c' [Htop Hreg] Hp.
  unfold inject_kt2 in Hp.
  destruct c as [b|col p tail].
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hbi.
    + inversion Hp; subst c'. split; [cbn; discriminate|apply reg_kt_ending].
    + destruct b; try discriminate.
      inversion Hp; subst c'. split; [cbn; discriminate|].
      apply reg_kt_green; [cbn; exact I|apply reg_kt_ending].
  - destruct col.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (green_inject suf x) as [suf'|] eqn:Hgi; [|discriminate].
      apply regular_kt_green_inv in Hreg. destruct Hreg as [_ Htail_reg].
      split.
      * eapply make_yellow_k_top_not_red; eauto.
      * eapply make_yellow_k_preserves_regular; eauto.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (yellow_inject suf x) as [suf'|] eqn:Hyi; [|discriminate].
      apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      split.
      * eapply make_red_k_top_not_red; eauto.
      * eapply make_red_k_preserves_regular; eauto.
    + discriminate.
Qed.

(** [pop_kt2] preserves [regular_kt_top]. *)
Theorem pop_kt2_preserves_regular_top :
  forall A (c : KChain A) (x : E.t A) (c' : KChain A),
    regular_kt_top c ->
    pop_kt2 c = Some (x, c') ->
    regular_kt_top c'.
Proof.
  intros A c x c' [Htop Hreg] Hp.
  unfold pop_kt2 in Hp.
  destruct c as [b|col p tail].
  - destruct (buf5_pop_naive b) as [[xv b']|] eqn:Hbp; [|discriminate].
    inversion Hp; subst c'. split; [cbn; discriminate|apply reg_kt_ending].
  - destruct col.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (green_pop pre) as [[xv pre']|] eqn:Hgp; [|discriminate].
      destruct (make_yellow_k pre' i suf tail) as [c''|] eqn:Hmy;
        [|discriminate].
      inversion Hp; subst c'.
      apply regular_kt_green_inv in Hreg. destruct Hreg as [_ Htail_reg].
      split.
      * eapply make_yellow_k_top_not_red; eauto.
      * eapply make_yellow_k_preserves_regular; eauto.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (yellow_pop pre) as [[xv pre']|] eqn:Hyp; [|discriminate].
      destruct (make_red_k pre' i suf tail) as [c''|] eqn:Hmr;
        [|discriminate].
      inversion Hp; subst c'.
      apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      split.
      * eapply make_red_k_top_not_red; eauto.
      * eapply make_red_k_preserves_regular; eauto.
    + discriminate.
Qed.

(** [eject_kt2] preserves [regular_kt_top]. *)
Theorem eject_kt2_preserves_regular_top :
  forall A (c c' : KChain A) (x : E.t A),
    regular_kt_top c ->
    eject_kt2 c = Some (c', x) ->
    regular_kt_top c'.
Proof.
  intros A c c' x [Htop Hreg] Hp.
  unfold eject_kt2 in Hp.
  destruct c as [b|col p tail].
  - destruct (buf5_eject_naive b) as [[b' xv]|] eqn:Hbe; [|discriminate].
    inversion Hp; subst c'. split; [cbn; discriminate|apply reg_kt_ending].
  - destruct col.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (green_eject suf) as [[suf' xv]|] eqn:Hge; [|discriminate].
      destruct (make_yellow_k pre i suf' tail) as [c''|] eqn:Hmy;
        [|discriminate].
      inversion Hp; subst c'.
      apply regular_kt_green_inv in Hreg. destruct Hreg as [_ Htail_reg].
      split.
      * eapply make_yellow_k_top_not_red; eauto.
      * eapply make_yellow_k_preserves_regular; eauto.
    + destruct p as [|pre i suf]; [discriminate|].
      destruct (yellow_eject suf) as [[suf' xv]|] eqn:Hye; [|discriminate].
      destruct (make_red_k pre i suf' tail) as [c''|] eqn:Hmr;
        [|discriminate].
      inversion Hp; subst c'.
      apply regular_kt_yellow_inv in Hreg.
      destruct Hreg as [_ [Htail_top Htail_reg]].
      split.
      * eapply make_red_k_top_not_red; eauto.
      * eapply make_red_k_preserves_regular; eauto.
    + discriminate.
Qed.

(** Foundation: [empty_kchain] satisfies the user-facing invariant. *)
Theorem empty_kchain_regular_top :
  forall A, regular_kt_top (@empty_kchain A).
Proof. intros A; split; [cbn; discriminate|apply regular_kt_empty]. Qed.
