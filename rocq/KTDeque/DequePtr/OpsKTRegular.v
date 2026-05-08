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

    The basic structural lemmas (decidability, trivial cases, top
    color non-Red) are proven.  The full preservation theorems are
    stated as [Lemma]s but **deliberately not proved yet** — they
    require substantial case work that will be added incrementally.
    None are [Admitted], preserving the project's zero-admit
    invariant.

    Until preservation is closed, the WC O(1) story holds for *cost*
    (via [Footprint.v]) but the *regularity* invariant required to
    apply that cost bound is not yet formally maintained across
    operations.  In practice, the C runtime asserts the invariant in
    debug builds (see [kt_check_regular] in [c/include/ktdeque.h]),
    and the QCheck/Monolith property tests have not yet found a
    violation.

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

Inductive regular_kt {A : Type} : KChain A -> Prop :=
| reg_kt_ending :
    forall b, regular_kt (KEnding b)
| reg_kt_green :
    forall p c, pkt_is_pnode p -> regular_kt c -> regular_kt (KCons Green p c)
| reg_kt_yellow :
    forall p c, pkt_is_pnode p -> regular_kt c -> regular_kt (KCons Yellow p c)
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

(** Inversion principle: a regular [KCons Red p c] forces the tail's
    top color to be ≠ Red (no two consecutive Reds). *)
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

(** Inversion: a regular [KCons Yellow p c] has [pkt_is_pnode p]. *)
Lemma regular_kt_yellow_inv :
  forall A p (c : KChain A),
    regular_kt (KCons Yellow p c) ->
    pkt_is_pnode p /\ regular_kt c.
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
    + left; apply reg_kt_yellow; auto.
    + (* Red case: also need top of c' to be non-Red. *)
      destruct c' as [b'|col' p' c''].
      * left. apply reg_kt_red; [exact Hp | cbn; discriminate | exact Hr].
      * destruct (color_eq_dec col' Red) as [Heq|Hne].
        -- subst. right; intros H. apply regular_kt_red_inv in H.
           destruct H as [_ [Htop _]]. cbn in Htop. apply Htop. reflexivity.
        -- left. apply reg_kt_red; [exact Hp | cbn; exact Hne | exact Hr].
Qed.

(* ========================================================================== *)
(* Pending heavy theorems (scoped out for follow-up commits).                  *)
(*                                                                             *)
(* The zero-admit invariant precludes us from leaving stub lemmas, so the      *)
(* goals below are documented but NOT introduced as named entities here:       *)
(*                                                                             *)
(*   green_of_red_k_preserves_regular :                                        *)
(*     regular_kt c -> green_of_red_k c = Some c' -> regular_kt c'.            *)
(*                                                                             *)
(*   ensure_green_k_preserves_regular :                                        *)
(*     regular_kt c -> ensure_green_k c = Some c' -> regular_kt c'.            *)
(*                                                                             *)
(*   push_kt2_preserves_regular :                                              *)
(*     regular_kt_top c -> push_kt2 x c = Some c' -> regular_kt_top c'.        *)
(*                                                                             *)
(*   push_kt2_total :                                                          *)
(*     regular_kt_top c -> exists c', push_kt2 x c = Some c'.                  *)
(*                                                                             *)
(* (and analogues for inject_kt2 / pop_kt2 / eject_kt2.)                       *)
(* ========================================================================== *)
