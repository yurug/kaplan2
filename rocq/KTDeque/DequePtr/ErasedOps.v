(** * KTDeque.DequePtr.ErasedOps — check-erased §4 operations.

    Phase 2026-06-12e (SESSION_STATE): mirrors of the sized kt4 ops
    over CHECK-FREE elements ([Common/ErasedTree.v]): every
    [Nat.eq_dec (E.level x) (E.level y)] + proof-carrying [E.pair]
    becomes an unchecked [EPair]; every [match E.unpair t] becomes a
    structural match.  Each mirror carries a SUCCESS-CONDITIONAL
    naturality lemma

        f args = Some r  ->  f_e (er args) = Some (er r)

    — where the original succeeds, the erased op computes the erasure
    of its result.  (On level-mismatch inputs the originals fail while
    the erased ops proceed; those inputs are unreachable from regular
    chains by the deque keystone, so the artifact's behaviour is
    pinned exactly where it is exercised.)

    Stage 1 (this section): element-generic chain structures (the
    original [Packet]/[Chain]/[KChain] hard-code [E.t A]; [GPacket]
    etc. generalize the element type so one definition serves both the
    tagged and the erased world), erasure maps, and the
    [buf5_map]-commutation toolkit for the polymorphic buffer
    shufflers. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color
  ErasedTree.
From KTDeque.DequePtr Require Import Model OpsKT SizedChain.

Set Implicit Arguments.

Module E := Model.E.

(* ========================================================================== *)
(* Element-generic chain structures.                                           *)
(* ========================================================================== *)

Inductive GPacket (X : Type) : Type :=
| GHole  : GPacket X
| GPNode : Buf5 X -> GPacket X -> Buf5 X -> GPacket X.
Arguments GHole {X}.
Arguments GPNode {X} _ _ _.

Inductive GChain (X : Type) : Type :=
| GEnding    : Buf5 X -> GChain X
| GChainCons : GPacket X -> GChain X -> GChain X.
Arguments GEnding {X} _.
Arguments GChainCons {X} _ _.

Inductive GKChain (X : Type) : Type :=
| GKEnding : Buf5 X -> GKChain X
| GKCons   : color -> GPacket X -> GKChain X -> GKChain X.
Arguments GKEnding {X} _.
Arguments GKCons   {X} _ _ _.

Inductive GSChain (X : Type) : Type :=
| GSEnding : nat -> Buf5 X -> GSChain X
| GSCons   : nat -> color -> GPacket X -> GKChain X -> GSChain X.
Arguments GSEnding {X} _ _.
Arguments GSCons   {X} _ _ _ _.

Inductive gpop_result (X : Type) : Type :=
| GPopFail : gpop_result X
| GPopOk   : X -> GSChain X -> gpop_result X.
Arguments GPopFail {X}.
Arguments GPopOk   {X} _ _.

(* ========================================================================== *)
(* Erasure maps.                                                               *)
(* ========================================================================== *)

Definition buf5_map {X Y : Type} (f : X -> Y) (b : Buf5 X) : Buf5 Y :=
  match b with
  | B0 => B0
  | B1 a => B1 (f a)
  | B2 a b1 => B2 (f a) (f b1)
  | B3 a b1 c => B3 (f a) (f b1) (f c)
  | B4 a b1 c d => B4 (f a) (f b1) (f c) (f d)
  | B5 a b1 c d e => B5 (f a) (f b1) (f c) (f d) (f e)
  end.

Definition er_buf {A : Type} (b : Buf5 (E.t A)) : Buf5 (etree A) :=
  buf5_map (@er A) b.

Fixpoint er_packet {A : Type} (p : Packet A) : GPacket (etree A) :=
  match p with
  | Hole => GHole
  | PNode pre i suf => GPNode (er_buf pre) (er_packet i) (er_buf suf)
  end.

Fixpoint er_chain {A : Type} (c : Chain A) : GChain (etree A) :=
  match c with
  | Ending b => GEnding (er_buf b)
  | ChainCons p c' => GChainCons (er_packet p) (er_chain c')
  end.

Fixpoint er_kchain {A : Type} (c : KChain A) : GKChain (etree A) :=
  match c with
  | KEnding b => GKEnding (er_buf b)
  | KCons col p c' => GKCons col (er_packet p) (er_kchain c')
  end.

Definition er_schain {A : Type} (c : SChain A) : GSChain (etree A) :=
  match c with
  | SEnding n b => GSEnding n (er_buf b)
  | SCons n col p t => GSCons n col (er_packet p) (er_kchain t)
  end.

(* ========================================================================== *)
(* buf5_map commutation toolkit (the polymorphic shufflers).                   *)
(* ========================================================================== *)

Section MapCommute.
  Variables (X Y : Type) (f : X -> Y).

  Let fb := buf5_map f.
  Let fpair := fun p : X * X => (f (fst p), f (snd p)).

  Lemma map_green_push : forall x b,
      green_push (f x) (fb b) = option_map fb (green_push x b).
  Proof. intros x b; destruct b; reflexivity. Qed.

  Lemma map_green_inject : forall b x,
      green_inject (fb b) (f x) = option_map fb (green_inject b x).
  Proof. intros b x; destruct b; reflexivity. Qed.

  Lemma map_yellow_push : forall x b,
      yellow_push (f x) (fb b) = option_map fb (yellow_push x b).
  Proof. intros x b; destruct b; reflexivity. Qed.

  Lemma map_yellow_inject : forall b x,
      yellow_inject (fb b) (f x) = option_map fb (yellow_inject b x).
  Proof. intros b x; destruct b; reflexivity. Qed.

  Lemma map_green_pop : forall b,
      green_pop (fb b)
      = option_map (fun '(x, b') => (f x, fb b')) (green_pop b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_green_eject : forall b,
      green_eject (fb b)
      = option_map (fun '(b', x) => (fb b', f x)) (green_eject b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_yellow_pop : forall b,
      yellow_pop (fb b)
      = option_map (fun '(x, b') => (f x, fb b')) (yellow_pop b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_yellow_eject : forall b,
      yellow_eject (fb b)
      = option_map (fun '(b', x) => (fb b', f x)) (yellow_eject b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_buf5_push_naive : forall x b,
      buf5_push_naive (f x) (fb b) = option_map fb (buf5_push_naive x b).
  Proof. intros x b; destruct b; reflexivity. Qed.

  Lemma map_buf5_inject_naive : forall b x,
      buf5_inject_naive (fb b) (f x) = option_map fb (buf5_inject_naive b x).
  Proof. intros b x; destruct b; reflexivity. Qed.

  Lemma map_buf5_pop_naive : forall b,
      buf5_pop_naive (fb b)
      = option_map (fun '(x, b') => (f x, fb b')) (buf5_pop_naive b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_buf5_eject_naive : forall b,
      buf5_eject_naive (fb b)
      = option_map (fun '(b', x) => (fb b', f x)) (buf5_eject_naive b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Definition bd_pre_map (d : bdecomp_pre X) : bdecomp_pre Y :=
    match d with
    | BD_pre_underflow o => BD_pre_underflow (option_map f o)
    | BD_pre_ok b => BD_pre_ok (fb b)
    | BD_pre_overflow b x y => BD_pre_overflow (fb b) (f x) (f y)
    end.

  Definition bd_suf_map (d : bdecomp_suf X) : bdecomp_suf Y :=
    match d with
    | BD_suf_underflow o => BD_suf_underflow (option_map f o)
    | BD_suf_ok b => BD_suf_ok (fb b)
    | BD_suf_overflow b x y => BD_suf_overflow (fb b) (f x) (f y)
    end.

  Lemma map_prefix_decompose : forall b,
      prefix_decompose (fb b) = bd_pre_map (prefix_decompose b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_suffix_decompose : forall b,
      suffix_decompose (fb b) = bd_suf_map (suffix_decompose b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Definition bs_map (s : bsandwich X) : bsandwich Y :=
    match s with
    | BS_alone o => BS_alone (option_map f o)
    | BS_sandwich x b y => BS_sandwich (f x) (fb b) (f y)
    end.

  Lemma map_buffer_unsandwich : forall b,
      buffer_unsandwich (fb b) = bs_map (buffer_unsandwich b).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_prefix_rot : forall x b,
      prefix_rot (f x) (fb b)
      = (fb (fst (prefix_rot x b)), f (snd (prefix_rot x b))).
  Proof. intros x b; destruct b; reflexivity. Qed.

  Lemma map_suffix_rot : forall b x,
      suffix_rot (fb b) (f x)
      = (f (fst (suffix_rot b x)), fb (snd (suffix_rot b x))).
  Proof. intros b x; destruct b; reflexivity. Qed.

  Lemma map_buffer_halve : forall b,
      buffer_halve (fb b)
      = (option_map f (fst (buffer_halve b)),
         buf5_map fpair (snd (buffer_halve b))).
  Proof. intros b; destruct b; reflexivity. Qed.

  Lemma map_prefix23 : forall o x y,
      prefix23 (option_map f o) (f x, f y) = fb (prefix23 o (x, y)).
  Proof. intros o x y; destruct o; reflexivity. Qed.

  Lemma map_suffix23 : forall x y o,
      suffix23 (f x, f y) (option_map f o) = fb (suffix23 (x, y) o).
  Proof. intros x y o; destruct o; reflexivity. Qed.

  Lemma map_suffix12 : forall x o,
      suffix12 (f x) (option_map f o) = fb (suffix12 x o).
  Proof. intros x o; destruct o; reflexivity. Qed.

End MapCommute.

(* ========================================================================== *)
(* Stage 2: the cross-buffer concat helpers, check-erased.                     *)
(* ========================================================================== *)

Definition green_prefix_concat_e {A : Type}
    (b1 b2 : Buf5 (etree A)) : option (Buf5 (etree A) * Buf5 (etree A)) :=
  match prefix_decompose b1 with
  | BD_pre_underflow opt =>
      match green_pop b2 with
      | Some (EPair a b, b2') => Some (prefix23 opt (a, b), b2')
      | _ => None
      end
  | BD_pre_ok b1' => Some (b1', b2)
  | BD_pre_overflow b1' c d =>
      match green_push (EPair c d) b2 with
      | Some b2' => Some (b1', b2')
      | None     => None
      end
  end.

Definition green_suffix_concat_e {A : Type}
    (b1 b2 : Buf5 (etree A)) : option (Buf5 (etree A) * Buf5 (etree A)) :=
  match suffix_decompose b2 with
  | BD_suf_underflow opt =>
      match green_eject b1 with
      | Some (b1', EPair a b) => Some (b1', suffix23 (a, b) opt)
      | _ => None
      end
  | BD_suf_ok b2' => Some (b1, b2')
  | BD_suf_overflow b2' a b =>
      match green_inject b1 (EPair a b) with
      | Some b1' => Some (b1', b2')
      | None     => None
      end
  end.

Definition prefix_concat_e {A : Type}
    (b1 b2 : Buf5 (etree A)) : option (Buf5 (etree A) * Buf5 (etree A)) :=
  match prefix_decompose b1 with
  | BD_pre_underflow opt =>
      match yellow_pop b2 with
      | Some (EPair a b, b2') => Some (prefix23 opt (a, b), b2')
      | _ => None
      end
  | BD_pre_ok b1' => Some (b1', b2)
  | BD_pre_overflow b1' c d =>
      match yellow_push (EPair c d) b2 with
      | Some b2' => Some (b1', b2')
      | None     => None
      end
  end.

Definition suffix_concat_e {A : Type}
    (b1 b2 : Buf5 (etree A)) : option (Buf5 (etree A) * Buf5 (etree A)) :=
  match suffix_decompose b2 with
  | BD_suf_underflow opt =>
      match yellow_eject b1 with
      | Some (b1', EPair a b) => Some (b1', suffix23 (a, b) opt)
      | _ => None
      end
  | BD_suf_ok b2' => Some (b1, b2')
  | BD_suf_overflow b2' a b =>
      match yellow_inject b1 (EPair a b) with
      | Some b1' => Some (b1', b2')
      | None     => None
      end
  end.

Lemma green_prefix_concat_nat : forall A (b1 b2 r1 r2 : Buf5 (E.t A)),
    green_prefix_concat b1 b2 = Some (r1, r2) ->
    green_prefix_concat_e (er_buf b1) (er_buf b2)
    = Some (er_buf r1, er_buf r2).
Proof.
  intros A b1 b2 r1 r2 H.
  unfold green_prefix_concat in H; unfold green_prefix_concat_e, er_buf.
  rewrite map_prefix_decompose.
  destruct (prefix_decompose b1) as [opt | b1' | b1' c d]; cbn [bd_pre_map].
  - rewrite map_green_pop.
    destruct (green_pop b2) as [[ab b2']|] eqn:Hp; cbn [option_map];
      [|discriminate].
    destruct (E.unpair A ab) as [[a b]|] eqn:Hu; [|discriminate].
    injection H as <- <-.
    rewrite (unpair_er Hu), (map_prefix23 (@er A) opt a b).
    reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct (Nat.eq_dec (E.level A c) (E.level A d)) as [e|];
      [|discriminate].
    destruct (green_push (E.pair A c d e) b2) as [b2'|] eqn:Hg;
      [|discriminate].
    injection H as <- <-.
    rewrite <- (er_pair e), map_green_push, Hg.
    reflexivity.
Qed.

Lemma green_suffix_concat_nat : forall A (b1 b2 r1 r2 : Buf5 (E.t A)),
    green_suffix_concat b1 b2 = Some (r1, r2) ->
    green_suffix_concat_e (er_buf b1) (er_buf b2)
    = Some (er_buf r1, er_buf r2).
Proof.
  intros A b1 b2 r1 r2 H.
  unfold green_suffix_concat in H; unfold green_suffix_concat_e, er_buf.
  rewrite map_suffix_decompose.
  destruct (suffix_decompose b2) as [opt | b2' | b2' a b]; cbn [bd_suf_map].
  - rewrite map_green_eject.
    destruct (green_eject b1) as [[b1' ab]|] eqn:Hp; cbn [option_map];
      [|discriminate].
    destruct (E.unpair A ab) as [[a b]|] eqn:Hu; [|discriminate].
    injection H as <- <-.
    rewrite (unpair_er Hu), (map_suffix23 (@er A) a b opt).
    reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [e|];
      [|discriminate].
    destruct (green_inject b1 (E.pair A a b e)) as [b1'|] eqn:Hg;
      [|discriminate].
    injection H as <- <-.
    rewrite <- (er_pair e), map_green_inject, Hg.
    reflexivity.
Qed.

Lemma prefix_concat_nat : forall A (b1 b2 r1 r2 : Buf5 (E.t A)),
    prefix_concat b1 b2 = Some (r1, r2) ->
    prefix_concat_e (er_buf b1) (er_buf b2) = Some (er_buf r1, er_buf r2).
Proof.
  intros A b1 b2 r1 r2 H.
  unfold prefix_concat in H; unfold prefix_concat_e, er_buf.
  rewrite map_prefix_decompose.
  destruct (prefix_decompose b1) as [opt | b1' | b1' c d]; cbn [bd_pre_map].
  - rewrite map_yellow_pop.
    destruct (yellow_pop b2) as [[ab b2']|] eqn:Hp; cbn [option_map];
      [|discriminate].
    destruct (E.unpair A ab) as [[a b]|] eqn:Hu; [|discriminate].
    injection H as <- <-.
    rewrite (unpair_er Hu), (map_prefix23 (@er A) opt a b).
    reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct (Nat.eq_dec (E.level A c) (E.level A d)) as [e|];
      [|discriminate].
    destruct (yellow_push (E.pair A c d e) b2) as [b2'|] eqn:Hg;
      [|discriminate].
    injection H as <- <-.
    rewrite <- (er_pair e), map_yellow_push, Hg.
    reflexivity.
Qed.

Lemma suffix_concat_nat : forall A (b1 b2 r1 r2 : Buf5 (E.t A)),
    suffix_concat b1 b2 = Some (r1, r2) ->
    suffix_concat_e (er_buf b1) (er_buf b2) = Some (er_buf r1, er_buf r2).
Proof.
  intros A b1 b2 r1 r2 H.
  unfold suffix_concat in H; unfold suffix_concat_e, er_buf.
  rewrite map_suffix_decompose.
  destruct (suffix_decompose b2) as [opt | b2' | b2' a b]; cbn [bd_suf_map].
  - rewrite map_yellow_eject.
    destruct (yellow_eject b1) as [[b1' ab]|] eqn:Hp; cbn [option_map];
      [|discriminate].
    destruct (E.unpair A ab) as [[a b]|] eqn:Hu; [|discriminate].
    injection H as <- <-.
    rewrite (unpair_er Hu), (map_suffix23 (@er A) a b opt).
    reflexivity.
  - injection H as <- <-. reflexivity.
  - destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [e|];
      [|discriminate].
    destruct (yellow_inject b1 (E.pair A a b e)) as [b1'|] eqn:Hg;
      [|discriminate].
    injection H as <- <-.
    rewrite <- (er_pair e), map_yellow_inject, Hg.
    reflexivity.
Qed.

(* ========================================================================== *)
(* Stage 3: make_small, check-erased.                                          *)
(* ========================================================================== *)

Definition er2 {A : Type} (p : E.t A * E.t A) : etree A * etree A :=
  (er (fst p), er (snd p)).

Definition gpair_one {A : Type} (p : etree A * etree A) : etree A :=
  EPair (fst p) (snd p).

Definition gpair_each {A : Type} (b : Buf5 (etree A * etree A))
    : Buf5 (etree A) := buf5_map (@gpair_one A) b.

Lemma pair_one_nat : forall A (p : E.t A * E.t A) (x : E.t A),
    pair_one p = Some x -> gpair_one (er2 p) = er x.
Proof.
  intros A [a b] x H.
  unfold pair_one in H.
  destruct (Nat.eq_dec (E.level A a) (E.level A b)) as [e|]; [|discriminate].
  injection H as <-.
  unfold gpair_one, er2; cbn [fst snd].
  rewrite (er_pair e). reflexivity.
Qed.

Lemma pair_each_buf_nat : forall A (b : Buf5 (E.t A * E.t A)) b',
    pair_each_buf b = Some b' ->
    gpair_each (buf5_map (@er2 A) b) = er_buf b'.
Proof.
  intros A b b' H.
  destruct b as [| p1 | p1 p2 | p1 p2 p3 | p1 p2 p3 p4 | p1 p2 p3 p4 p5];
    cbn in H;
    repeat
      match goal with
      | H : context [match pair_one ?p with _ => _ end] |- _ =>
          destruct (pair_one p) eqn:?; [|discriminate]
      end;
    injection H as <-;
    unfold gpair_each, er_buf; cbn [buf5_map];
    repeat
      match goal with
      | Hp : pair_one ?p = Some ?x |- _ =>
          rewrite <- (pair_one_nat Hp); clear Hp
      end;
    reflexivity.
Qed.

Definition gbuffer_push_chain {X : Type} (x : X) (b : Buf5 X) : GChain X :=
  match b with
  | B0           => GEnding (B1 x)
  | B1 a         => GEnding (B2 x a)
  | B2 a b1      => GEnding (B3 x a b1)
  | B3 a b1 c    => GEnding (B4 x a b1 c)
  | B4 a b1 c d  => GEnding (B5 x a b1 c d)
  | B5 a b1 c d e =>
      GChainCons (GPNode (B3 x a b1) GHole (B3 c d e)) (GEnding B0)
  end.

Definition gbuffer_inject_chain {X : Type} (b : Buf5 X) (x : X) : GChain X :=
  match b with
  | B0           => GEnding (B1 x)
  | B1 a         => GEnding (B2 a x)
  | B2 a b1      => GEnding (B3 a b1 x)
  | B3 a b1 c    => GEnding (B4 a b1 c x)
  | B4 a b1 c d  => GEnding (B5 a b1 c d x)
  | B5 a b1 c d e =>
      GChainCons (GPNode (B3 a b1 c) GHole (B3 d e x)) (GEnding B0)
  end.

Lemma er_buffer_push_chain : forall A (x : E.t A) b,
    er_chain (buffer_push_chain x b)
    = gbuffer_push_chain (er x) (er_buf b).
Proof. intros A x b; destruct b; reflexivity. Qed.

Lemma er_buffer_inject_chain : forall A b (x : E.t A),
    er_chain (buffer_inject_chain b x)
    = gbuffer_inject_chain (er_buf b) (er x).
Proof. intros A b x; destruct b; reflexivity. Qed.

Definition gmk_ending_from_options {X : Type}
    (p1 : option X) (mid : option (X * X)) (s1 : option X) : GChain X :=
  match p1, mid, s1 with
  | None,   None,        None      => GEnding B0
  | Some a, None,        None      => GEnding (B1 a)
  | None,   None,        Some a    => GEnding (B1 a)
  | Some a, None,        Some b    => GEnding (B2 a b)
  | None,   Some (a, b), None      => GEnding (B2 a b)
  | Some a, Some (b, c), None      => GEnding (B3 a b c)
  | None,   Some (a, b), Some c    => GEnding (B3 a b c)
  | Some a, Some (b, c), Some d    => GEnding (B4 a b c d)
  end.

Lemma er_mk_ending : forall A (p1 : option (E.t A)) mid s1,
    er_chain (mk_ending_from_options p1 mid s1)
    = gmk_ending_from_options (option_map (@er A) p1)
        (option_map (@er2 A) mid) (option_map (@er A) s1).
Proof.
  intros A [a|] [[b c]|] [d|]; reflexivity.
Qed.

Definition make_small_e {A : Type}
    (b1 b2 b3 : Buf5 (etree A)) : option (GChain (etree A)) :=
  match prefix_decompose b1, suffix_decompose b3 with
  | BD_pre_underflow p1opt, BD_suf_underflow s1opt =>
      match buffer_unsandwich b2 with
      | BS_alone midopt =>
          match midopt with
          | None => Some (gmk_ending_from_options p1opt None s1opt)
          | Some (EPair x y) =>
              Some (gmk_ending_from_options p1opt (Some (x, y)) s1opt)
          | Some (ELeaf _) => None
          end
      | BS_sandwich ab rest cd =>
          match ab, cd with
          | EPair ax ay, EPair cx cy =>
              Some (GChainCons
                      (GPNode (prefix23 p1opt (ax, ay)) GHole
                              (suffix23 (cx, cy) s1opt))
                      (GEnding rest))
          | _, _ => None
          end
      end
  | BD_pre_underflow p1opt, BD_suf_ok s1' =>
      match buf5_pop_naive b2, p1opt with
      | None, None   => Some (GEnding s1')
      | None, Some x =>
          match buf5_push_naive x s1' with
          | Some s1'' => Some (GEnding s1'')
          | None      => None
          end
      | Some (cd, rest), _ =>
          match cd with
          | EPair cx cy =>
              Some (GChainCons
                      (GPNode (prefix23 p1opt (cx, cy)) GHole s1')
                      (GEnding rest))
          | ELeaf _ => None
          end
      end
  | BD_pre_underflow p1opt, BD_suf_overflow s1' a b =>
      let '(cd, center) := suffix_rot b2 (EPair a b) in
      match cd with
      | EPair cx cy =>
          Some (GChainCons
                  (GPNode (prefix23 p1opt (cx, cy)) GHole s1')
                  (GEnding center))
      | ELeaf _ => None
      end
  | BD_pre_ok p1', BD_suf_underflow s1opt =>
      match buf5_eject_naive b2, s1opt with
      | None, None   => Some (GEnding p1')
      | None, Some x =>
          match buf5_inject_naive p1' x with
          | Some p1'' => Some (GEnding p1'')
          | None      => None
          end
      | Some (rest, ab), _ =>
          match ab with
          | EPair ax ay =>
              Some (GChainCons
                      (GPNode p1' GHole (suffix23 (ax, ay) s1opt))
                      (GEnding rest))
          | ELeaf _ => None
          end
      end
  | BD_pre_ok p1', BD_suf_ok s1' =>
      Some (GChainCons (GPNode p1' GHole s1') (GEnding b2))
  | BD_pre_ok p1', BD_suf_overflow s1' a b =>
      Some (GChainCons (GPNode p1' GHole s1')
              (gbuffer_inject_chain b2 (EPair a b)))
  | BD_pre_overflow p1' c d, BD_suf_underflow s1opt =>
      let '(center, ab) := prefix_rot (EPair c d) b2 in
      match ab with
      | EPair ax ay =>
          Some (GChainCons
                  (GPNode p1' GHole (suffix23 (ax, ay) s1opt))
                  (GEnding center))
      | ELeaf _ => None
      end
  | BD_pre_overflow p1' c d, BD_suf_ok s1' =>
      Some (GChainCons (GPNode p1' GHole s1')
              (gbuffer_push_chain (EPair c d) b2))
  | BD_pre_overflow p1' c d, BD_suf_overflow s1' a b =>
      let '(midopt, rest_pairs) := buffer_halve b2 in
      Some (GChainCons
              (GPNode p1' (GPNode (suffix12 (EPair c d) midopt) GHole
                                  (B1 (EPair a b))) s1')
              (GEnding (gpair_each rest_pairs)))
  end.

Lemma make_small_nat : forall A (b1 b2 b3 : Buf5 (E.t A)) c,
    make_small b1 b2 b3 = Some c ->
    make_small_e (er_buf b1) (er_buf b2) (er_buf b3) = Some (er_chain c).
Proof.
  intros A b1 b2 b3 c H.
  unfold make_small in H; unfold make_small_e.
  unfold er_buf.
  rewrite map_prefix_decompose, !map_suffix_decompose.
  destruct (prefix_decompose b1) as [p1opt | p1' | p1' cc dd];
    destruct (suffix_decompose b3) as [s1opt | s1' | s1' aa bb];
    cbn [bd_pre_map bd_suf_map].
  - (* U, U *)
    rewrite map_buffer_unsandwich.
    destruct (buffer_unsandwich b2) as [midopt | ab rest cd]; cbn [bs_map].
    + destruct midopt as [elem|]; cbn [option_map].
      * destruct (E.unpair A elem) as [[x y]|] eqn:Hu; [|discriminate].
        injection H as <-.
        rewrite (unpair_er Hu), er_mk_ending. reflexivity.
      * injection H as <-. rewrite er_mk_ending. reflexivity.
    + destruct (E.unpair A ab) as [[ax ay]|] eqn:Hua; [|discriminate].
      destruct (E.unpair A cd) as [[cx cy]|] eqn:Huc; [|discriminate].
      injection H as <-.
      rewrite (unpair_er Hua), (unpair_er Huc).
      destruct p1opt; destruct s1opt; reflexivity.
  - (* U, Ok *)
    rewrite map_buf5_pop_naive.
    destruct (buf5_pop_naive b2) as [[cd rest]|] eqn:Hp; cbn [option_map].
    + destruct (E.unpair A cd) as [[cx cy]|] eqn:Hu; [|discriminate].
      injection H as <-.
      rewrite (unpair_er Hu).
      destruct p1opt; reflexivity.
    + destruct p1opt as [x|]; cbn [option_map].
      * rewrite map_buf5_push_naive.
        destruct (buf5_push_naive x s1') as [s1''|] eqn:Hpu;
          cbn [option_map]; [|discriminate].
        injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
  - (* U, Overflow *)
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [e|];
      [|discriminate].
    destruct (suffix_rot b2 (E.pair A aa bb e)) as [cd center] eqn:Hrot.
    rewrite <- (er_pair e), map_suffix_rot, Hrot.
    cbn [fst snd].
    destruct (E.unpair A cd) as [[cx cy]|] eqn:Hu; [|discriminate].
    injection H as <-.
    rewrite (unpair_er Hu).
    destruct p1opt; reflexivity.
  - (* Ok, U *)
    rewrite map_buf5_eject_naive.
    destruct (buf5_eject_naive b2) as [[rest ab]|] eqn:Hp; cbn [option_map].
    + destruct (E.unpair A ab) as [[ax ay]|] eqn:Hu; [|discriminate].
      injection H as <-.
      rewrite (unpair_er Hu).
      destruct s1opt; reflexivity.
    + destruct s1opt as [x|]; cbn [option_map].
      * rewrite map_buf5_inject_naive.
        destruct (buf5_inject_naive p1' x) as [p1''|] eqn:Hpu;
          cbn [option_map]; [|discriminate].
        injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
  - (* Ok, Ok *)
    injection H as <-. reflexivity.
  - (* Ok, Overflow *)
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [e|];
      [|discriminate].
    injection H as <-.
    cbn [er_chain er_packet].
    rewrite <- (er_pair e), er_buffer_inject_chain.
    reflexivity.
  - (* Overflow, U *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [e|];
      [|discriminate].
    destruct (prefix_rot (E.pair A cc dd e) b2) as [center ab] eqn:Hrot.
    rewrite <- (er_pair e), map_prefix_rot, Hrot.
    cbn [fst snd].
    destruct (E.unpair A ab) as [[ax ay]|] eqn:Hu; [|discriminate].
    injection H as <-.
    rewrite (unpair_er Hu).
    destruct s1opt; reflexivity.
  - (* Overflow, Ok *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [e|];
      [|discriminate].
    injection H as <-.
    cbn [er_chain er_packet].
    rewrite <- (er_pair e), er_buffer_push_chain.
    reflexivity.
  - (* Overflow, Overflow *)
    destruct (Nat.eq_dec (E.level A cc) (E.level A dd)) as [ecd|];
      [|discriminate].
    destruct (Nat.eq_dec (E.level A aa) (E.level A bb)) as [eab|];
      [|discriminate].
    destruct (buffer_halve b2) as [midopt rest_pairs] eqn:Hh.
    rewrite <- (er_pair ecd), <- (er_pair eab),
      map_buffer_halve, Hh.
    cbn [fst snd].
    destruct (pair_each_buf rest_pairs) as [rest|] eqn:Hpe; [|discriminate].
    injection H as <-.
    pose proof (pair_each_buf_nat Hpe) as HPE.
    unfold er2 in HPE.
    cbn [er_chain er_packet].
    rewrite HPE.
    destruct midopt; reflexivity.
Qed.

(* ========================================================================== *)
(* Stage 4: green_of_red_k + the sized operations, check-erased.               *)
(* ========================================================================== *)

Fixpoint gchain_to_gkchain_g {X : Type} (c : GChain X) : GKChain X :=
  match c with
  | GEnding b => GKEnding b
  | GChainCons p c' => GKCons Green p (gchain_to_gkchain_g c')
  end.

Lemma er_chain_to_kchain_g : forall A (c : Chain A),
    er_kchain (chain_to_kchain_g c) = gchain_to_gkchain_g (er_chain c).
Proof.
  intros A c; induction c as [b | p c' IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Definition green_of_red_k_e {A : Type} (c : GKChain (etree A))
    : option (GKChain (etree A)) :=
  match c with
  | GKCons Red (GPNode pre1 GHole suf1) (GKEnding b) =>
      match make_small_e pre1 b suf1 with
      | Some c'' => Some (gchain_to_gkchain_g c'')
      | None     => None
      end
  | GKCons Red (GPNode pre1 GHole suf1)
               (GKCons _ (GPNode pre2 child suf2) c2) =>
      match green_prefix_concat_e pre1 pre2,
            green_suffix_concat_e suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          Some (GKCons Green
                       (GPNode pre1' (GPNode pre2' child suf2') suf1')
                       c2)
      | _, _ => None
      end
  | GKCons Red (GPNode pre1 (GPNode pre2 child suf2) suf1) c1 =>
      match prefix_concat_e pre1 pre2, suffix_concat_e suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          Some (GKCons Green (GPNode pre1' GHole suf1')
                             (GKCons Red (GPNode pre2' child suf2') c1))
      | _, _ => None
      end
  | _ => None
  end.

Lemma green_of_red_k_nat : forall A (c r : KChain A),
    green_of_red_k c = Some r ->
    green_of_red_k_e (er_kchain c) = Some (er_kchain r).
Proof.
  intros A c r H.
  unfold green_of_red_k in H; unfold green_of_red_k_e.
  destruct c as [b | col p t]; [discriminate|].
  destruct col; try discriminate.
  destruct p as [| pre1 i suf1]; [discriminate|].
  destruct i as [| pre2 child suf2].
  - (* Hole inner *)
    destruct t as [b | col2 p2 t2].
    + (* Case 1 *)
      destruct (make_small pre1 b suf1) as [c''|] eqn:Hm; [|discriminate].
      injection H as <-.
      cbn [er_kchain er_packet].
      rewrite (make_small_nat Hm), er_chain_to_kchain_g.
      reflexivity.
    + (* Case 2 *)
      destruct p2 as [| pre2 child suf2]; [discriminate|].
      destruct (green_prefix_concat pre1 pre2) as [[pre1' pre2']|] eqn:H1;
        [|discriminate].
      destruct (green_suffix_concat suf2 suf1) as [[suf2' suf1']|] eqn:H2;
        [|discriminate].
      injection H as <-.
      cbn [er_kchain er_packet].
      rewrite (green_prefix_concat_nat H1), (green_suffix_concat_nat H2).
      reflexivity.
  - (* PNode inner: Case 3 *)
    destruct (prefix_concat pre1 pre2) as [[pre1' pre2']|] eqn:H1;
      [|discriminate].
    destruct (suffix_concat suf2 suf1) as [[suf2' suf1']|] eqn:H2;
      [|discriminate].
    injection H as <-.
    cbn [er_kchain er_packet].
    rewrite (prefix_concat_nat H1), (suffix_concat_nat H2).
    reflexivity.
Qed.

Definition gs_of {X : Type} (n : nat) (c : GKChain X) : GSChain X :=
  match c with
  | GKEnding b => GSEnding n b
  | GKCons col p t => GSCons n col p t
  end.

Definition eyellow_wrap {A : Type} (fb : GSChain (etree A)) (n' : nat)
    (pre : Buf5 (etree A)) (i : GPacket (etree A)) (suf : Buf5 (etree A))
    (t : GKChain (etree A)) : GSChain (etree A) :=
  match t with
  | GKCons Red _ _ =>
      match green_of_red_k_e t with
      | Some t' => GSCons n' Yellow (GPNode pre i suf) t'
      | None    => fb
      end
  | _ => GSCons n' Yellow (GPNode pre i suf) t
  end.

Definition epush_s {A : Type} (x : etree A) (c : GSChain (etree A))
    : GSChain (etree A) :=
  match c with
  | GSEnding n b =>
      match b with
      | B0           => GSEnding (S n) (B1 x)
      | B1 a         => GSEnding (S n) (B2 x a)
      | B2 a b1      => GSEnding (S n) (B3 x a b1)
      | B3 a b1 c1   => GSEnding (S n) (B4 x a b1 c1)
      | B4 a b1 c1 d => GSEnding (S n) (B5 x a b1 c1 d)
      | B5 a b1 c1 d e =>
          GSCons (S n) Green (GPNode (B3 x a b1) GHole (B3 c1 d e))
            (GKEnding B0)
      end
  | GSCons n col p t =>
      match col, p with
      | Green, GPNode pre i suf =>
          match pre with
          | B2 a b1    => eyellow_wrap c (S n) (B3 x a b1) i suf t
          | B3 a b1 c1 => eyellow_wrap c (S n) (B4 x a b1 c1) i suf t
          | _          => c
          end
      | Yellow, GPNode pre i suf =>
          match pre with
          | B1 a         => GSCons (S n) Yellow (GPNode (B2 x a) i suf) t
          | B2 a b1      => GSCons (S n) Yellow (GPNode (B3 x a b1) i suf) t
          | B3 a b1 c1   =>
              GSCons (S n) Yellow (GPNode (B4 x a b1 c1) i suf) t
          | B4 a b1 c1 d =>
              match green_of_red_k_e
                      (GKCons Red (GPNode (B5 x a b1 c1 d) i suf) t) with
              | Some d' => gs_of (S n) d'
              | None    => c
              end
          | _ => c
          end
      | _, _ => c
      end
  end.

Lemma epush_s_nat : forall A (x : E.t A) (c : SChain A) (d : KChain A),
    push_kt4 x (s_erase c) = PushOk d ->
    epush_s (er x) (er_schain c) = gs_of (S (s_size c)) (er_kchain d).
Proof.
  intros A x c d H.
  destruct c as [n b | n col p t].
  - destruct b; cbn in H; injection H as <-; reflexivity.
  - destruct col.
    + (* Green *)
      destruct p as [| pre i suf]; [discriminate|].
      destruct pre; try discriminate;
        cbn in H; unfold yellow_wrap_pr in H;
        cbn [er_schain er_packet er_buf buf5_map epush_s];
        unfold eyellow_wrap;
        (destruct t as [b' | col' p' t']; cbn [er_kchain];
         [injection H as <-; reflexivity|];
         destruct col';
         try (injection H as <-; reflexivity);
         destruct (green_of_red_k (KCons Red p' t')) as [k|] eqn:Hg;
         [|discriminate];
         injection H as <-;
         pose proof (green_of_red_k_nat Hg) as HG;
         cbn [er_kchain er_packet] in HG; rewrite HG;
         reflexivity).
    + (* Yellow *)
      destruct p as [| pre i suf]; [discriminate|].
      destruct pre as [| a | a b1 | a b1 c1 | a b1 c1 d0 |];
        cbn [s_erase push_kt4] in H; try discriminate;
        cbn [er_schain er_packet er_buf buf5_map epush_s].
      * injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
      * destruct (green_of_red_k
            (KCons Red (PNode (B5 x a b1 c1 d0) i suf) t))
          as [k|] eqn:Hg; [|discriminate].
        injection H as <-.
        pose proof (green_of_red_k_nat Hg) as HG.
        cbn [er_kchain er_packet er_buf buf5_map] in HG. rewrite HG.
        destruct k as [kb | kc kp kt]; reflexivity.
    + (* Red *)
      destruct p; discriminate.
Qed.

Definition einject_s {A : Type} (c : GSChain (etree A)) (x : etree A)
    : GSChain (etree A) :=
  match c with
  | GSEnding n b =>
      match b with
      | B0           => GSEnding (S n) (B1 x)
      | B1 a         => GSEnding (S n) (B2 a x)
      | B2 a b1      => GSEnding (S n) (B3 a b1 x)
      | B3 a b1 c1   => GSEnding (S n) (B4 a b1 c1 x)
      | B4 a b1 c1 d => GSEnding (S n) (B5 a b1 c1 d x)
      | B5 a b1 c1 d e =>
          GSCons (S n) Green (GPNode (B3 a b1 c1) GHole (B3 d e x))
            (GKEnding B0)
      end
  | GSCons n col p t =>
      match col, p with
      | Green, GPNode pre i suf =>
          match suf with
          | B2 a b1    => eyellow_wrap c (S n) pre i (B3 a b1 x) t
          | B3 a b1 c1 => eyellow_wrap c (S n) pre i (B4 a b1 c1 x) t
          | _          => c
          end
      | Yellow, GPNode pre i suf =>
          match suf with
          | B1 a         => GSCons (S n) Yellow (GPNode pre i (B2 a x)) t
          | B2 a b1      => GSCons (S n) Yellow (GPNode pre i (B3 a b1 x)) t
          | B3 a b1 c1   =>
              GSCons (S n) Yellow (GPNode pre i (B4 a b1 c1 x)) t
          | B4 a b1 c1 d =>
              match green_of_red_k_e
                      (GKCons Red (GPNode pre i (B5 a b1 c1 d x)) t) with
              | Some d' => gs_of (S n) d'
              | None    => c
              end
          | _ => c
          end
      | _, _ => c
      end
  end.

Lemma einject_s_nat : forall A (c : SChain A) (x : E.t A) (d : KChain A),
    inject_kt4 (s_erase c) x = PushOk d ->
    einject_s (er_schain c) (er x) = gs_of (S (s_size c)) (er_kchain d).
Proof.
  intros A c x d H.
  destruct c as [n b | n col p t].
  - destruct b; cbn in H; injection H as <-; reflexivity.
  - destruct col.
    + destruct p as [| pre i suf]; [discriminate|].
      destruct suf; try discriminate;
        cbn in H; unfold yellow_wrap_pr in H;
        cbn [er_schain er_packet er_buf buf5_map einject_s];
        unfold eyellow_wrap;
        (destruct t as [b' | col' p' t']; cbn [er_kchain];
         [injection H as <-; reflexivity|];
         destruct col';
         try (injection H as <-; reflexivity);
         destruct (green_of_red_k (KCons Red p' t')) as [k|] eqn:Hg;
         [|discriminate];
         injection H as <-;
         pose proof (green_of_red_k_nat Hg) as HG;
         cbn [er_kchain er_packet] in HG; rewrite HG;
         reflexivity).
    + destruct p as [| pre i suf]; [discriminate|].
      destruct suf as [| a | a b1 | a b1 c1 | a b1 c1 d0 |];
        cbn [s_erase inject_kt4] in H; try discriminate;
        cbn [er_schain er_packet er_buf buf5_map einject_s].
      * injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
      * injection H as <-. reflexivity.
      * destruct (green_of_red_k
            (KCons Red (PNode pre i (B5 a b1 c1 d0 x)) t))
          as [k|] eqn:Hg; [|discriminate].
        injection H as <-.
        pose proof (green_of_red_k_nat Hg) as HG.
        cbn [er_kchain er_packet er_buf buf5_map] in HG. rewrite HG.
        destruct k as [kb | kc kp kt]; reflexivity.
    + destruct p; discriminate.
Qed.

Definition epop_s {A : Type} (c : GSChain (etree A))
    : gpop_result (etree A) :=
  match c with
  | GSEnding n b =>
      match b with
      | B0           => GPopFail
      | B1 a         => GPopOk a (GSEnding (Nat.pred n) B0)
      | B2 a b1      => GPopOk a (GSEnding (Nat.pred n) (B1 b1))
      | B3 a b1 c1   => GPopOk a (GSEnding (Nat.pred n) (B2 b1 c1))
      | B4 a b1 c1 d => GPopOk a (GSEnding (Nat.pred n) (B3 b1 c1 d))
      | B5 a b1 c1 d e => GPopOk a (GSEnding (Nat.pred n) (B4 b1 c1 d e))
      end
  | GSCons n col p t =>
      match col, p with
      | Green, GPNode pre i suf =>
          match pre with
          | B2 a b1 =>
              match t with
              | GKCons Red _ _ =>
                  match green_of_red_k_e t with
                  | Some t' =>
                      GPopOk a
                        (GSCons (Nat.pred n) Yellow
                                (GPNode (B1 b1) i suf) t')
                  | None => GPopFail
                  end
              | _ =>
                  GPopOk a
                    (GSCons (Nat.pred n) Yellow (GPNode (B1 b1) i suf) t)
              end
          | B3 a b1 c1 =>
              match t with
              | GKCons Red _ _ =>
                  match green_of_red_k_e t with
                  | Some t' =>
                      GPopOk a
                        (GSCons (Nat.pred n) Yellow
                                (GPNode (B2 b1 c1) i suf) t')
                  | None => GPopFail
                  end
              | _ =>
                  GPopOk a
                    (GSCons (Nat.pred n) Yellow (GPNode (B2 b1 c1) i suf) t)
              end
          | _ => GPopFail
          end
      | Yellow, GPNode pre i suf =>
          match pre with
          | B1 a =>
              match green_of_red_k_e (GKCons Red (GPNode B0 i suf) t) with
              | Some d' => GPopOk a (gs_of (Nat.pred n) d')
              | None    => GPopFail
              end
          | B2 a b1 =>
              GPopOk a (GSCons (Nat.pred n) Yellow (GPNode (B1 b1) i suf) t)
          | B3 a b1 c1 =>
              GPopOk a
                (GSCons (Nat.pred n) Yellow (GPNode (B2 b1 c1) i suf) t)
          | B4 a b1 c1 d =>
              GPopOk a
                (GSCons (Nat.pred n) Yellow (GPNode (B3 b1 c1 d) i suf) t)
          | _ => GPopFail
          end
      | _, _ => GPopFail
      end
  end.

Lemma epop_s_nat : forall A (c : SChain A) (x : E.t A) (d : KChain A),
    pop_kt4 (s_erase c) = PopOk x d ->
    epop_s (er_schain c)
    = GPopOk (er x) (gs_of (Nat.pred (s_size c)) (er_kchain d)).
Proof.
  intros A c x d H.
  destruct c as [n b | n col p t].
  - destruct b; cbn in H; [discriminate|injection H as <- <-; reflexivity..].
  - destruct col.
    + (* Green *)
      destruct p as [| pre i suf]; [discriminate|].
      destruct pre; try discriminate;
        cbn [s_erase pop_kt4] in H; unfold yellow_wrap_pr in H;
        cbn [er_schain er_packet er_buf buf5_map epop_s];
        (destruct t as [b' | col' p' t']; cbn [er_kchain];
         [injection H as <- <-; reflexivity|];
         destruct col';
         try (injection H as <- <-; reflexivity);
         destruct (green_of_red_k (KCons Red p' t')) as [k|] eqn:Hg;
         [|discriminate];
         injection H as <- <-;
         pose proof (green_of_red_k_nat Hg) as HG;
         cbn [er_kchain er_packet] in HG; rewrite HG;
         reflexivity).
    + (* Yellow *)
      destruct p as [| pre i suf]; [discriminate|].
      destruct pre as [| a | a b1 | a b1 c1 | a b1 c1 d0 |];
        cbn [s_erase pop_kt4] in H; try discriminate;
        cbn [er_schain er_packet er_buf buf5_map epop_s].
      * destruct (green_of_red_k (KCons Red (PNode B0 i suf) t))
          as [k|] eqn:Hg; [|discriminate].
        injection H as <- <-.
        pose proof (green_of_red_k_nat Hg) as HG.
        cbn [er_kchain er_packet er_buf buf5_map] in HG. rewrite HG.
        destruct k as [kb | kc kp kt]; reflexivity.
      * injection H as <- <-. reflexivity.
      * injection H as <- <-. reflexivity.
      * injection H as <- <-. reflexivity.
    + destruct p; discriminate.
Qed.

Definition eeject_s {A : Type} (c : GSChain (etree A))
    : gpop_result (etree A) :=
  match c with
  | GSEnding n b =>
      match b with
      | B0           => GPopFail
      | B1 a         => GPopOk a (GSEnding (Nat.pred n) B0)
      | B2 a b1      => GPopOk b1 (GSEnding (Nat.pred n) (B1 a))
      | B3 a b1 c1   => GPopOk c1 (GSEnding (Nat.pred n) (B2 a b1))
      | B4 a b1 c1 d => GPopOk d (GSEnding (Nat.pred n) (B3 a b1 c1))
      | B5 a b1 c1 d e => GPopOk e (GSEnding (Nat.pred n) (B4 a b1 c1 d))
      end
  | GSCons n col p t =>
      match col, p with
      | Green, GPNode pre i suf =>
          match suf with
          | B2 a b1 =>
              match t with
              | GKCons Red _ _ =>
                  match green_of_red_k_e t with
                  | Some t' =>
                      GPopOk b1
                        (GSCons (Nat.pred n) Yellow
                                (GPNode pre i (B1 a)) t')
                  | None => GPopFail
                  end
              | _ =>
                  GPopOk b1
                    (GSCons (Nat.pred n) Yellow (GPNode pre i (B1 a)) t)
              end
          | B3 a b1 c1 =>
              match t with
              | GKCons Red _ _ =>
                  match green_of_red_k_e t with
                  | Some t' =>
                      GPopOk c1
                        (GSCons (Nat.pred n) Yellow
                                (GPNode pre i (B2 a b1)) t')
                  | None => GPopFail
                  end
              | _ =>
                  GPopOk c1
                    (GSCons (Nat.pred n) Yellow (GPNode pre i (B2 a b1)) t)
              end
          | _ => GPopFail
          end
      | Yellow, GPNode pre i suf =>
          match suf with
          | B1 a =>
              match green_of_red_k_e (GKCons Red (GPNode pre i B0) t) with
              | Some d' => GPopOk a (gs_of (Nat.pred n) d')
              | None    => GPopFail
              end
          | B2 a b1 =>
              GPopOk b1 (GSCons (Nat.pred n) Yellow (GPNode pre i (B1 a)) t)
          | B3 a b1 c1 =>
              GPopOk c1
                (GSCons (Nat.pred n) Yellow (GPNode pre i (B2 a b1)) t)
          | B4 a b1 c1 d =>
              GPopOk d
                (GSCons (Nat.pred n) Yellow (GPNode pre i (B3 a b1 c1)) t)
          | _ => GPopFail
          end
      | _, _ => GPopFail
      end
  end.

Lemma eeject_s_nat : forall A (c : SChain A) (x : E.t A) (d : KChain A),
    eject_kt4 (s_erase c) = PopOk x d ->
    eeject_s (er_schain c)
    = GPopOk (er x) (gs_of (Nat.pred (s_size c)) (er_kchain d)).
Proof.
  intros A c x d H.
  destruct c as [n b | n col p t].
  - destruct b; cbn in H; [discriminate|injection H as <- <-; reflexivity..].
  - destruct col.
    + destruct p as [| pre i suf]; [discriminate|].
      destruct suf; try discriminate;
        cbn [s_erase eject_kt4] in H; unfold yellow_wrap_pr in H;
        cbn [er_schain er_packet er_buf buf5_map eeject_s];
        (destruct t as [b' | col' p' t']; cbn [er_kchain];
         [injection H as <- <-; reflexivity|];
         destruct col';
         try (injection H as <- <-; reflexivity);
         destruct (green_of_red_k (KCons Red p' t')) as [k|] eqn:Hg;
         [|discriminate];
         injection H as <- <-;
         pose proof (green_of_red_k_nat Hg) as HG;
         cbn [er_kchain er_packet] in HG; rewrite HG;
         reflexivity).
    + destruct p as [| pre i suf]; [discriminate|].
      destruct suf as [| a | a b1 | a b1 c1 | a b1 c1 d0 |];
        cbn [s_erase eject_kt4] in H; try discriminate;
        cbn [er_schain er_packet er_buf buf5_map eeject_s].
      * destruct (green_of_red_k (KCons Red (PNode pre i B0) t))
          as [k|] eqn:Hg; [|discriminate].
        injection H as <- <-.
        pose proof (green_of_red_k_nat Hg) as HG.
        cbn [er_kchain er_packet er_buf buf5_map] in HG. rewrite HG.
        destruct k as [kb | kc kp kt]; reflexivity.
      * injection H as <- <-. reflexivity.
      * injection H as <- <-. reflexivity.
      * injection H as <- <-. reflexivity.
    + destruct p; discriminate.
Qed.
