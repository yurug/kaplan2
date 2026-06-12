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

  Lemma map_prefix23 : forall o p,
      prefix23 (option_map f o) (fpair p) = fb (prefix23 o p).
  Proof. intros o [x y]; destruct o; reflexivity. Qed.

  Lemma map_suffix23 : forall p o,
      suffix23 (fpair p) (option_map f o) = fb (suffix23 p o).
  Proof. intros [x y] o; destruct o; reflexivity. Qed.

  Lemma map_suffix12 : forall x o,
      suffix12 (f x) (option_map f o) = fb (suffix12 x o).
  Proof. intros x o; destruct o; reflexivity. Qed.

End MapCommute.
