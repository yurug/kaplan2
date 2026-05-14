(** * Module: KTDeque.Cadeque7.PushInject — push / inject on KCadeque.

    Phase 2 of the [Cadeque7] development.  Implements the two
    "growing" public operations:

    - [kcad_push  : X -> KCadeque X -> KCadeque X]
    - [kcad_inject : KCadeque X -> X -> KCadeque X]

    with sequence-correctness theorems.

    ## What this version is and isn't

    This is the *naive* push/inject: it prepends to the outermost
    prefix buffer (push) or appends to the outermost suffix buffer
    (inject).  Buffers grow without bound — there's no overflow
    cascade yet.

    The WC O(1) bound requires:
    1. Buffer size discipline (Buf6 sizes 5/6/7 → Red/Orange/Yellow,
       8+ → Green) — Phase 3 will add the cascade.
    2. Color discipline preservation via the [RegularityTag] —
       Phase 3 will track this through [ensure_green].

    For now, this gives functionally-correct push/inject that
    preserves [kcad_to_list] semantics, even though it lets
    buffers grow without bound on long runs.

    ## Node-shape dispatch

    Mirrors Viennot's [push_only_packet] / [inject_only_packet] etc.:
    push targets the outermost node (the body's head if the body is
    non-Hole, otherwise the tail).  Inject targets the same outermost
    node, but the suffix buffer rather than the prefix.

    For [KPair l r], push descends into [l]; inject descends into [r]. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque7 Require Import Model.

(** ** Node-level push / inject.

    [push_node x n] prepends [XBase x] to the prefix buffer of [n].
    [inject_node n x] appends [XBase x] to the suffix buffer.  For
    [NOnlyEnd] (which has only one buffer that serves as both prefix
    and suffix), push prepends and inject appends to that single
    buffer. *)

Definition push_node {X : Type} (x : X) (n : Node X) : Node X :=
  match n with
  | NOnlyEnd b     => NOnlyEnd (buf6_push (XBase x) b)
  | NOnly  pre suf => NOnly    (buf6_push (XBase x) pre) suf
  | NLeft  pre suf => NLeft    (buf6_push (XBase x) pre) suf
  | NRight pre suf => NRight   (buf6_push (XBase x) pre) suf
  end.

Definition inject_node {X : Type} (n : Node X) (x : X) : Node X :=
  match n with
  | NOnlyEnd b     => NOnlyEnd (buf6_inject b (XBase x))
  | NOnly  pre suf => NOnly    pre (buf6_inject suf (XBase x))
  | NLeft  pre suf => NLeft    pre (buf6_inject suf (XBase x))
  | NRight pre suf => NRight   pre (buf6_inject suf (XBase x))
  end.

(** ** Packet-level push / inject.

    Both push and inject target the *outermost* node of the packet:
    the head of the body if the body is non-Hole, otherwise the
    tail.  This matches Viennot's structure. *)

Definition push_packet {X : Type} (x : X) (p : Packet X) : Packet X :=
  match p with
  | Pkt Hole tail           => Pkt Hole (push_node x tail)
  | Pkt (BSingleY head body) tail =>
      Pkt (BSingleY (push_node x head) body) tail
  | Pkt (BPairY head bl br) tail =>
      Pkt (BPairY (push_node x head) bl br) tail
  | Pkt (BPairO head bl br) tail =>
      Pkt (BPairO (push_node x head) bl br) tail
  end.

(** [inject_packet]: the new element goes at the *back* of the user
    sequence.  Under our linear flattening
    [packet_to_list (Pkt body tail) = body_to_list body ++ node_to_list tail],
    the tail's suffix is the last segment — so inject always modifies
    the tail's suffix buffer, regardless of body shape. *)

Definition inject_packet {X : Type} (p : Packet X) (x : X) : Packet X :=
  match p with
  | Pkt body tail => Pkt body (inject_node tail x)
  end.

(** ** Top-level [kcad_push] / [kcad_inject]. *)

(** [kcad_push x] descends into the LEFTMOST child of the chain
    (the leftmost element under our linear flattening).  At [KEmpty]
    we build a fresh singleton.  At [KSingle r p c] we modify the
    packet (whose contents come before [c] in the flattening).  At
    [KPair l r] we descend into [l]. *)

Fixpoint kcad_push {X : Type} (x : X) (k : KCadeque X) : KCadeque X :=
  match k with
  | KEmpty           => kcad_singleton x
  | KSingle r p c    => KSingle r (push_packet x p) c
  | KPair l r        => KPair (kcad_push x l) r
  end.

(** [kcad_inject k x] descends into the RIGHTMOST element holder.
    Under our linear flattening, the child chain [c] inside a
    [KSingle r p c] comes after [p]'s contents — so inject targets
    [c] if non-empty, falling back to the packet otherwise. *)

Fixpoint kcad_inject {X : Type} (k : KCadeque X) (x : X) : KCadeque X :=
  match k with
  | KEmpty                  => kcad_singleton x
  | KSingle r p KEmpty      => KSingle r (inject_packet p x) KEmpty
  | KSingle r p c           => KSingle r p (kcad_inject c x)
  | KPair l r               => KPair l (kcad_inject r x)
  end.

(** ** Sequence-correctness for the helpers.

    Each helper preserves [_to_list] in the canonical way. *)

(** *** Buffer push/inject under [buf6_flat_kelem]. *)

Lemma buf6_flat_kelem_push :
  forall (X : Type) (x : X) (b : Buf6 (KElem X)),
    buf6_flat_kelem (buf6_elems (buf6_push (XBase x) b))
    = x :: buf6_flat_kelem (buf6_elems b).
Proof.
  intros X x [xs]. unfold buf6_push, buf6_elems. cbn.
  reflexivity.
Qed.

Lemma buf6_flat_kelem_inject :
  forall (X : Type) (b : Buf6 (KElem X)) (x : X),
    buf6_flat_kelem (buf6_elems (buf6_inject b (XBase x)))
    = buf6_flat_kelem (buf6_elems b) ++ [x].
Proof.
  intros X [xs] x. unfold buf6_inject, buf6_elems. cbn.
  induction xs as [|e es IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

(** *** Node-level sequence preservation. *)

Lemma node_to_list_push :
  forall (X : Type) (x : X) (n : Node X),
    node_to_list (push_node x n) = x :: node_to_list n.
Proof.
  intros X x n.
  destruct n; cbn [push_node];
    rewrite ?node_to_list_NOnlyEnd, ?node_to_list_NOnly,
            ?node_to_list_NLeft, ?node_to_list_NRight;
    rewrite buf6_flat_kelem_push; reflexivity.
Qed.

Lemma node_to_list_inject :
  forall (X : Type) (n : Node X) (x : X),
    node_to_list (inject_node n x) = node_to_list n ++ [x].
Proof.
  intros X n x.
  destruct n; cbn [inject_node];
    rewrite ?node_to_list_NOnlyEnd, ?node_to_list_NOnly,
            ?node_to_list_NLeft, ?node_to_list_NRight;
    rewrite buf6_flat_kelem_inject;
    try rewrite <- app_assoc;
    reflexivity.
Qed.

(** *** Packet-level sequence preservation. *)

Lemma packet_to_list_push :
  forall (X : Type) (x : X) (p : Packet X),
    packet_to_list (push_packet x p) = x :: packet_to_list p.
Proof.
  intros X x p.
  destruct p as [body tail].
  destruct body; cbn [push_packet packet_to_list body_to_list];
    rewrite node_to_list_push;
    cbn [app];
    reflexivity.
Qed.

Lemma packet_to_list_inject :
  forall (X : Type) (p : Packet X) (x : X),
    packet_to_list (inject_packet p x) = packet_to_list p ++ [x].
Proof.
  intros X p x.
  destruct p as [body tail].
  cbn [inject_packet packet_to_list].
  rewrite node_to_list_inject.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(** *** Top-level [kcad_push] / [kcad_inject] sequence laws. *)

Theorem kcad_push_seq :
  forall (X : Type) (x : X) (k : KCadeque X),
    kcad_to_list (kcad_push x k) = x :: kcad_to_list k.
Proof.
  intros X x k.
  induction k as [|r p c IHc|l IHl r IHr].
  - reflexivity.
  - cbn [kcad_push kcad_to_list].
    rewrite packet_to_list_push.
    reflexivity.
  - cbn [kcad_push kcad_to_list].
    rewrite IHl. reflexivity.
Qed.

Theorem kcad_inject_seq :
  forall (X : Type) (k : KCadeque X) (x : X),
    kcad_to_list (kcad_inject k x) = kcad_to_list k ++ [x].
Proof.
  intros X k x.
  induction k as [|r p c IHc|l IHl r IHr].
  - reflexivity.
  - destruct c.
    + (* c = KEmpty *)
      cbn [kcad_inject kcad_to_list].
      rewrite packet_to_list_inject.
      rewrite app_nil_r, app_nil_r. reflexivity.
    + (* c = KSingle _ _ _ *)
      change (kcad_inject (KSingle r p (KSingle r0 p0 c)) x)
        with (KSingle r p (kcad_inject (KSingle r0 p0 c) x)).
      cbn [kcad_to_list].
      rewrite IHc.
      cbn [kcad_to_list].
      repeat rewrite <- app_assoc. reflexivity.
    + (* c = KPair _ _ *)
      change (kcad_inject (KSingle r p (KPair c1 c2)) x)
        with (KSingle r p (kcad_inject (KPair c1 c2) x)).
      cbn [kcad_to_list].
      rewrite IHc.
      cbn [kcad_to_list].
      repeat rewrite <- app_assoc. reflexivity.
  - cbn [kcad_inject kcad_to_list].
    rewrite IHr. rewrite <- app_assoc. reflexivity.
Qed.

(** ** Sanity checks. *)

Example push_then_inject :
  let k := kcad_push 1 (kcad_inject (kcad_inject kcad_empty 2) 3) in
  kcad_to_list k = [1; 2; 3].
Proof. reflexivity. Qed.

Example multi_push :
  kcad_to_list (kcad_push 1 (kcad_push 2 (kcad_push 3 kcad_empty)))
  = [1; 2; 3].
Proof. reflexivity. Qed.

Example multi_inject :
  kcad_to_list (kcad_inject (kcad_inject (kcad_inject kcad_empty 1) 2) 3)
  = [1; 2; 3].
Proof. reflexivity. Qed.
