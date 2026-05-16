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

(** Phase 5b: push and inject are WC O(1) by construction.

    Previously [kcad_push] recursed through [KPair l r → KPair (push l) r]
    and [kcad_inject] recursed through [KSingle r p c → KSingle r p
    (inject c x)] and [KPair l r → KPair l (inject r x)] — both
    O(depth) in the KPair-tree or child-chain depth.

    To keep push/inject WC O(1) on every structure:

    - [kcad_push x (KPair l r)] wraps the entire [KPair l r] as the
      child of a fresh single-element [KSingle].  No recursion.

    - [kcad_inject (KSingle r p c) x] when [c] is non-[KEmpty] places
      a single-element singleton to the right of [c] via [KPair],
      keeping the outer [KSingle] unchanged.  No recursion.

    - [kcad_inject (KPair l r) x] does the same: [KPair (KPair l r)
      (kcad_singleton x)].

    The trade-off: pop/eject on KPair-deep trees may now descend
    O(depth) into the right spine of the [KPair] structure.  Phase 5c
    introduces a smart concat that keeps the [KPair] tree depth
    bounded; until then, deep-concat workloads see slower pop/eject. *)

Definition kcad_push {X : Type} (x : X) (k : KCadeque X) : KCadeque X :=
  match k with
  | KEmpty           => kcad_singleton x
  | KSingle r p c    => KSingle r (push_packet x p) c
  | KPair _ _        =>
      KSingle RegG (Pkt Hole (NOnlyEnd (mkBuf6 [XBase x]))) k
  end.

Definition kcad_inject {X : Type} (k : KCadeque X) (x : X) : KCadeque X :=
  match k with
  | KEmpty                  => kcad_singleton x
  | KSingle r p KEmpty      => KSingle r (inject_packet p x) KEmpty
  | KSingle r p c           =>
      KSingle r p (KPair c (kcad_singleton x))
  | KPair _ _               =>
      KPair k (kcad_singleton x)
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
  destruct k as [|r p c|l r].
  - reflexivity.
  - cbn [kcad_push kcad_to_list].
    rewrite packet_to_list_push.
    reflexivity.
  - (* KPair: wrap as fresh KSingle head with a single-element node. *)
    change (kcad_to_list (kcad_push x (KPair l r)))
      with (kcad_to_list (kcad_singleton x) ++ kcad_to_list (KPair l r)).
    rewrite kcad_to_list_singleton. reflexivity.
Qed.

Theorem kcad_inject_seq :
  forall (X : Type) (k : KCadeque X) (x : X),
    kcad_to_list (kcad_inject k x) = kcad_to_list k ++ [x].
Proof.
  intros X k x.
  destruct k as [|r p c|l r].
  - reflexivity.
  - destruct c as [|r' p' c'|l' r'].
    + (* c = KEmpty: inject into packet directly. *)
      cbn [kcad_inject kcad_to_list].
      rewrite packet_to_list_inject.
      rewrite app_nil_r, app_nil_r. reflexivity.
    + (* c = KSingle _ _ _: wrap child in KPair (c, singleton x). *)
      change (kcad_to_list (kcad_inject
                              (KSingle r p (KSingle r' p' c')) x))
        with (packet_to_list p
              ++ (kcad_to_list (KSingle r' p' c')
                  ++ kcad_to_list (kcad_singleton x))).
      rewrite kcad_to_list_singleton.
      cbn [kcad_to_list].
      rewrite app_assoc. reflexivity.
    + (* c = KPair _ _: wrap child in KPair (c, singleton x). *)
      change (kcad_to_list (kcad_inject
                              (KSingle r p (KPair l' r')) x))
        with (packet_to_list p
              ++ (kcad_to_list (KPair l' r')
                  ++ kcad_to_list (kcad_singleton x))).
      rewrite kcad_to_list_singleton.
      cbn [kcad_to_list].
      rewrite app_assoc. reflexivity.
  - (* KPair: wrap as KPair k (singleton x). *)
    change (kcad_to_list (kcad_inject (KPair l r) x))
      with (kcad_to_list (KPair l r) ++ kcad_to_list (kcad_singleton x)).
    rewrite kcad_to_list_singleton. reflexivity.
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

(** Phase 5b regression: push/inject on a KPair-rooted structure
    must succeed via the non-recursive wrap branch and preserve
    sequence semantics. *)

Example phase5b_push_on_kpair :
  let kp : KCadeque nat :=
    KPair (kcad_singleton 1) (kcad_singleton 2) in
  kcad_to_list (kcad_push 0 kp) = [0; 1; 2].
Proof. reflexivity. Qed.

Example phase5b_inject_on_kpair :
  let kp : KCadeque nat :=
    KPair (kcad_singleton 1) (kcad_singleton 2) in
  kcad_to_list (kcad_inject kp 3) = [1; 2; 3].
Proof. reflexivity. Qed.

Example phase5b_inject_on_ksingle_nonempty_child :
  (* Build a KSingle whose child is itself a KSingle, then inject. *)
  let inner := kcad_singleton 2 in
  let outer : KCadeque nat :=
    KSingle RegG (Pkt Hole (NOnlyEnd (mkBuf6 [XBase 1]))) inner in
  kcad_to_list (kcad_inject outer 3) = [1; 2; 3].
Proof. reflexivity. Qed.
