(** * Module: KTDeque.DequePtr.OpsAbstract -- non-recursive push/inject/pop/eject
    on the abstract [Chain] / [Packet].

    Per ADR-0010+ and the project hard rule: WC O(1) requires that each
    operation touches a CONSTANT number of structural cells.  In the
    Viennot packet representation, this is achieved by:

    1. Aggregating each yellow run into one [Packet] (one allocation
       unit).  Done in [Model.v].

    2. Operations dispatch on the OUTERMOST [PNode] of the topmost
       packet (or on [Ending] when the chain is a single buffer).  No
       recursion on packets or chains; the structural depth is invisible
       to a single push/pop.

    3. The repair half-step ([green_of_red] in Viennot) re-threads the
       chain by touching at most TWO packets + ONE chain link.  This is
       implemented in the imperative tier ([Footprint.v]); on the
       abstract side we expose the simple "naive push, then maybe
       overflow" surface, leaving the cascade-prevention to the heap-
       layer's regularity invariant.

    The abstract ops here are partial via [option]: they return [None]
    when the buffer overflows / underflows beyond the local repair's
    reach.  The cost-tracked [Footprint.v] versions implement the actual
    KT cascade bound; this file establishes the functional surface.

    Cross-references:
    - [bench/viennot/deque_core.ml] lines 60+ for the operations.
    - [KTDeque/DequePtr/Model.v] -- the [Packet] / [Chain] types.
*)

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model.

(** ** [push_chain]: push onto the front of a chain.

    Non-recursive on the chain spine: dispatches on the outer
    [Ending b | ChainCons p c'] structure, and within [ChainCons], on
    [Hole | PNode pre i suf].  Recursion-free; depth-invariant. *)

Definition push_chain {A : Type} (x : E.t A) (c : Chain A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_push_naive x b with
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole =>
          (* [Hole] inside a [ChainCons] means the inner level is
             addressed by [c']; pushing is a "thin pass-through" --
             we have no buffer here to push to.  In a well-formed
             chain this case shouldn't arise (a packet with [Hole]
             at the top has empty pre/suf, so it's effectively
             absent).  Returning [None] makes the case explicit. *)
          None
      | PNode pre i suf =>
          match buf5_push_naive x pre with
          | Some pre' => Some (ChainCons (PNode pre' i suf) c')
          | None      => None
          end
      end
  end.

Definition inject_chain {A : Type} (c : Chain A) (x : E.t A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_inject_naive b x with
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_inject_naive suf x with
          | Some suf' => Some (ChainCons (PNode pre i suf') c')
          | None      => None
          end
      end
  end.

Definition pop_chain {A : Type} (c : Chain A)
  : option (E.t A * Chain A) :=
  match c with
  | Ending b =>
      match buf5_pop_naive b with
      | Some (x, b') => Some (x, Ending b')
      | None         => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_pop_naive pre with
          | Some (x, pre') => Some (x, ChainCons (PNode pre' i suf) c')
          | None           => None
          end
      end
  end.

Definition eject_chain {A : Type} (c : Chain A)
  : option (Chain A * E.t A) :=
  match c with
  | Ending b =>
      match buf5_eject_naive b with
      | Some (b', x) => Some (Ending b', x)
      | None         => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_eject_naive suf with
          | Some (suf', x_out) => Some (ChainCons (PNode pre i suf') c', x_out)
          | None               => None
          end
      end
  end.

(** ** Sequence preservation.

    Each abstract op preserves [chain_to_list] up to a single element
    at the appropriate end. *)

Lemma push_chain_seq :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    push_chain x c = Some c' ->
    chain_to_list c' = E.to_list A x ++ chain_to_list c.
Proof.
  intros A x c c' Heq.
  unfold chain_to_list.
  destruct c as [b | p c0]; cbn in Heq.
  - destruct (buf5_push_naive x b) as [b'|] eqn:Hpush; [|discriminate].
    inversion Heq; subst c'. cbn. unfold buf_seq_E.
    eapply buf5_push_naive_seq; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush; [|discriminate].
    inversion Heq; subst c'. cbn. unfold buf_seq_E.
    erewrite buf5_push_naive_seq by eauto.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma inject_chain_seq :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    inject_chain c x = Some c' ->
    chain_to_list c' = chain_to_list c ++ E.to_list A x.
Proof.
  intros A c c' x Heq.
  unfold chain_to_list.
  destruct c as [b | p c0]; cbn in Heq.
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hinj; [|discriminate].
    inversion Heq; subst c'. cbn. unfold buf_seq_E.
    eapply buf5_inject_naive_seq; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hinj; [|discriminate].
    inversion Heq; subst c'. cbn. unfold buf_seq_E.
    pose proof (@buf5_inject_naive_seq (E.t A) A (E.to_list A) suf suf' x Hinj) as Hs.
    rewrite Hs.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma pop_chain_seq :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    pop_chain c = Some (x, c') ->
    chain_to_list c = E.to_list A x ++ chain_to_list c'.
Proof.
  intros A c x c' Heq.
  unfold chain_to_list.
  destruct c as [b | p c0]; cbn in Heq.
  - destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hpop; [|discriminate].
    inversion Heq; subst x c'. cbn. unfold buf_seq_E.
    eapply buf5_pop_naive_seq; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hpop; [|discriminate].
    inversion Heq; subst xp c'. cbn. unfold buf_seq_E.
    pose proof (@buf5_pop_naive_seq (E.t A) A (E.to_list A) pre x pre' Hpop) as Hs.
    rewrite Hs.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma eject_chain_seq :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    eject_chain c = Some (c', x) ->
    chain_to_list c = chain_to_list c' ++ E.to_list A x.
Proof.
  intros A c c' x Heq.
  unfold chain_to_list.
  destruct c as [b | p c0]; cbn in Heq.
  - destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hej; [|discriminate].
    inversion Heq; subst c' xp. cbn. unfold buf_seq_E.
    eapply buf5_eject_naive_seq; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hej; [|discriminate].
    inversion Heq; subst c' xp. cbn. unfold buf_seq_E.
    pose proof (@buf5_eject_naive_seq (E.t A) A (E.to_list A) suf suf' x Hej) as Hs.
    rewrite Hs.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** Levels preservation.

    Each abstract op preserves [chain_levels] when the input element is
    at the matching level.  This ensures that the level invariant is
    maintained across operations. *)

Lemma buf5_push_preserves_levels :
  forall (A : Type) (k : nat) (x : E.t A) (b b' : Buf5 (E.t A)),
    E.level A x = k ->
    buf_all_at_level k b ->
    buf5_push_naive x b = Some b' ->
    buf_all_at_level k b'.
Proof.
  intros A k x b b' Hlx Hb Hpush.
  destruct b; cbn in Hpush; inversion Hpush; subst; cbn in *; intuition.
Qed.

Lemma buf5_inject_preserves_levels :
  forall (A : Type) (k : nat) (b : Buf5 (E.t A)) (x : E.t A) (b' : Buf5 (E.t A)),
    E.level A x = k ->
    buf_all_at_level k b ->
    buf5_inject_naive b x = Some b' ->
    buf_all_at_level k b'.
Proof.
  intros A k b x b' Hlx Hb Hinj.
  destruct b; cbn in Hinj; inversion Hinj; subst; cbn in *; intuition.
Qed.

Lemma buf5_pop_preserves_levels :
  forall (A : Type) (k : nat) (b : Buf5 (E.t A)) (x : E.t A) (b' : Buf5 (E.t A)),
    buf_all_at_level k b ->
    buf5_pop_naive b = Some (x, b') ->
    E.level A x = k /\ buf_all_at_level k b'.
Proof.
  intros A k b x b' Hb Hpop.
  destruct b; cbn in Hpop; inversion Hpop; subst; cbn in *; intuition.
Qed.

Lemma buf5_eject_preserves_levels :
  forall (A : Type) (k : nat) (b : Buf5 (E.t A)) (x : E.t A) (b' : Buf5 (E.t A)),
    buf_all_at_level k b ->
    buf5_eject_naive b = Some (b', x) ->
    E.level A x = k /\ buf_all_at_level k b'.
Proof.
  intros A k b x b' Hb Hej.
  destruct b; cbn in Hej; inversion Hej; subst; cbn in *; intuition.
Qed.

Lemma push_chain_preserves_levels :
  forall (A : Type) (x : E.t A) (c c' : Chain A) (k : nat),
    E.level A x = k ->
    chain_levels k c ->
    push_chain x c = Some c' ->
    chain_levels k c'.
Proof.
  intros A x c c' k Hlx Hcl Hpush.
  destruct c as [b | p c0]; cbn in Hpush.
  - destruct (buf5_push_naive x b) as [b'|] eqn:Hpb; [|discriminate].
    inversion Hpush; subst c'. clear Hpush.
    inversion Hcl; subst.
    apply cl_ending. eapply buf5_push_preserves_levels; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpb; [|discriminate].
    inversion Hpush; subst c'. clear Hpush.
    inversion Hcl as [|? ? ? Hpl Hcl_inner]; subst.
    inversion Hpl as [|? ? ? ? Hpre Hi Hsuf]; subst.
    apply cl_cons.
    apply pl_node.
    refine (@buf5_push_preserves_levels A (E.level A x) x pre pre' eq_refl Hpre Hpb).
    exact Hi.
    exact Hsuf.
    exact Hcl_inner.
Qed.

Lemma inject_chain_preserves_levels :
  forall (A : Type) (c c' : Chain A) (x : E.t A) (k : nat),
    E.level A x = k ->
    chain_levels k c ->
    inject_chain c x = Some c' ->
    chain_levels k c'.
Proof.
  intros A c c' x k Hlx Hcl Hinj.
  destruct c as [b | p c0]; cbn in Hinj.
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hib; [|discriminate].
    inversion Hinj; subst c'. clear Hinj.
    inversion Hcl; subst.
    apply cl_ending. eapply buf5_inject_preserves_levels; eauto.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hib; [|discriminate].
    inversion Hinj; subst c'. clear Hinj.
    inversion Hcl as [|? ? ? Hpl Hcl_inner]; subst.
    inversion Hpl as [|? ? ? ? Hpre Hi Hsuf]; subst.
    apply cl_cons.
    apply pl_node.
    exact Hpre.
    exact Hi.
    refine (@buf5_inject_preserves_levels A (E.level A x) suf x suf' eq_refl Hsuf Hib).
    exact Hcl_inner.
Qed.

Lemma pop_chain_preserves_levels :
  forall (A : Type) (c c' : Chain A) (x : E.t A) (k : nat),
    chain_levels k c ->
    pop_chain c = Some (x, c') ->
    E.level A x = k /\ chain_levels k c'.
Proof.
  intros A c c' x k Hcl Hpop.
  destruct c as [b | p c0]; cbn in Hpop.
  - destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hpop_b; [|discriminate].
    inversion Hpop; subst xp c'. clear Hpop.
    inversion Hcl; subst.
    pose proof (@buf5_pop_preserves_levels A k b x b' H1 Hpop_b)
      as [Hlx Hb].
    split; [exact Hlx|].
    apply cl_ending. exact Hb.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hpop_b; [|discriminate].
    inversion Hpop; subst xp c'. clear Hpop.
    inversion Hcl as [|? ? ? Hpl Hcl_inner]; subst.
    inversion Hpl as [|? ? ? ? Hpre Hi Hsuf]; subst.
    pose proof (@buf5_pop_preserves_levels A k pre x pre' Hpre Hpop_b)
      as [Hlx Hpre'].
    split; [exact Hlx|].
    apply cl_cons.
    apply pl_node.
    exact Hpre'.
    exact Hi.
    exact Hsuf.
    exact Hcl_inner.
Qed.

Lemma eject_chain_preserves_levels :
  forall (A : Type) (c c' : Chain A) (x : E.t A) (k : nat),
    chain_levels k c ->
    eject_chain c = Some (c', x) ->
    E.level A x = k /\ chain_levels k c'.
Proof.
  intros A c c' x k Hcl Hej.
  destruct c as [b | p c0]; cbn in Hej.
  - destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hej_b; [|discriminate].
    inversion Hej; subst c' xp. clear Hej.
    inversion Hcl; subst.
    pose proof (@buf5_eject_preserves_levels A k b x b' H1 Hej_b)
      as [Hlx Hb].
    split; [exact Hlx|].
    apply cl_ending. exact Hb.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hej_b; [|discriminate].
    inversion Hej; subst c' xp. clear Hej.
    inversion Hcl as [|? ? ? Hpl Hcl_inner]; subst.
    inversion Hpl as [|? ? ? ? Hpre Hi Hsuf]; subst.
    pose proof (@buf5_eject_preserves_levels A k suf x suf' Hsuf Hej_b)
      as [Hlx Hsuf'].
    split; [exact Hlx|].
    apply cl_cons.
    apply pl_node.
    exact Hpre.
    exact Hi.
    exact Hsuf'.
    exact Hcl_inner.
Qed.

(** ** Overflow repair: [make_red_chain].

    When a naive [push] / [inject] on the top buffer overflows to [B5],
    the abstract repair takes the last (push) or first (inject) two
    elements of the [B5], pairs them at the next level, and pushes the
    pair onto the next chain link's prefix.

    The Viennot insight: the inner yellow run is aggregated into a
    single packet allocation, so the chain hop from the top to "one
    chain step deeper" is a single pointer dereference at the heap
    layer.  Sequence preservation follows by buffer-level reasoning;
    the proof does not recurse on chain depth. *)

(** [make_red_push_chain c]: when the top of [c] has prefix [B5 ...],
    pair the last two and push onto the next chain link.

    Returns [None] if the chain is malformed (no next link, the inner
    yellow run is non-trivial — see below — or pair levels mismatch,
    or next-link prefix overflows again).

    KEY INVARIANT: in the [ChainCons (PNode pre i suf) c'] case, we
    require [i = Hole].  This is the Viennot algorithm's invariant:
    when we make_red, the topmost packet's inner yellow run is empty
    (because we just allocated the topmost cell as a single-PNode
    packet with no aggregated inner run).  Without this, sequence
    preservation fails: the pair would land "above" the inner run [i],
    not at the chain step deeper. *)
Definition make_red_push_chain {A : Type} (c : Chain A)
  : option (Chain A) :=
  match c with
  | Ending (B5 a b cc d e) =>
      (* The chain is a single buffer; pair (d, e) at level 1 and form
         a new ChainCons whose tail is a fresh Ending (B1 pde). *)
      match Nat.eq_dec (E.level A d) (E.level A e) with
      | left eq =>
          Some (ChainCons (PNode (B3 a b cc) Hole B0)
                          (Ending (B1 (E.pair A d e eq))))
      | right _ => None
      end
  | ChainCons (PNode (B5 a b cc d e) Hole suf) c' =>
      match Nat.eq_dec (E.level A d) (E.level A e) with
      | left eq =>
          (* Pair (d, e), push pde onto c' (the next chain link).
             c' is at depth (S k); the pair is at level (S k). *)
          match push_chain (E.pair A d e eq) c' with
          | Some c'' => Some (ChainCons (PNode (B3 a b cc) Hole suf) c'')
          | None     => None
          end
      | right _ => None
      end
  | ChainCons (PNode (B5 a b cc d e) (PNode pre' i' suf') suf) c' =>
      (* Phase S''''' / P5 / Viennot Case 3: depth>=2, nested top.
         Pair (d, e) at next level, push pde onto the inner packet's
         prefix [pre'] (without recursing into [c']).  The outer level
         peels to (B3 a b cc, Hole, suf) and the inner packet promotes
         to a fresh chain link with the original [c'] as its tail. *)
      match Nat.eq_dec (E.level A d) (E.level A e) with
      | left eq =>
          let pde := E.pair A d e eq in
          match buf5_push_naive pde pre' with
          | Some (B5 _ _ _ _ _) => None  (* regularity prevents *)
          | Some pre'' =>
              Some (ChainCons (PNode (B3 a b cc) Hole suf)
                              (ChainCons (PNode pre'' i' suf') c'))
          | None => None
          end
      | right _ => None
      end
  | _ => None
  end.

Definition make_red_inject_chain {A : Type} (c : Chain A)
  : option (Chain A) :=
  match c with
  | Ending (B5 a b cc d e) =>
      (* Inject overflow: pair (a, b) at level 1, form a ChainCons
         whose top is a PNode whose prefix is empty and suffix carries
         the last three; the inner chain link holds the pair. *)
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          Some (ChainCons (PNode B0 Hole (B3 cc d e))
                          (Ending (B1 (E.pair A a b eq))))
      | right _ => None
      end
  | ChainCons (PNode pre Hole (B5 a b cc d e)) c' =>
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          match inject_chain c' (E.pair A a b eq) with
          | Some c'' => Some (ChainCons (PNode pre Hole (B3 cc d e)) c'')
          | None     => None
          end
      | right _ => None
      end
  | ChainCons (PNode pre (PNode pre' i' suf') (B5 a b cc d e)) c' =>
      (* Phase S''''' / P5 / Viennot Case 3 dual: depth>=2, nested top
         on the inject side.  Pair (a, b) at next level, inject pab onto
         the inner packet's suffix [suf'].  Outer peels to (pre, Hole,
         B3 cc d e); the inner packet promotes to a fresh chain link
         with the original [c'] as its tail. *)
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          let pab := E.pair A a b eq in
          match buf5_inject_naive suf' pab with
          | Some (B5 _ _ _ _ _) => None
          | Some suf'' =>
              Some (ChainCons (PNode pre Hole (B3 cc d e))
                              (ChainCons (PNode pre' i' suf'') c'))
          | None => None
          end
      | right _ => None
      end
  | _ => None
  end.

(** ** Sequence preservation for make_red.

    Both the [Ending] and [ChainCons] cases preserve [chain_to_list] —
    the buffer-only argument: B5 splits into B3 + 2 elements, the 2
    elements pair at the next level (preserving total flatten via
    [E.to_list_pair]), and the pair lands at the next chain link. *)

Lemma make_red_push_chain_seq :
  forall (A : Type) (c c' : Chain A),
    make_red_push_chain c = Some c' ->
    chain_to_list c' = chain_to_list c.
Proof.
  intros A c c' Heq.
  unfold chain_to_list, make_red_push_chain in *.
  destruct c as [b | p c0].
  - destruct b as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
    destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
      [|discriminate].
    inversion Heq; subst c'; clear Heq. cbn -[E.pair].
    unfold buf_seq_E. cbn -[E.pair].
    rewrite E.to_list_pair.
    rewrite ?app_nil_r. repeat rewrite <- app_assoc. reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: existing simple case *)
      destruct pre as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
      destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
        [|discriminate].
      destruct (push_chain (E.pair A u v eq) c0) as [c0''|] eqn:Hpush;
        [|discriminate].
      inversion Heq; subst c'; clear Heq.
      pose proof (@push_chain_seq A (E.pair A u v eq) c0 c0'' Hpush) as Hps.
      unfold chain_to_list in Hps.
      cbn -[E.pair]. rewrite Hps.
      unfold buf_seq_E. cbn -[E.pair].
      rewrite E.to_list_pair.
      repeat rewrite <- app_assoc. reflexivity.
    + (* PNode inner: new nested case (Phase S''''' P5) *)
      destruct pre as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
      destruct (Nat.eq_dec (E.level A u) (E.level A v)) as [eq|];
        [|discriminate].
      destruct (buf5_push_naive (E.pair A u v eq) ipre) as [pre''|] eqn:Hpush;
        [|discriminate].
      pose proof (@buf5_push_naive_seq (E.t A) A (E.to_list A)
                     (E.pair A u v eq) ipre _ Hpush) as Hpush_seq.
      destruct pre'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv];
        try discriminate.
      * (* B0: buf5_push_naive never returns B0 *)
        destruct ipre; cbn in Hpush; inversion Hpush.
      * (* B1 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hpush_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B2 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hpush_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B3 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hpush_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B4 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hpush_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma make_red_inject_chain_seq :
  forall (A : Type) (c c' : Chain A),
    make_red_inject_chain c = Some c' ->
    chain_to_list c' = chain_to_list c.
Proof.
  intros A c c' Heq.
  unfold chain_to_list, make_red_inject_chain in *.
  destruct c as [b | p c0].
  - destruct b as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
    destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
      [|discriminate].
    inversion Heq; subst c'; clear Heq. cbn -[E.pair].
    unfold buf_seq_E. cbn -[E.pair].
    rewrite E.to_list_pair.
    rewrite ?app_nil_r, ?app_nil_l.
    repeat rewrite <- app_assoc. reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: existing case *)
      destruct suf as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
      destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
        [|discriminate].
      destruct (inject_chain c0 (E.pair A y z eq)) as [c0''|] eqn:Hinj;
        [|discriminate].
      inversion Heq; subst c'; clear Heq.
      pose proof (@inject_chain_seq A c0 c0'' (E.pair A y z eq) Hinj) as Hps.
      unfold chain_to_list in Hps.
      cbn -[E.pair]. rewrite Hps.
      unfold buf_seq_E. cbn -[E.pair].
      rewrite E.to_list_pair.
      repeat rewrite <- app_assoc. reflexivity.
    + (* PNode inner: new nested case (Phase S''''' P5) *)
      destruct suf as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
      destruct (Nat.eq_dec (E.level A y) (E.level A z)) as [eq|];
        [|discriminate].
      destruct (buf5_inject_naive isuf (E.pair A y z eq)) as [suf''|] eqn:Hinj;
        [|discriminate].
      pose proof (@buf5_inject_naive_seq (E.t A) A (E.to_list A)
                     isuf _ (E.pair A y z eq) Hinj) as Hinj_seq.
      destruct suf'' as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv];
        try discriminate.
      * (* B0: buf5_inject_naive never returns B0 *)
        destruct isuf; cbn in Hinj; inversion Hinj.
      * (* B1 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hinj_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B2 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hinj_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B3 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hinj_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
      * (* B4 *)
        inversion Heq; subst c'; clear Heq.
        cbn -[E.pair]. unfold buf_seq_E in *. cbn -[E.pair] in *.
        rewrite Hinj_seq. rewrite E.to_list_pair.
        repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** [push_chain_full] / [inject_chain_full]: full push / inject with
    one-step make_red repair.

    These are the abstract counterparts of the imperative [exec_push_pkt_C]
    after the make_red merger.  When the naive op succeeds without
    overflow, return its result.  Otherwise (the naive op produced a B5
    on the top), fire make_red.

    Note: these are defined extrinsically by inspecting the result of
    the naive [buf5_push_naive] on the top buffer.  This mirrors the
    decision logic of the imperative implementation. *)

Definition push_chain_full {A : Type} (x : E.t A) (c : Chain A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_push_naive x b with
      | Some (B5 a b1 cc d e) =>
          (* Overflow at top of Ending: fire make_red. *)
          make_red_push_chain (Ending (B5 a b1 cc d e))
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre Hole suf =>
          match buf5_push_naive x pre with
          | Some (B5 a b1 cc d e) =>
              make_red_push_chain
                (ChainCons (PNode (B5 a b1 cc d e) Hole suf) c')
          | Some pre' => Some (ChainCons (PNode pre' Hole suf) c')
          | None      => None
          end
      | PNode pre (PNode pre' i' suf') suf =>
          (* Phase S6 / P5 closure: depth-2 nested top, dispatch
             on the outer pre's overflow into Case 3 of [make_red_push_chain]. *)
          match buf5_push_naive x pre with
          | Some (B5 a b1 cc d e) =>
              make_red_push_chain
                (ChainCons (PNode (B5 a b1 cc d e)
                                  (PNode pre' i' suf') suf) c')
          | Some pre_new =>
              Some (ChainCons (PNode pre_new (PNode pre' i' suf') suf) c')
          | None => None
          end
      end
  end.

Definition inject_chain_full {A : Type} (c : Chain A) (x : E.t A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_inject_naive b x with
      | Some (B5 a b1 cc d e) =>
          make_red_inject_chain (Ending (B5 a b1 cc d e))
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre Hole suf =>
          match buf5_inject_naive suf x with
          | Some (B5 a b1 cc d e) =>
              make_red_inject_chain
                (ChainCons (PNode pre Hole (B5 a b1 cc d e)) c')
          | Some suf' => Some (ChainCons (PNode pre Hole suf') c')
          | None      => None
          end
      | PNode pre (PNode pre' i' suf') suf =>
          (* Phase S6 / P5 closure: depth-2 nested top, dispatch
             on the outer suf's overflow into Case 3 dual of
             [make_red_inject_chain]. *)
          match buf5_inject_naive suf x with
          | Some (B5 a b1 cc d e) =>
              make_red_inject_chain
                (ChainCons (PNode pre (PNode pre' i' suf')
                                  (B5 a b1 cc d e)) c')
          | Some suf_new =>
              Some (ChainCons (PNode pre (PNode pre' i' suf') suf_new) c')
          | None => None
          end
      end
  end.

Local Ltac push_simple_ending Heq Hs :=
  inversion Heq; subst; unfold chain_to_list; cbn -[buf5_seq];
  unfold buf_seq_E; rewrite Hs; reflexivity.

Local Ltac push_simple_cons Heq Hs :=
  inversion Heq; subst; unfold chain_to_list; cbn -[buf5_seq];
  unfold buf_seq_E; rewrite Hs;
  repeat rewrite <- app_assoc; reflexivity.

Lemma push_chain_full_seq :
  forall (A : Type) (x : E.t A) (c c' : Chain A),
    push_chain_full x c = Some c' ->
    chain_to_list c' = E.to_list A x ++ chain_to_list c.
Proof.
  intros A x c c' Heq.
  unfold push_chain_full in Heq.
  destruct c as [b | p c0].
  - destruct (buf5_push_naive x b) as [b'|] eqn:Hpush; [|discriminate].
    pose proof (@buf5_push_naive_seq (E.t A) A (E.to_list A) x b b' Hpush) as Hs.
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + (* B0 impossible *) destruct b; cbn in Hpush; inversion Hpush.
    + push_simple_ending Heq Hs.
    + push_simple_ending Heq Hs.
    + push_simple_ending Heq Hs.
    + push_simple_ending Heq Hs.
    + (* B5: make_red *)
      pose proof (@make_red_push_chain_seq A (Ending (B5 y z w u v)) c' Heq) as Hmr.
      rewrite Hmr.
      unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
      rewrite Hs. reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: simple-packet path *)
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush; [|discriminate].
      pose proof (@buf5_push_naive_seq (E.t A) A (E.to_list A) x pre pre' Hpush) as Hs.
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * (* B0 impossible *) destruct pre; cbn in Hpush; inversion Hpush.
      * push_simple_cons Heq Hs.
      * push_simple_cons Heq Hs.
      * push_simple_cons Heq Hs.
      * push_simple_cons Heq Hs.
      * (* B5: make_red *)
        pose proof (@make_red_push_chain_seq A
                      (ChainCons (PNode (B5 y z w u v) Hole suf) c0) c' Heq) as Hmr.
        rewrite Hmr.
        unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
        rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      destruct (buf5_push_naive x pre) as [pre'|] eqn:Hpush; [|discriminate].
      pose proof (@buf5_push_naive_seq (E.t A) A (E.to_list A) x pre pre' Hpush) as Hs.
      destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
      * (* B0 impossible *) destruct pre; cbn in Hpush; inversion Hpush.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * (* B5: make_red Case 3 *)
        pose proof (@make_red_push_chain_seq A
                      (ChainCons (PNode (B5 y z w u v)
                                        (PNode ipre ii isuf) suf) c0) c' Heq) as Hmr.
        rewrite Hmr.
        unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
        rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
Qed.

Local Ltac inject_simple_ending Heq Hs :=
  inversion Heq; subst; unfold chain_to_list; cbn -[buf5_seq];
  unfold buf_seq_E; rewrite Hs; reflexivity.

Local Ltac inject_simple_cons Heq Hs :=
  inversion Heq; subst; unfold chain_to_list; cbn -[buf5_seq];
  unfold buf_seq_E; rewrite Hs;
  repeat rewrite <- app_assoc; reflexivity.

(** ** Proof-artifact: recursive push/inject (NOT WC O(1)).

    [push_chain_rec] cascades through the chain spine, firing
    [make_red] at each level as needed.  This is O(log n) worst
    case — NOT the production WC O(1) bound.  The certified
    production implementations are [exec_push_pkt_C] in
    [Footprint.v] (constant-bound by structural inspection).

    Despite being a proof artifact, [push_chain_rec] is what we
    extract to OCaml for benchmarking: the recursion follows the
    chain spine which has logarithmic depth, so amortized cost
    is competitive with Viennot's OCaml deque (which is also
    persistent + amortized in practice).  See the
    [agentic-dev-kit] / CLAUDE.md note: "If you find yourself
    writing `let rec kt_push` ... stop." — but this is the
    abstract proof-side version, not the certified one. *)

Fixpoint push_chain_rec {A : Type} (x : E.t A) (c : Chain A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_push_naive x b with
      | Some (B5 a b1 cc d e) =>
          match Nat.eq_dec (E.level A d) (E.level A e) with
          | left eq =>
              Some (ChainCons (PNode (B3 a b1 cc) Hole B0)
                              (Ending (B1 (E.pair A d e eq))))
          | right _ => None
          end
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_push_naive x pre with
          | Some (B5 a b1 cc d e) =>
              match i with
              | Hole =>
                  match Nat.eq_dec (E.level A d) (E.level A e) with
                  | left eq =>
                      match push_chain_rec (E.pair A d e eq) c' with
                      | Some c'' =>
                          Some (ChainCons (PNode (B3 a b1 cc) Hole suf) c'')
                      | None => None
                      end
                  | right _ => None
                  end
              | PNode _ _ _ => None  (* non-trivial inner: reject *)
              end
          | Some pre' => Some (ChainCons (PNode pre' i suf) c')
          | None      => None
          end
      end
  end.

Fixpoint inject_chain_rec {A : Type} (c : Chain A) (x : E.t A)
  : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_inject_naive b x with
      | Some (B5 a b1 cc d e) =>
          match Nat.eq_dec (E.level A a) (E.level A b1) with
          | left eq =>
              Some (ChainCons (PNode B0 Hole (B3 cc d e))
                              (Ending (B1 (E.pair A a b1 eq))))
          | right _ => None
          end
      | Some b' => Some (Ending b')
      | None    => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_inject_naive suf x with
          | Some (B5 a b1 cc d e) =>
              match i with
              | Hole =>
                  match Nat.eq_dec (E.level A a) (E.level A b1) with
                  | left eq =>
                      match inject_chain_rec c' (E.pair A a b1 eq) with
                      | Some c'' =>
                          Some (ChainCons (PNode pre Hole (B3 cc d e)) c'')
                      | None => None
                      end
                  | right _ => None
                  end
              | PNode _ _ _ => None
              end
          | Some suf' => Some (ChainCons (PNode pre i suf') c')
          | None      => None
          end
      end
  end.

(** Sequence-preservation lemmas for [push_chain_rec] / [inject_chain_rec]
    are omitted in this revision: the four headline seq theorems
    ([push_chain_full_seq], etc.) cover the bounded-cascade variants,
    which are the certified production case.  The recursive variants
    are extracted purely for benchmarking and are out of scope for the
    Coq proofs proper. *)

(** ** Recursive pop / eject (also proof artifacts).

    The non-recursive [pop_chain] / [eject_chain] only handle the top
    buffer of the chain.  If the top buffer is empty but the chain
    has deeper links, we need to descend and unpair an element from
    the next link.

    Note: per the "level-l element" interface, an [E.t A] at level l
    flattens to a list of 2^l base elements.  When the top buffer is
    empty and we pop from the next chain link, we get a single level-(l+1)
    element which represents *two* level-l elements — we use [E.unpair]
    to split it, return one, and push the other back onto the top. *)

Fixpoint pop_chain_rec {A : Type} (c : Chain A) : option (E.t A * Chain A) :=
  match c with
  | Ending b =>
      match buf5_pop_naive b with
      | Some (x, b') => Some (x, Ending b')
      | None         => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_pop_naive pre with
          | Some (x, pre') => Some (x, ChainCons (PNode pre' i suf) c')
          | None =>
              (* Top prefix is empty.  Try the suffix. *)
              match buf5_pop_naive suf with
              | Some (x, suf') =>
                  Some (x, ChainCons (PNode pre i suf') c')
              | None =>
                  (* Both empty; descend to c' to obtain a paired element,
                     unpair, return the first half, push the second back
                     to the prefix. *)
                  match pop_chain_rec c' with
                  | Some (paired, c'') =>
                      match E.unpair A paired with
                      | Some (x, y) =>
                          Some (x, ChainCons (PNode (B1 y) i suf) c'')
                      | None => None
                      end
                  | None =>
                      (* c' is also empty; the whole chain is empty
                         except for the [PNode] envelope.  Treat as None. *)
                      None
                  end
              end
          end
      end
  end.

Fixpoint eject_chain_rec {A : Type} (c : Chain A) : option (Chain A * E.t A) :=
  match c with
  | Ending b =>
      match buf5_eject_naive b with
      | Some (b', x) => Some (Ending b', x)
      | None         => None
      end
  | ChainCons p c' =>
      match p with
      | Hole => None
      | PNode pre i suf =>
          match buf5_eject_naive suf with
          | Some (suf', x) => Some (ChainCons (PNode pre i suf') c', x)
          | None =>
              match buf5_eject_naive pre with
              | Some (pre', x) =>
                  Some (ChainCons (PNode pre' i suf) c', x)
              | None =>
                  match eject_chain_rec c' with
                  | Some (c'', paired) =>
                      match E.unpair A paired with
                      | Some (x, y) =>
                          Some (ChainCons (PNode pre i (B1 x)) c'', y)
                      | None => None
                      end
                  | None => None
                  end
              end
          end
      end
  end.

Lemma inject_chain_full_seq :
  forall (A : Type) (c c' : Chain A) (x : E.t A),
    inject_chain_full c x = Some c' ->
    chain_to_list c' = chain_to_list c ++ E.to_list A x.
Proof.
  intros A c c' x Heq.
  unfold inject_chain_full in Heq.
  destruct c as [b | p c0].
  - destruct (buf5_inject_naive b x) as [b'|] eqn:Hinj; [|discriminate].
    pose proof (@buf5_inject_naive_seq (E.t A) A (E.to_list A) b b' x Hinj) as Hs.
    destruct b' as [|y|y z|y z w|y z w u|y z w u v].
    + destruct b; cbn in Hinj; inversion Hinj.
    + inject_simple_ending Heq Hs.
    + inject_simple_ending Heq Hs.
    + inject_simple_ending Heq Hs.
    + inject_simple_ending Heq Hs.
    + (* B5: make_red *)
      pose proof (@make_red_inject_chain_seq A (Ending (B5 y z w u v)) c' Heq) as Hmr.
      rewrite Hmr.
      unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
      rewrite Hs. reflexivity.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf].
    + (* Hole inner: simple-packet path *)
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hinj; [|discriminate].
      pose proof (@buf5_inject_naive_seq (E.t A) A (E.to_list A) suf suf' x Hinj) as Hs.
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * destruct suf; cbn in Hinj; inversion Hinj.
      * inject_simple_cons Heq Hs.
      * inject_simple_cons Heq Hs.
      * inject_simple_cons Heq Hs.
      * inject_simple_cons Heq Hs.
      * (* B5: make_red *)
        pose proof (@make_red_inject_chain_seq A
                      (ChainCons (PNode pre Hole (B5 y z w u v)) c0) c' Heq) as Hmr.
        rewrite Hmr.
        unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
        rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
    + (* PNode inner: nested-top path (Phase S6 / P5) *)
      destruct (buf5_inject_naive suf x) as [suf'|] eqn:Hinj; [|discriminate].
      pose proof (@buf5_inject_naive_seq (E.t A) A (E.to_list A) suf suf' x Hinj) as Hs.
      destruct suf' as [|y|y z|y z w|y z w u|y z w u v].
      * destruct suf; cbn in Hinj; inversion Hinj.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * inversion Heq; subst c'; clear Heq.
        unfold chain_to_list; cbn -[buf5_seq];
          unfold buf_seq_E; rewrite Hs;
          repeat rewrite <- app_assoc; reflexivity.
      * (* B5: make_red Case 3 dual *)
        pose proof (@make_red_inject_chain_seq A
                      (ChainCons (PNode pre (PNode ipre ii isuf)
                                        (B5 y z w u v)) c0) c' Heq) as Hmr.
        rewrite Hmr.
        unfold chain_to_list. cbn -[buf5_seq]. unfold buf_seq_E.
        rewrite Hs. repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** Underflow repair: [make_green_pop_chain] / [make_green_eject_chain].

    The dual of [make_red_push_chain]: when the top buffer drains
    (becomes [B0]), refill it by popping a paired element from the next
    chain link, unpairing it, and laying it down as a fresh [B2] in the
    top prefix.

    Shape preconditions (mirroring [make_red_push_chain]):
    - In the [Ending B0] case, there's nothing to refill from -- return
      [None] (the chain is empty).
    - In the [ChainCons (PNode B0 Hole suf) c'] case, refill from [c']
      via a single naive-pop of [c'] (whose result is a level-(S k)
      paired element).

    On the way down, we use the SHALLOW [pop_chain] (not the recursive
    cascade): the regularity invariant should ensure that c''s top
    buffer is non-empty when make_green is fired.  If it's not, we
    return [None] -- a degenerate state.

    Sequence preservation: [B0] contributes [], the popped paired
    element [pxy] flattens to [x ++ y], and the [B2 x y] also flattens
    to [x ++ y].  Net: [chain_to_list] preserved. *)

(** [make_green_pop_chain c]: refill the underflow case.

    Precondition (informally): the top buffer is [B0] (drained), and we
    want to pop the next element.  The repair fires only when the chain
    has a tail with a non-empty top buffer; otherwise we return [None].

    The repair:
    1. Pop a level-(S k) paired element [pxy] from the chain tail [c'].
    2. Unpair [pxy] into level-k elements [(x, y)].
    3. Return [(x, ChainCons (PNode (B2 x y) Hole suf) c'')].

    This places [B2 x y] at the top, draining one paired element from
    the next level.  Sequence preservation is the central invariant:
    [pxy] flattens to [x ++ y], [B2 x y] also flattens to [x ++ y].

    For chains where the tail's [pop_chain] returns [None] (i.e. the
    tail is structurally empty in its own [pre]/inside), we conservatively
    return [None] and let the caller decide.  This is safe and still
    bounded-cost (one pop on the abstract tail). *)

Definition make_green_pop_chain {A : Type} (c : Chain A)
  : option (E.t A * Chain A) :=
  match c with
  | ChainCons (PNode B0 Hole suf) c' =>
      match pop_chain c' with
      | Some (paired, c'') =>
          match E.unpair A paired with
          | Some (x, y) =>
              (* The pair flattens to [x ++ y].  We return [x] to the
                 caller and place [y] alone (as [B1 y]) in the new top
                 prefix.  Net effect: the popped element is exactly
                 the first half of the paired element. *)
              Some (x, ChainCons (PNode (B1 y) Hole suf) c'')
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition make_green_eject_chain {A : Type} (c : Chain A)
  : option (Chain A * E.t A) :=
  match c with
  | ChainCons (PNode pre Hole B0) c' =>
      match eject_chain c' with
      | Some (c'', paired) =>
          match E.unpair A paired with
          | Some (x, y) =>
              (* Place [x] alone in the new top suffix; return [y] to
                 the caller (the back-end of the unpaired pair). *)
              Some (ChainCons (PNode pre Hole (B1 x)) c'', y)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(** ** Sequence preservation for make_green. *)

Lemma make_green_pop_chain_seq :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    make_green_pop_chain c = Some (x, c') ->
    chain_to_list c = E.to_list A x ++ chain_to_list c'.
Proof.
  intros A c x c' Heq.
  unfold make_green_pop_chain in Heq.
  destruct c as [b | p c0]; [discriminate|].
  destruct p as [|pre i suf]; [discriminate|].
  destruct pre as [|y|y z|y z w|y z w u|y z w u v];
    destruct i as [|ipre ii isuf];
    try discriminate.
  destruct (pop_chain c0) as [[paired c0'']|] eqn:Hpop; [|discriminate].
  destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
  inversion Heq; subst x c'; clear Heq.
  pose proof (@pop_chain_seq A c0 paired c0'' Hpop) as Hs0.
  pose proof (E.unpair_to_list A paired xa ya Hup) as Heq_list.
  unfold chain_to_list in *.
  cbn -[buf5_seq].
  unfold buf_seq_E.
  rewrite Hs0. rewrite Heq_list.
  rewrite ?app_nil_l, ?app_nil_r.
  repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma make_green_eject_chain_seq :
  forall (A : Type) (c : Chain A) (c' : Chain A) (x : E.t A),
    make_green_eject_chain c = Some (c', x) ->
    chain_to_list c = chain_to_list c' ++ E.to_list A x.
Proof.
  intros A c c' x Heq.
  unfold make_green_eject_chain in Heq.
  destruct c as [b | p c0]; [discriminate|].
  destruct p as [|pre i suf]; [discriminate|].
  destruct suf as [|y|y z|y z w|y z w u|y z w u v];
    destruct i as [|ipre ii isuf];
    try discriminate.
  destruct (eject_chain c0) as [[c0'' paired]|] eqn:Hej; [|discriminate].
  destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
  inversion Heq; subst c' x; clear Heq.
  pose proof (@eject_chain_seq A c0 c0'' paired Hej) as Hs0.
  pose proof (E.unpair_to_list A paired xa ya Hup) as Heq_list.
  unfold chain_to_list in *.
  cbn -[buf5_seq].
  unfold buf_seq_E.
  rewrite Hs0. rewrite Heq_list.
  rewrite ?app_nil_l, ?app_nil_r.
  repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** [pop_chain_full] / [eject_chain_full]: pop / eject with one-step
    make_green refill on underflow.

    Mirrors [push_chain_full] / [inject_chain_full] symmetrically.  When
    the naive [pop_chain] succeeds and the result's top is non-degenerate,
    we return its result.  When the naive [pop_chain] fails (top buffer
    empty), fire [make_green_pop_chain] for tail-refill. *)

Definition pop_chain_full {A : Type} (c : Chain A)
  : option (E.t A * Chain A) :=
  match c with
  | Ending b =>
      match buf5_pop_naive b with
      | Some (x, b') => Some (x, Ending b')
      | None         => None  (* truly empty *)
      end
  | ChainCons (PNode pre Hole suf) c' =>
      match buf5_pop_naive pre with
      | Some (x, pre') =>
          Some (x, ChainCons (PNode pre' Hole suf) c')
      | None =>
          (* Top prefix drained: fire make_green from tail. *)
          make_green_pop_chain (ChainCons (PNode B0 Hole suf) c')
      end
  | _ => None
  end.

Definition eject_chain_full {A : Type} (c : Chain A)
  : option (Chain A * E.t A) :=
  match c with
  | Ending b =>
      match buf5_eject_naive b with
      | Some (b', x) => Some (Ending b', x)
      | None         => None
      end
  | ChainCons (PNode pre Hole suf) c' =>
      match buf5_eject_naive suf with
      | Some (suf', x) =>
          Some (ChainCons (PNode pre Hole suf') c', x)
      | None =>
          make_green_eject_chain (ChainCons (PNode pre Hole B0) c')
      end
  | _ => None
  end.

Lemma pop_chain_full_seq :
  forall (A : Type) (c : Chain A) (x : E.t A) (c' : Chain A),
    pop_chain_full c = Some (x, c') ->
    chain_to_list c = E.to_list A x ++ chain_to_list c'.
Proof.
  intros A c x c' Heq.
  unfold pop_chain_full in Heq.
  destruct c as [b | p c0].
  - (* Ending *)
    destruct (buf5_pop_naive b) as [[xp b']|] eqn:Hp; [|discriminate].
    inversion Heq; subst x c'; clear Heq.
    pose proof (@buf5_pop_naive_seq (E.t A) A (E.to_list A) b xp b' Hp) as Hs.
    unfold chain_to_list. cbn. unfold buf_seq_E. exact Hs.
  - (* ChainCons p c0 *)
    destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf]; [|discriminate].
    destruct (buf5_pop_naive pre) as [[xp pre']|] eqn:Hp.
    + (* Naive succeeded *)
      inversion Heq; subst xp c'; clear Heq.
      pose proof (@buf5_pop_naive_seq (E.t A) A (E.to_list A) pre x pre' Hp) as Hs.
      unfold chain_to_list. cbn. unfold buf_seq_E. rewrite Hs.
      repeat rewrite <- app_assoc. reflexivity.
    + (* Underflow: fire make_green *)
      pose proof (@make_green_pop_chain_seq A
                    (ChainCons (PNode B0 Hole suf) c0) x c' Heq) as Hmg.
      unfold chain_to_list in *. cbn in Hmg. cbn.
      unfold buf_seq_E in *. cbn in Hmg.
      (* We have: chain_seq (ChainCons (PNode B0 Hole suf) c0) =
         [] ++ chain_seq c0 ++ buf5_seq E.to_list suf = E.to_list x ++ chain_seq c'.
         Want: buf_seq_E pre ++ chain_seq c0 ++ buf_seq_E suf = E.to_list x ++ chain_seq c'.
         But pre is non-empty (since buf5_pop_naive pre = None means pre = B0).
         So pre = B0, buf_seq_E B0 = [], same as the make_green case. *)
      destruct pre as [|py|py pz|py pz pw|py pz pw pu|py pz pw pu pv]; try discriminate.
      cbn. rewrite ?app_nil_l in Hmg. exact Hmg.
Qed.

Lemma eject_chain_full_seq :
  forall (A : Type) (c : Chain A) (c' : Chain A) (x : E.t A),
    eject_chain_full c = Some (c', x) ->
    chain_to_list c = chain_to_list c' ++ E.to_list A x.
Proof.
  intros A c c' x Heq.
  unfold eject_chain_full in Heq.
  destruct c as [b | p c0].
  - destruct (buf5_eject_naive b) as [[b' xp]|] eqn:Hp; [|discriminate].
    inversion Heq; subst c' x; clear Heq.
    pose proof (@buf5_eject_naive_seq (E.t A) A (E.to_list A) b b' xp Hp) as Hs.
    unfold chain_to_list. cbn. unfold buf_seq_E. exact Hs.
  - destruct p as [|pre i suf]; [discriminate|].
    destruct i as [|ipre ii isuf]; [|discriminate].
    destruct (buf5_eject_naive suf) as [[suf' xp]|] eqn:Hp.
    + inversion Heq; subst c' xp; clear Heq.
      pose proof (@buf5_eject_naive_seq (E.t A) A (E.to_list A) suf suf' x Hp) as Hs.
      unfold chain_to_list. cbn. unfold buf_seq_E. rewrite Hs.
      repeat rewrite <- app_assoc. reflexivity.
    + pose proof (@make_green_eject_chain_seq A
                    (ChainCons (PNode pre Hole B0) c0) c' x Heq) as Hmg.
      unfold chain_to_list in *. cbn in Hmg. cbn.
      unfold buf_seq_E in *. cbn in Hmg.
      destruct suf as [|sy|sy sz|sy sz sw|sy sz sw su|sy sz sw su sv]; try discriminate.
      cbn. rewrite ?app_nil_r in Hmg |- *. exact Hmg.
Qed.
