(** * KTDeque.Catenable.Ops — §6 operations, part 1: push / inject.

    KT99 §6.2 (kb/spec/section6-catenable-deques.md): push receives at the
    deque's LEFT or ONLY triple — in this encoding, the head node of the top
    packet (the first triple of the top preferred path) — and pushes onto its
    prefix (suffix if the prefix is empty, the childless one-sided case).
    Inject is the mirror.

    Pushing raises a buffer size, so colours only move toward green; the
    resulting path-decomposition surgery (KT99 Lemma 6.1: a push "adds t to or
    deletes t from the front of a preferred path") is driven by the
    RECOMPUTED colour (an only-node's min may not move), and is the same for
    push and inject, so one worker [pkt_update] serves both:

    - head was a body node, new colour green (Y->G):  the head leaves the
      run and becomes its own green packet; the rest of the run is the new
      top of the chain below.  For a yellow PAIR head, its two subtrees
      become a [CPair].
    - head was an orange PAIR node, new colour yellow (O->Y): the preference
      flips from right to left — the parked (green-path) left tree is inlined
      as the new continuation and the old continuation is parked as the
      right tree.  An orange SINGLE-child head needs no surgery (yellow
      prefers the only child too).
    - head was the packet's terminal node (body = BHole, colour G or R):
      G stays G (no surgery); R may become orange (R->O), which merges the
      node into the head of its child packet (the body grows at the front).

    Cost note (memo, Decision 4): each operation performs O(1) buffer
    primitives and touches O(1) nodes/packets — the surgeries only rearrange
    constructors at the top. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color.

Set Implicit Arguments.

(* ========================================================================== *)
(* Buffer-level receivers.                                                     *)
(* ========================================================================== *)

Definition node_push {A : Type} (s : stored A) (n : cnode A) : cnode A :=
  match n with
  | Node k [] suf => Node k [] (s :: suf)
  | Node k p suf => Node k (s :: p) suf
  end.

Definition node_inject {A : Type} (n : cnode A) (s : stored A) : cnode A :=
  match n with
  | Node k p [] => Node k (p ++ [s]) []
  | Node k p suf => Node k p (suf ++ [s])
  end.

(* ========================================================================== *)
(* The shared top-of-packet update with colour-driven surgery.                 *)
(* ========================================================================== *)

(** Decompose a packet over its following chain into (root triple's node,
    root's child deque).  The body/packet bundling is exactly the path
    decomposition, so this is O(1) constructor surgery. *)
Definition root_and_child {A : Type}
    (p : cpacket A) (rest : cchain A) : cnode A * cchain A :=
  match p with
  | Pkt BHole n => (n, rest)
  | Pkt (BSingle hn b') n => (hn, CSingle (Pkt b' n) rest)
  | Pkt (BPairY hn b' rc) n => (hn, CPair (CSingle (Pkt b' n) rest) rc)
  | Pkt (BPairO hn lc b') n => (hn, CPair lc (CSingle (Pkt b' n) rest))
  end.

(** Rebuild a tree from a root node and its child deque, re-bundling the
    preferred path per the root's (computed) colour: green/red roots head
    their own packet; a yellow root prepends to its left/only child's
    packet; an orange root to its right/only child's.  The catch-all arms
    are unreachable under [J] (a coloured pair root always has the
    single-tree children the colour demands). *)
Definition tree_of {A : Type} (n : cnode A) (child : cchain A) : cchain A :=
  match node_color (chain_has_node child) n with
  | CG | CR => CSingle (Pkt BHole n) child
  | CY =>
      match child with
      | CSingle (Pkt rb rn) rrest => CSingle (Pkt (BSingle n rb) rn) rrest
      | CPair (CSingle (Pkt lb ln) lrest) r =>
          CSingle (Pkt (BPairY n lb r) ln) lrest
      | _ => CSingle (Pkt BHole n) child
      end
  | CO =>
      match child with
      | CSingle (Pkt rb rn) rrest => CSingle (Pkt (BSingle n rb) rn) rrest
      | CPair l (CSingle (Pkt rb rn) rrest) =>
          CSingle (Pkt (BPairO n l rb) rn) rrest
      | _ => CSingle (Pkt BHole n) child
      end
  end.

(** Updating the root triple = unpack, update, re-bundle. *)
Definition pkt_update {A : Type}
    (upd : cnode A -> cnode A) (p : cpacket A) (rest : cchain A) : cchain A :=
  let '(n, child) := root_and_child p rest in
  tree_of (upd n) child.

(* ========================================================================== *)
(* push / inject.                                                              *)
(* ========================================================================== *)

(** The level-generic workers move whole [stored] elements; the public ops
    wrap a raw element as [SGround].  (Concat and the pop/eject repair reuse
    the workers at inner levels with [SSmall]/[SBig] elements.) *)

Fixpoint push_chain {A : Type} (s : stored A) (c : cchain A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly [s] [])) CEmpty
  | CSingle p rest => pkt_update (node_push s) p rest
  | CPair l r => CPair (push_chain s l) r
  end.

Fixpoint inject_chain {A : Type} (c : cchain A) (s : stored A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly [] [s])) CEmpty
  | CSingle p rest => pkt_update (fun n => node_inject n s) p rest
  | CPair l r => CPair l (inject_chain r s)
  end.

Definition cad_push {A : Type} (x : A) (d : cadeque A) : cadeque A :=
  push_chain (SGround x) d.

Definition cad_inject {A : Type} (d : cadeque A) (x : A) : cadeque A :=
  inject_chain d (SGround x).

(* ========================================================================== *)
(* Sanity examples (sequence behaviour, including a surgery case).             *)
(* ========================================================================== *)

Example cad_push_two :
  cad_to_list (cad_push 1 (cad_push 2 cad_empty)) = [1; 2].
Proof. reflexivity. Qed.

Example cad_inject_two :
  cad_to_list (cad_inject (cad_inject cad_empty 1) 2) = [1; 2].
Proof. reflexivity. Qed.

Example cad_push_inject_mix :
  cad_to_list (cad_inject (cad_push 1 (cad_inject cad_empty 2)) 3)
  = [1; 2; 3].
Proof. reflexivity. Qed.

(** A Y->G split: a yellow only-triple head (7/7 with a child) goes green and
    leaves the run.  Sequence is preserved across the surgery. *)
Example pkt_update_split_seq :
  let n7 := Node KOnly
              [SGround 1; SGround 2; SGround 3; SGround 4; SGround 5;
               SGround 6; SGround 7]
              [SGround 21; SGround 22; SGround 23; SGround 24; SGround 25;
               SGround 26; SGround 27] in
  let nend := Node KOnly
                [SSmall [SGround 11; SGround 12; SGround 13]]
                [SSmall [SGround 14; SGround 15; SGround 16]] in
  cchain_seq (push_chain (SGround 0)
                (CSingle (Pkt (BSingle n7 BHole) nend) CEmpty))
  = 0 :: cchain_seq (CSingle (Pkt (BSingle n7 BHole) nend) CEmpty).
Proof. reflexivity. Qed.
