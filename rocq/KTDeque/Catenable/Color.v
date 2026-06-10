(** * KTDeque.Catenable.Color — computed GYOR colours and the invariant [J].

    KT99 §6.1 made extrinsic (kb/spec/section6-catenable-deques.md is the
    transcription; kb/spec/catenable-type-design.md the design memo).

    Colours are COMPUTED from buffer sizes — there are no colour tags, so the
    tag/shape mismatch class that the deque keystone's [colors_consistent]
    had to police cannot exist here.

    [J] bundles, per the memo:
    1. shape/kind correctness (body preference discipline, pair shapes);
    2. size floors per triple kind;
    3. §6 regularity (red packet => green child chain; orange's nonpreferred
       child => green path; top-level paths green via [chain_ends_green]).

    Deliberate simplification vs the memo: NO level-stratification clause in
    [J] v1.  Unlike the deque (where [E.pair]/[E.unpair] made levels
    load-bearing for totality), §6's operations only move whole [stored]
    elements between same-level buffers and never re-pair across levels, so
    no obligation should need stratification.  If discharge surfaces one, the
    clause is added here in place (methodology: refine the one invariant). *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model.

Set Implicit Arguments.

(* ========================================================================== *)
(* Colours.                                                                    *)
(* ========================================================================== *)

Inductive gyor : Type := CG | CY | CO | CR.

Definition node_kind {A : Type} (n : cnode A) : kind :=
  match n with Node k _ _ => k end.

(** §6.1 colour table.  A childless triple (and every stored triple) is
    green.  With a child: a left triple is coloured by its prefix size
    (>=8 G, 7 Y, 6 O, 5 R), a right triple by its suffix size, an only
    triple by the min of the two. *)
Definition node_color {A : Type} (has_child : bool) (n : cnode A) : gyor :=
  if negb has_child then CG
  else
    match n with
    | Node k p s =>
        let m :=
          match k with
          | KLeft => length p
          | KRight => length s
          | KOnly => Nat.min (length p) (length s)
          end
        in
        if 8 <=? m then CG
        else if m =? 7 then CY
        else if m =? 6 then CO
        else CR
    end.

(* ========================================================================== *)
(* Size floors (§6.1).                                                         *)
(* ========================================================================== *)

(** Only triple: >=5/>=5; childless only triples may instead be one-sided
    nonempty.  Left: prefix >=5, suffix exactly 2.  Right symmetric. *)
Definition node_sizes {A : Type} (has_child : bool) (n : cnode A) : Prop :=
  match n with
  | Node KOnly p s =>
      (5 <= length p /\ 5 <= length s) \/
      (has_child = false /\
       ((p = [] /\ 1 <= length s) \/ (s = [] /\ 1 <= length p)))
  | Node KLeft p s => 5 <= length p /\ length s = 2
  | Node KRight p s => length p = 2 /\ 5 <= length s
  end.

(** Shape test used to keep [chain_wf]'s recursion guard-safe at [CPair]
    and at parked body chains: a (sub)tree must be a single-packet chain. *)
Definition is_single {A : Type} (c : cchain A) : bool :=
  match c with CSingle _ _ => true | _ => false end.

Definition chain_has_node {A : Type} (c : cchain A) : bool :=
  match c with CEmpty => false | _ => true end.

(** The kind reached at the end of a preferred run: a single-child step
    descends to the only child; a yellow pair prefers its LEFT child; an
    orange pair its RIGHT child (§6.1). *)
Fixpoint body_out_kind {A : Type} (k : kind) (b : cbody A) : kind :=
  match b with
  | BHole => k
  | BSingle _ b' => body_out_kind KOnly b'
  | BPairY _ b' _ => body_out_kind KLeft b'
  | BPairO _ _ b' => body_out_kind KRight b'
  end.

(* ========================================================================== *)
(* The invariant [J], as one mutual structural predicate family.               *)
(* ========================================================================== *)

Fixpoint stored_wf {A : Type} (s : stored A) : Prop :=
  match s with
  | SGround _ => True
  | SSmall b =>
      3 <= length b /\
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_wf x /\ all r
         end) b
  | SBig p c q =>
      3 <= length p /\ 3 <= length q /\
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_wf x /\ all r
         end) p /\
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_wf x /\ all r
         end) q /\
      chain_wf KOnly c
  end
with cnode_wf {A : Type} (n : cnode A) : Prop :=
  match n with
  | Node _ p s =>
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_wf x /\ all r
         end) p /\
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_wf x /\ all r
         end) s
  end
with cbody_wf {A : Type} (k : kind) (b : cbody A) : Prop :=
  match b with
  | BHole => True
  | BSingle n b' =>
      node_kind n = k /\
      node_sizes true n /\
      cnode_wf n /\
      (node_color true n = CY \/ node_color true n = CO) /\
      cbody_wf KOnly b'
  | BPairY n b' rc =>
      node_kind n = k /\
      node_sizes true n /\
      cnode_wf n /\
      node_color true n = CY /\
      is_single rc = true /\
      chain_wf KRight rc /\
      cbody_wf KLeft b'
  | BPairO n lc b' =>
      node_kind n = k /\
      node_sizes true n /\
      cnode_wf n /\
      node_color true n = CO /\
      is_single lc = true /\
      chain_wf KLeft lc /\
      chain_ends_green lc /\
      cbody_wf KRight b'
  end
with chain_wf {A : Type} (k : kind) (c : cchain A) : Prop :=
  match c with
  | CEmpty => True
  | CSingle (Pkt b n) rest =>
      cbody_wf k b /\
      node_kind n = body_out_kind k b /\
      node_sizes (chain_has_node rest) n /\
      cnode_wf n /\
      (node_color (chain_has_node rest) n = CG \/
       (node_color (chain_has_node rest) n = CR /\ chain_ends_green rest)) /\
      chain_wf KOnly rest
  | CPair l r =>
      is_single l = true /\ is_single r = true /\
      chain_wf KLeft l /\ chain_wf KRight r
  end
with chain_ends_green {A : Type} (c : cchain A) : Prop :=
  match c with
  | CEmpty => True
  | CSingle (Pkt _ n) rest =>
      node_color (chain_has_node rest) n = CG
  | CPair l r => chain_ends_green l /\ chain_ends_green r
  end.

(* ========================================================================== *)
(* Level stratification (J v2, grown in place for pop/eject).                  *)
(*                                                                              *)
(* A node at level k holds level-k stored cells in its buffers; its child      *)
(* chain's roots sit at level k+1; a packet's tail node sits body_depth        *)
(* levels below its head (each body step descends one level).  SGround is      *)
(* exactly the level-0 cell — this is what makes [cad_pop]'s SGround match     *)
(* total on regular inputs.  A level-(k+1) cell contains level-k cells, so     *)
(* repair's buffer splices (child cell contents into the parent's buffers)     *)
(* are level-correct by construction.                                          *)
(* ========================================================================== *)

Fixpoint body_depth {A : Type} (b : cbody A) : nat :=
  match b with
  | BHole => 0
  | BSingle _ b' => S (body_depth b')
  | BPairY _ b' _ => S (body_depth b')
  | BPairO _ _ b' => S (body_depth b')
  end.

Fixpoint stored_leveled {A : Type} (k : nat) (s : stored A) : Prop :=
  match s with
  | SGround _ => k = 0
  | SSmall b =>
      match k with
      | 0 => False
      | S k' =>
          (fix all (l : list (stored A)) : Prop :=
             match l with
             | [] => True
             | x :: r => stored_leveled k' x /\ all r
             end) b
      end
  | SBig p c q =>
      match k with
      | 0 => False
      | S k' =>
          (fix all (l : list (stored A)) : Prop :=
             match l with
             | [] => True
             | x :: r => stored_leveled k' x /\ all r
             end) p /\
          (fix all (l : list (stored A)) : Prop :=
             match l with
             | [] => True
             | x :: r => stored_leveled k' x /\ all r
             end) q /\
          chain_leveled (S k') c
      end
  end
with cnode_leveled {A : Type} (k : nat) (n : cnode A) : Prop :=
  match n with
  | Node _ p s =>
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_leveled k x /\ all r
         end) p /\
      (fix all (l : list (stored A)) : Prop :=
         match l with
         | [] => True
         | x :: r => stored_leveled k x /\ all r
         end) s
  end
with cbody_leveled {A : Type} (k : nat) (b : cbody A) : Prop :=
  match b with
  | BHole => True
  | BSingle n b' => cnode_leveled k n /\ cbody_leveled (S k) b'
  | BPairY n b' rc =>
      cnode_leveled k n /\ cbody_leveled (S k) b' /\
      chain_leveled (S k) rc
  | BPairO n lc b' =>
      cnode_leveled k n /\ chain_leveled (S k) lc /\
      cbody_leveled (S k) b'
  end
with chain_leveled {A : Type} (k : nat) (c : cchain A) : Prop :=
  match c with
  | CEmpty => True
  | CSingle (Pkt b n) rest =>
      cbody_leveled k b /\
      cnode_leveled (k + body_depth b) n /\
      chain_leveled (S (k + body_depth b)) rest
  | CPair l r => chain_leveled k l /\ chain_leveled k r
  end.

(** §6 regularity, packaged: a catenable deque is semiregular by [chain_wf]
    (red packets force green child chains; orange's parked child is a green
    path), REGULAR when additionally every top-level preferred path is
    green ([chain_ends_green]), and stratified ([chain_leveled 0]) so that
    the elements reachable at the top are exactly the [SGround]s. *)
Definition J {A : Type} (d : cadeque A) : Prop :=
  chain_wf KOnly d /\ chain_ends_green d /\ chain_leveled 0 d.

(* ========================================================================== *)
(* Basic facts.                                                                *)
(* ========================================================================== *)

Lemma empty_J : forall A, J (@cad_empty A).
Proof. intros A. split; [cbn; exact I | split; cbn; exact I]. Qed.

(** A childless node is green, whatever its buffers. *)
Lemma node_color_no_child :
  forall A (n : cnode A), node_color false n = CG.
Proof. intros A n. reflexivity. Qed.

(** Sanity: the singleton from Model.v satisfies [J]. *)
Example singleton_J :
  J (CSingle (Pkt BHole (Node KOnly [SGround 7] [])) CEmpty).
Proof.
  unfold J; cbn.
  repeat split.
  - right. split; [reflexivity|]. right. split; [reflexivity|]. cbn. lia.
  - left. reflexivity.
Qed.
