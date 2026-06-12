(** * KTDeque.Catenable.OpsFused — verified program transformations.

    Coq-level optimizations of the OpsFast.v family, each proved EQUAL
    to the function it replaces (so the keystone transfers verbatim and
    the extracted artifact stays theorem-backed):

    1. [upd_pkt] — case-of-case fusion of
       [pkt_update_f upd = root_and_child ; tree_of_f]: the
       intermediate (node, child) pair vanishes, and in each body arm
       the just-built child chain is matched AGAINST A KNOWN
       CONSTRUCTOR, so the Y/O absorb arms deforest the child cell
       entirely (the [BSingle]/[BPairY]/[BPairO] preferred-path arms
       allocate the result directly instead of building the child and
       immediately tearing it down).

    2. [tree_repair] — deforestation of [repair_*_side_f ∘ tree_of_f]:
       pop/eject build a tree whose top packet the repair pass
       immediately destructs, re-colours and re-allocates.  Fused, the
       repair decision happens where the colour is FIRST computed —
       the G/R/fallback arms skip the second colour computation and
       the duplicate [CSingle] allocation.

    3. [cad_pop_v2]/[cad_eject_v2] — single-tree removal fused with
       its repair (childless rebuilds skip repair outright, justified
       by [repair_packet_childless]); the rarer pair-rooted path
       delegates to the proven composition. *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast.

Set Implicit Arguments.

(* ========================================================================== *)
(* 1. Fused packet update (push / inject).                                     *)
(* ========================================================================== *)

Definition upd_pkt {A : Type} (upd : cnode A -> cnode A)
    (p : cpacket A) (rest : cchain A) : cchain A :=
  match p with
  | Pkt BHole n => tree_of_f (upd n) rest
  | Pkt (BSingle hn b') n =>
      let hn' := upd hn in
      match node_color_f true hn' with
      | CG | CR => CSingle (Pkt BHole hn') (CSingle (Pkt b' n) rest)
      | CY | CO => CSingle (Pkt (BSingle hn' b') n) rest
      end
  | Pkt (BPairY hn b' rc) n =>
      let hn' := upd hn in
      match node_color_f true hn' with
      | CG | CR =>
          CSingle (Pkt BHole hn') (CPair (CSingle (Pkt b' n) rest) rc)
      | CY => CSingle (Pkt (BPairY hn' b' rc) n) rest
      | CO =>
          match rc with
          | CSingle (Pkt rb rn) rrest =>
              CSingle (Pkt (BPairO hn' (CSingle (Pkt b' n) rest) rb) rn)
                rrest
          | _ =>
              CSingle (Pkt BHole hn') (CPair (CSingle (Pkt b' n) rest) rc)
          end
      end
  | Pkt (BPairO hn lc b') n =>
      let hn' := upd hn in
      match node_color_f true hn' with
      | CG | CR =>
          CSingle (Pkt BHole hn') (CPair lc (CSingle (Pkt b' n) rest))
      | CO => CSingle (Pkt (BPairO hn' lc b') n) rest
      | CY =>
          match lc with
          | CSingle (Pkt lb ln) lrest =>
              CSingle (Pkt (BPairY hn' lb (CSingle (Pkt b' n) rest)) ln)
                lrest
          | _ =>
              CSingle (Pkt BHole hn') (CPair lc (CSingle (Pkt b' n) rest))
          end
      end
  end.

Lemma upd_pkt_eq : forall A (upd : cnode A -> cnode A) p rest,
    upd_pkt upd p rest = pkt_update_f upd p rest.
Proof.
  intros A upd [b n] rest.
  destruct b as [| hn b' | hn b' rc | hn lc b'];
    cbn [upd_pkt pkt_update_f root_and_child]; unfold tree_of_f.
  - reflexivity.
  - cbn [chain_has_node];
      destruct (node_color_f true (upd hn)); reflexivity.
  - cbn [chain_has_node];
      destruct (node_color_f true (upd hn)); try reflexivity;
      destruct rc as [| [rb rn] rrest |]; reflexivity.
  - cbn [chain_has_node];
      destruct (node_color_f true (upd hn)); try reflexivity;
      destruct lc as [| [lb ln] lrest |]; reflexivity.
Qed.

Fixpoint push_chain_v2 {A : Type} (s : stored A) (c : cchain A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly (b1 s) bempty)) CEmpty
  | CSingle p rest => upd_pkt (node_push_f s) p rest
  | CPair l r => CPair (push_chain_v2 s l) r
  end.

Lemma push_chain_v2_eq : forall A (s : stored A) c,
    push_chain_v2 s c = push_chain_f s c.
Proof.
  intros A s c. revert s.
  induction c as [| p rest _ | l IHl r _]; intros s; cbn.
  - reflexivity.
  - apply upd_pkt_eq.
  - rewrite IHl. reflexivity.
Qed.

Fixpoint inject_chain_v2 {A : Type} (c : cchain A) (s : stored A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly bempty (b1 s))) CEmpty
  | CSingle p rest => upd_pkt (fun n => node_inject_f n s) p rest
  | CPair l r => CPair l (inject_chain_v2 r s)
  end.

Lemma inject_chain_v2_eq : forall A (c : cchain A) (s : stored A),
    inject_chain_v2 c s = inject_chain_f c s.
Proof.
  intros A c. induction c as [| p rest _ | l _ r IHr]; intros s; cbn.
  - reflexivity.
  - apply upd_pkt_eq.
  - rewrite IHr. reflexivity.
Qed.

Definition cad_push_v2 {A : Type} (x : A) (d : cadeque A) : cadeque A :=
  push_chain_v2 (SGround x) d.

Lemma cad_push_v2_eq : forall A (x : A) d, cad_push_v2 x d = cad_push_f x d.
Proof. intros. apply push_chain_v2_eq. Qed.

Definition cad_inject_v2 {A : Type} (d : cadeque A) (x : A) : cadeque A :=
  inject_chain_v2 d (SGround x).

Lemma cad_inject_v2_eq : forall A (d : cadeque A) x,
    cad_inject_v2 d x = cad_inject_f d x.
Proof. intros. apply inject_chain_v2_eq. Qed.

(* ========================================================================== *)
(* 2. Fused removal + repair.                                                  *)
(* ========================================================================== *)

(** A childless rebuild never needs repair: it is empty or a childless
    (hence green) single node. *)
Lemma repair_packet_childless : forall A (n : cnode A),
    repair_packet_f (Pkt BHole n) CEmpty = Some (CSingle (Pkt BHole n) CEmpty).
Proof. reflexivity. Qed.

Lemma repair_pop_side_rebuild : forall A (n : cnode A),
    repair_pop_side_f (rebuild_childless_f n) = Some (rebuild_childless_f n).
Proof.
  intros A [k p s].
  unfold rebuild_childless_f.
  destruct (bis_empty p && bis_empty s); [reflexivity|].
  destruct k;
    [destruct (bis_empty p || bis_empty s); [reflexivity|];
     destruct ((bsize p <? 5) || (bsize s <? 5)); reflexivity
    | reflexivity | reflexivity].
Qed.

Lemma repair_eject_side_rebuild : forall A (n : cnode A),
    repair_eject_side_f (rebuild_childless_f n) = Some (rebuild_childless_f n).
Proof.
  intros A [k p s].
  unfold rebuild_childless_f.
  destruct (bis_empty p && bis_empty s); [reflexivity|].
  destruct k;
    [destruct (bis_empty p || bis_empty s); [reflexivity|];
     destruct ((bsize p <? 5) || (bsize s <? 5)); reflexivity
    | reflexivity | reflexivity].
Qed.

(** [tree_repair n child] = repair of [tree_of_f n child], with the
    rebundle and the repair decision fused: the root colour is computed
    once, the G/R/fallback arms skip the duplicate packet teardown and
    [CSingle] re-allocation, and only the absorb arms (whose terminal
    colour is genuinely unknown) delegate to the full repair check. *)
Definition tree_repair {A : Type} (n : cnode A) (child : cchain A)
    : option (cchain A) :=
  match node_color_f (chain_has_node child) n with
  | CG => Some (CSingle (Pkt BHole n) child)
  | CR =>
      match n with
      | Node KLeft p1 s1 => repair_front_f KLeft BHole p1 s1 child
      | Node KRight p1 s1 => repair_back_f KRight BHole p1 s1 child
      | Node KOnly p1 s1 =>
          if 8 <=? bsize s1 then repair_front_f KOnly BHole p1 s1 child
          else if 8 <=? bsize p1 then repair_back_f KOnly BHole p1 s1 child
          else repair_both_f BHole p1 s1 child
      end
  | CY =>
      match child with
      | CSingle (Pkt rb rn) rrest =>
          repair_packet_f (Pkt (BSingle n rb) rn) rrest
      | CPair (CSingle (Pkt lb ln) lrest) r =>
          repair_packet_f (Pkt (BPairY n lb r) ln) lrest
      | _ => Some (CSingle (Pkt BHole n) child)
      end
  | CO =>
      match child with
      | CSingle (Pkt rb rn) rrest =>
          repair_packet_f (Pkt (BSingle n rb) rn) rrest
      | CPair l (CSingle (Pkt rb rn) rrest) =>
          repair_packet_f (Pkt (BPairO n l rb) rn) rrest
      | _ => Some (CSingle (Pkt BHole n) child)
      end
  end.

Lemma tree_repair_pop_eq : forall A (n : cnode A) child,
    tree_repair n child = repair_pop_side_f (tree_of_f n child).
Proof.
  intros A n child.
  unfold tree_repair, tree_of_f.
  destruct (node_color_f (chain_has_node child) n) eqn:Hc.
  - (* CG: identity both sides; the repair recheck rewrites with Hc *)
    cbn [repair_pop_side_f repair_packet_f]. rewrite Hc. reflexivity.
  - (* CY *)
    destruct child as [| [rb rn] rrest | l r].
    + cbn [chain_has_node] in Hc.
      cbn [repair_pop_side_f repair_packet_f chain_has_node].
      rewrite Hc. reflexivity.
    + cbn [repair_pop_side_f]. reflexivity.
    + cbn [chain_has_node] in Hc.
      destruct l as [| [lb ln] lrest |].
      * cbn [repair_pop_side_f repair_packet_f chain_has_node].
        rewrite Hc. reflexivity.
      * cbn [repair_pop_side_f]. reflexivity.
      * cbn [repair_pop_side_f repair_packet_f chain_has_node].
        rewrite Hc. reflexivity.
  - (* CO *)
    destruct child as [| [rb rn] rrest | l r].
    + cbn [chain_has_node] in Hc.
      cbn [repair_pop_side_f repair_packet_f chain_has_node].
      rewrite Hc. reflexivity.
    + cbn [repair_pop_side_f]. reflexivity.
    + cbn [chain_has_node] in Hc.
      destruct r as [| [rb rn] rrest |].
      * cbn [repair_pop_side_f repair_packet_f chain_has_node].
        rewrite Hc. reflexivity.
      * cbn [repair_pop_side_f]. reflexivity.
      * cbn [repair_pop_side_f repair_packet_f chain_has_node].
        rewrite Hc. reflexivity.
  - (* CR: both sides dispatch on the kind with body = BHole *)
    cbn [repair_pop_side_f repair_packet_f]. rewrite Hc.
    destruct n as [k p1 s1]; destruct k; reflexivity.
Qed.

Lemma tree_repair_eject_eq : forall A (n : cnode A) child,
    tree_repair n child = repair_eject_side_f (tree_of_f n child).
Proof.
  intros A n child.
  rewrite tree_repair_pop_eq.
  unfold tree_of_f.
  destruct (node_color_f (chain_has_node child) n);
    [reflexivity | | | reflexivity].
  - destruct child as [| [rb rn] rrest | l r]; try reflexivity.
    destruct l as [| [lb ln] lrest |]; reflexivity.
  - destruct child as [| [rb rn] rrest | l r]; try reflexivity.
    destruct r as [| [rb rn] rrest |]; reflexivity.
Qed.

Definition cad_pop_v2 {A : Type} (d : cadeque A) : option (A * cadeque A) :=
  match d with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_pop_f n with
      | Some (SGround a, n') =>
          match child with
          | CEmpty => Some (a, rebuild_childless_f n')
          | _ =>
              match tree_repair n' child with
              | Some d'' => Some (a, d'')
              | None => None
              end
          end
      | _ => None
      end
  | CPair _ _ =>
      (* pair-rooted top: the rarer path; the proven composition *)
      match pop_raw_f d with
      | Some (SGround x, d') =>
          match repair_pop_side_f d' with
          | Some d'' => Some (x, d'')
          | None => None
          end
      | _ => None
      end
  end.

Lemma cad_pop_v2_eq : forall A (d : cadeque A), cad_pop_v2 d = cad_pop_f d.
Proof.
  intros A d.
  unfold cad_pop_v2, cad_pop_f.
  destruct d as [| p rest | l r]; [reflexivity | | reflexivity].
  cbn [pop_raw_f].
  destruct (root_and_child p rest) as [n child].
  destruct (node_pop_f n) as [[x n']|]; [|reflexivity].
  destruct x as [a | bb | pp dd ss].
  - destruct child.
    + rewrite repair_pop_side_rebuild. reflexivity.
    + rewrite tree_repair_pop_eq. reflexivity.
    + rewrite tree_repair_pop_eq. reflexivity.
  - destruct child; reflexivity.
  - destruct child; reflexivity.
Qed.

Definition cad_eject_v2 {A : Type} (d : cadeque A) : option (cadeque A * A) :=
  match d with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_eject_f n with
      | Some (n', SGround a) =>
          match child with
          | CEmpty => Some (rebuild_childless_f n', a)
          | _ =>
              match tree_repair n' child with
              | Some d'' => Some (d'', a)
              | None => None
              end
          end
      | _ => None
      end
  | CPair _ _ =>
      match eject_raw_f d with
      | Some (d', SGround x) =>
          match repair_eject_side_f d' with
          | Some d'' => Some (d'', x)
          | None => None
          end
      | _ => None
      end
  end.

Lemma cad_eject_v2_eq : forall A (d : cadeque A), cad_eject_v2 d = cad_eject_f d.
Proof.
  intros A d.
  unfold cad_eject_v2, cad_eject_f.
  destruct d as [| p rest | l r]; [reflexivity | | reflexivity].
  cbn [eject_raw_f].
  destruct (root_and_child p rest) as [n child].
  destruct (node_eject_f n) as [[n' x]|]; [|reflexivity].
  destruct x as [a | bb | pp dd ss].
  - destruct child.
    + rewrite repair_eject_side_rebuild. reflexivity.
    + rewrite tree_repair_eject_eq. reflexivity.
    + rewrite tree_repair_eject_eq. reflexivity.
  - destruct child; reflexivity.
  - destruct child; reflexivity.
Qed.
