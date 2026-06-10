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

(* ========================================================================== *)
(* Concat (KT99 §6.2, Cases 1–4 with subcases 1a–1d).                          *)
(*                                                                            *)
(* Every element movement below is CONSTANT-bounded (combine two 2-buffers,   *)
(* eject/pop two, move at most 8): the §6 concat never appends two unbounded  *)
(* buffers.  [option] marks the size side conditions; under [J] every [None]  *)
(* arm is unreachable (a keystone obligation).                                *)
(* ========================================================================== *)

(** Pop / eject two elements from a buffer. *)
Definition buf_pop2 {X : Type} (b : buffer X) : option (X * X * buffer X) :=
  match b with
  | x :: y :: r => Some (x, y, r)
  | _ => None
  end.

Definition buf_eject2 {X : Type} (b : buffer X) : option (buffer X * X * X) :=
  match rev b with
  | z :: y :: r => Some (rev r, y, z)
  | _ => None
  end.

Definition buf_eject3 {X : Type} (b : buffer X)
    : option (buffer X * X * X * X) :=
  match rev b with
  | c :: bb :: a :: r => Some (rev r, a, bb, c)
  | _ => None
  end.

(** A degenerate top: a single childless one-sided only triple (the shapes
    Cases 2–4 receive).  Returns its one buffer. *)
Definition degenerate_buf {A : Type} (d : cchain A)
    : option (buffer (stored A)) :=
  match d with
  | CSingle (Pkt BHole (Node KOnly p s)) CEmpty =>
      match p, s with
      | [], _ => Some s
      | _, [] => Some p
      | _, _ => None
      end
  | _ => None
  end.

(** Subcases 1c/1d on an only-triple (p1, d1, s1): build the LEFT triple. *)
Definition make_left_only {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : option (cchain A) :=
  match d1 with
  | CEmpty =>
      (* 1d *)
      if length s1 <=? 8 then
        match buf_eject2 s1 with
        | Some (s1', y, z) =>
            Some (tree_of (Node KLeft (p1 ++ s1') [y; z]) CEmpty)
        | None => None
        end
      else
        match s1 with
        | a :: b :: c :: srest =>
            match buf_eject2 srest with
            | Some (smid, y, z) =>
                Some (tree_of (Node KLeft (p1 ++ [a; b; c]) [y; z])
                        (push_chain (SSmall smid) CEmpty))
            | None => None
            end
        | _ => None
        end
  | _ =>
      (* 1c *)
      match buf_eject2 s1 with
      | Some (s1', y, z) =>
          Some (tree_of (Node KLeft p1 [y; z])
                  (inject_chain d1 (SSmall s1')))
      | None => None
      end
  end.

(** Case 1, d side: turn a (non-degenerate, nonempty) deque into a LEFT
    triple's tree. *)
Definition make_left {A : Type} (d : cchain A) : option (cchain A) :=
  match d with
  | CEmpty => None
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => make_left_only p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d1 with
          | CEmpty =>
              (* 1b: collapse to an only triple, then 1c/1d *)
              make_left_only (p1 ++ s1 ++ p2) d2 s2
          | _ =>
              (* 1a *)
              match buf_eject2 s2 with
              | Some (s2', y, z) =>
                  Some (tree_of (Node KLeft p1 [y; z])
                          (inject_chain d1 (SBig (s1 ++ p2) d2 s2')))
              | None => None
              end
          end
      end
  | CPair _ _ => None
  end.

(** Mirrors for the e side: build a RIGHT triple's tree. *)
Definition make_right_only {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : option (cchain A) :=
  match d1 with
  | CEmpty =>
      if length p1 <=? 8 then
        match buf_pop2 p1 with
        | Some (x, y, p1') =>
            Some (tree_of (Node KRight [x; y] (p1' ++ s1)) CEmpty)
        | None => None
        end
      else
        match buf_pop2 p1 with
        | Some (x, y, p1') =>
            match buf_eject3 p1' with
            | Some (pmid, a, b, c) =>
                Some (tree_of (Node KRight [x; y] ([a; b; c] ++ s1))
                        (push_chain (SSmall pmid) CEmpty))
            | None => None
            end
        | None => None
        end
  | _ =>
      match buf_pop2 p1 with
      | Some (x, y, p1') =>
          Some (tree_of (Node KRight [x; y] s1)
                  (push_chain (SSmall p1') d1))
      | None => None
      end
  end.

(** Case 1, e side. *)
Definition make_right {A : Type} (e : cchain A) : option (cchain A) :=
  match e with
  | CEmpty => None
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => make_right_only p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d2 with
          | CEmpty =>
              make_right_only p1 d1 (s1 ++ p2 ++ s2)
          | _ =>
              match buf_pop2 p1 with
              | Some (x, y, p1') =>
                  Some (tree_of (Node KRight [x; y] s2)
                          (push_chain (SBig p1' d1 (s1 ++ p2)) d2))
              | None => None
              end
          end
      end
  | CPair _ _ => None
  end.

(** Case 2: degenerate d (one buffer [p3]) onto a normal e. *)
Definition concat_small_left {A : Type}
    (p3 : buffer (stored A)) (e : cchain A) : option (cchain A) :=
  if length p3 <? 8 then Some (fold_right push_chain e p3)
  else
    match e with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p2 s2, d2) =>
            match d2 with
            | CEmpty =>
                (* Childless only root: s2 may be as small as 5, which would
                   make the rebuilt min-coloured root RED at the top.  Two
                   extra buffer moves lift the suffix to >= 7, so the new
                   root is yellow or green and absorbable (still O(1)). *)
                match buf_eject2 p2 with
                | Some (p2', y, z) =>
                    Some (tree_of (Node KOnly p3 (y :: z :: s2))
                            (push_chain (SSmall p2') CEmpty))
                | None => None
                end
            | _ =>
                Some (tree_of (Node KOnly p3 s2)
                        (push_chain (SSmall p2) d2))
            end
        end
    | CPair (CSingle pl rl) rt =>
        match root_and_child pl rl with
        | (Node _ p2 s2, d2) =>
            Some (CPair (tree_of (Node KLeft p3 s2)
                           (push_chain (SSmall p2) d2)) rt)
        end
    | _ => None
    end.

(** Case 3: normal d, degenerate e (one buffer [s3]). *)
Definition concat_small_right {A : Type}
    (d : cchain A) (s3 : buffer (stored A)) : option (cchain A) :=
  if length s3 <? 8 then Some (fold_left inject_chain s3 d)
  else
    match d with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p1 s1, d1) =>
            match d1 with
            | CEmpty =>
                (* Mirror of the left fix: lift the prefix to >= 7. *)
                match buf_pop2 s1 with
                | Some (x, y, s1') =>
                    Some (tree_of (Node KOnly (p1 ++ [x; y]) s3)
                            (push_chain (SSmall s1') CEmpty))
                | None => None
                end
            | _ =>
                Some (tree_of (Node KOnly p1 s3)
                        (inject_chain d1 (SSmall s1)))
            end
        end
    | CPair lt (CSingle pr rr) =>
        match root_and_child pr rr with
        | (Node _ p1 s1, d1) =>
            Some (CPair lt (tree_of (Node KRight p1 s3)
                              (inject_chain d1 (SSmall s1))))
        end
    | _ => None
    end.

Definition cad_concat {A : Type} (d e : cadeque A) : option (cadeque A) :=
  match d, e with
  | CEmpty, _ => Some e
  | _, CEmpty => Some d
  | _, _ =>
      match degenerate_buf d, degenerate_buf e with
      | Some p, Some s =>
          (* Case 4 *)
          if (length p <? 8) || (length s <? 8)
          then Some (CSingle (Pkt BHole (Node KOnly (p ++ s) [])) CEmpty)
          else Some (CSingle (Pkt BHole (Node KOnly p s)) CEmpty)
      | Some p, None => concat_small_left p e
      | None, Some s => concat_small_right d s
      | None, None =>
          match make_left d, make_right e with
          | Some t, Some u => Some (CPair t u)
          | _, _ => None
          end
      end
  end.

(* -------------------------------------------------------------------------- *)
(* Concat sequence sanity.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition mk (l : list nat) : cadeque nat := fold_right cad_push cad_empty l.

Definition cad_concat_list (d e : cadeque nat) : list nat :=
  match cad_concat d e with
  | Some f => cad_to_list f
  | None => []
  end.

(** Case 4, small side: two one-sided childless triples merge buffers. *)
Example cad_concat_case4_small :
  cad_concat_list (mk [1; 2]) (mk [3; 4]) = [1; 2; 3; 4].
Proof. reflexivity. Qed.

(** Case 4, both >=8: a two-sided childless only triple. *)
Example cad_concat_case4_big :
  cad_concat_list (mk [1;2;3;4;5;6;7;8]) (mk [11;12;13;14;15;16;17;18])
  = [1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18].
Proof. vm_compute. reflexivity. Qed.

(** Case 1 (the general path): concatenating two already-concatenated deques
    goes through make_left / make_right and produces a CPair. *)
Example cad_concat_case1 :
  match cad_concat (mk [1;2;3;4;5;6;7;8]) (mk [11;12;13;14;15;16;17;18]) with
  | Some de => cad_concat_list de de
  | None => []
  end
  = [1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18;
     1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18].
Proof. vm_compute. reflexivity. Qed.

(** Case 2: a small degenerate left operand folds onto a normal right one. *)
Example cad_concat_case2_small :
  match cad_concat (mk [1;2;3;4;5;6;7;8]) (mk [11;12;13;14;15;16;17;18]) with
  | Some de => cad_concat_list (mk [97; 98]) de
  | None => []
  end
  = [97;98;1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18].
Proof. vm_compute. reflexivity. Qed.

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

(* ========================================================================== *)
(* Pop / eject with the §6 repair (Cases 1, 2a–2c).                            *)
(*                                                                            *)
(* Pop part 1 ([pop_raw]) removes the first element of the left/only triple   *)
(* and re-bundles via [tree_of] — whose colour-driven reroute is exactly      *)
(* KT99's "the preferred path containing t' may be red": a G->Y or Y->O       *)
(* root change splices the (unconstrained) preferred-child path in, so the    *)
(* new packet terminal may be red.  Part 2 ([repair_packet]) replaces a red   *)
(* terminal u = (p1,d1,s1) per §6: pop/eject a stored triple from d1          *)
(* WITHOUT repair, splice its buffers into u's, and re-attach its child by    *)
(* one child-level [cad_concat].  The repair is non-recursive.                *)
(*                                                                            *)
(* Where the paper is silent: a childless left/right triple of a pair can     *)
(* shrink below its |p|>=5 floor with no red ever arising (childless =        *)
(* green).  We adopt Viennot's vector path: collapse the pair by pushing the  *)
(* <=6 remaining elements onto the sibling (constant work).  Similarly a      *)
(* childless only triple whose pop breaks the two-sided floor merges to the   *)
(* legal one-sided form (<=4 conses).                                         *)
(* ========================================================================== *)

Definition node_pop {A : Type} (n : cnode A) : option (stored A * cnode A) :=
  match n with
  | Node k (x :: p) s => Some (x, Node k p s)
  | Node k [] (x :: s) => Some (x, Node k [] s)
  | _ => None
  end.

Definition node_eject {A : Type} (n : cnode A) : option (cnode A * stored A) :=
  match n with
  | Node k p s =>
      match rev s with
      | x :: s' => Some (Node k p (rev s'), x)
      | [] =>
          match rev p with
          | x :: p' => Some (Node k (rev p') [], x)
          | [] => None
          end
      end
  end.

(** Keep a childless node legal after a removal: empty => [CEmpty]; an only
    node whose two-sided floor broke merges to the one-sided form. *)
Definition rebuild_childless {A : Type} (n : cnode A) : cchain A :=
  match n with
  | Node _ [] [] => CEmpty
  | Node KOnly p s =>
      match p, s with
      | [], _ | _, [] => CSingle (Pkt BHole n) CEmpty
      | _, _ =>
          if (length p <? 5) || (length s <? 5)
          then CSingle (Pkt BHole (Node KOnly (p ++ s) [])) CEmpty
          else CSingle (Pkt BHole n) CEmpty
      end
  | _ => CSingle (Pkt BHole n) CEmpty
  end.

Fixpoint pop_raw {A : Type} (c : cchain A)
    : option (stored A * cchain A) :=
  match c with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_pop n with
      | Some (x, n') =>
          match child with
          | CEmpty => Some (x, rebuild_childless n')
          | _ => Some (x, tree_of n' child)
          end
      | None => None
      end
  | CPair l r =>
      match pop_raw l with
      | Some (x, l') =>
          match l' with
          | CEmpty => Some (x, r)
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty =>
              if length lp <? 5
              then
                (* Viennot collapse, re-crowned: pushing into the KRight
                   sibling would break its |p|=2 discipline, so peel its
                   root and rebuild ONE only-rooted tree.  The new prefix
                   has 4+2+2 = 8 elements, so the min colour equals the
                   old right-root colour key. *)
                match r with
                | CSingle pr rr =>
                    match root_and_child pr rr with
                    | (Node _ p2 s2, d2) =>
                        Some (x, tree_of (Node KOnly (lp ++ ls ++ p2) s2) d2)
                    end
                | _ => None
                end
              else Some (x, CPair l' r)
          | _ => Some (x, CPair l' r)
          end
      | None => None
      end
  end.

Fixpoint eject_raw {A : Type} (c : cchain A)
    : option (cchain A * stored A) :=
  match c with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_eject n with
      | Some (n', x) =>
          match child with
          | CEmpty => Some (rebuild_childless n', x)
          | _ => Some (tree_of n' child, x)
          end
      | None => None
      end
  | CPair l r =>
      match eject_raw r with
      | Some (r', x) =>
          match r' with
          | CEmpty => Some (l, x)
          | CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if length rs <? 5
              then
                (* Mirror of the pop collapse: re-crown over the KLeft
                   sibling's peeled root. *)
                match l with
                | CSingle pl rl =>
                    match root_and_child pl rl with
                    | (Node _ p1 s1, d1) =>
                        Some (tree_of (Node KOnly p1 (s1 ++ rp ++ rs)) d1, x)
                    end
                | _ => None
                end
              else Some (CPair l r', x)
          | _ => Some (CPair l r', x)
          end
      | None => None
      end
  end.

(** §6 repair, front splice (Case 1 for left triples; Case 2a for only):
    pop a stored triple from d1 without repair, merge its prefix into u's,
    park its suffix, re-attach its child by one child-level concat. *)
Definition repair_front {A : Type} (k : kind) (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match pop_raw rest with
  | Some (SBig p2 d2 s2, d1') =>
      match cad_concat d2 (push_chain (SSmall s2) d1') with
      | Some d3 => Some (CSingle (Pkt body (Node k (p1 ++ p2) s1)) d3)
      | None => None
      end
  | Some (SSmall b, d1') =>
      Some (CSingle (Pkt body (Node k (p1 ++ b) s1)) d1')
  | _ => None
  end.

Definition repair_back {A : Type} (k : kind) (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match eject_raw rest with
  | Some (d1', SBig p2 d2 s2) =>
      match cad_concat (inject_chain d1' (SSmall p2)) d2 with
      | Some d3 => Some (CSingle (Pkt body (Node k p1 (s2 ++ s1))) d3)
      | None => None
      end
  | Some (d1', SSmall b) =>
      Some (CSingle (Pkt body (Node k p1 (b ++ s1))) d1')
  | _ => None
  end.

(** Case 2c front+back drain.  Chaining eject after pop on the SAME chain
    degrades it twice and breaks the re-park discipline at depth, so the
    drain takes both cells in ONE step: a single rest double-shrinks its
    root (one rebundle, exact one-rank colour drop); a pair rest drains
    its two components INDEPENDENTLY (each still regular), merging or
    re-crowning when a side dies.  Sequence-identical to pop-then-eject. *)
Definition drain_both {A : Type} (rest : cchain A)
    : option (stored A * option (stored A) * cchain A) :=
  match rest with
  | CEmpty => None
  | CSingle p r =>
      let '(n, dd) := root_and_child p r in
      match node_pop n with
      | Some (cellF, n1) =>
          match node_eject n1 with
          | Some (n2, cellB) =>
              match dd with
              | CEmpty => Some (cellF, Some cellB, rebuild_childless n2)
              | _ => Some (cellF, Some cellB, tree_of n2 dd)
              end
          | None =>
              (* the root held a single cell: childless one-sided rest *)
              match dd with
              | CEmpty => Some (cellF, None, CEmpty)
              | _ => None
              end
          end
      | None => None
      end
  | CPair l r =>
      match pop_raw l, eject_raw r with
      | Some (cellF, l'), Some (r', cellB) =>
          match l', r' with
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty,
            CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if (length lp <? 5) || (length rs <? 5)
              then Some (cellF, Some cellB,
                     CSingle (Pkt BHole
                       (Node KOnly (lp ++ ls) (rp ++ rs))) CEmpty)
              else Some (cellF, Some cellB, CPair l' r')
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty, CSingle pr' rr' =>
              if length lp <? 5
              then
                match root_and_child pr' rr' with
                | (Node _ p2 s2, d2) =>
                    Some (cellF, Some cellB,
                      tree_of (Node KOnly (lp ++ ls ++ p2) s2) d2)
                end
              else Some (cellF, Some cellB, CPair l' r')
          | CSingle pl' rl', CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if length rs <? 5
              then
                match root_and_child pl' rl' with
                | (Node _ p2 s2, d2) =>
                    Some (cellF, Some cellB,
                      tree_of (Node KOnly p2 (s2 ++ rp ++ rs)) d2)
                end
              else Some (cellF, Some cellB, CPair l' r')
          | _, _ => Some (cellF, Some cellB, CPair l' r')
          end
      | _, _ => None
      end
  end.

Definition repair_both {A : Type} (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match drain_both rest with
  | Some (cellF, None, _) =>
      (* one-cell rest: both refills come from the same cell *)
      match cellF with
      | SBig p2 d2 s2 =>
          Some (CSingle (Pkt body (Node KOnly (p1 ++ p2) (s2 ++ s1))) d2)
      | SSmall b =>
          Some (CSingle (Pkt body (Node KOnly (p1 ++ b) s1)) CEmpty)
      | SGround _ => None
      end
  | Some (cellF, Some cellB, mid) =>
      let front :=
        match cellF with
        | SBig p2 d2 s2 =>
            match cad_concat d2 (push_chain (SSmall s2) mid) with
            | Some d4 => Some (p2, d4)
            | None => None
            end
        | SSmall b => Some (b, mid)
        | SGround _ => None
        end
      in
      match front with
      | Some (pf, d4) =>
          match cellB with
          | SBig p3 d3 s3 =>
              match cad_concat (inject_chain d4 (SSmall p3)) d3 with
              | Some d5 =>
                  Some (CSingle
                    (Pkt body (Node KOnly (p1 ++ pf) (s3 ++ s1))) d5)
              | None => None
              end
          | SSmall b =>
              Some (CSingle
                (Pkt body (Node KOnly (p1 ++ pf) (b ++ s1))) d4)
          | SGround _ => None
          end
      | None => None
      end
  | None => None
  end.

(** Repair a packet whose terminal went red; identity otherwise. *)
Definition repair_packet {A : Type}
    (p : cpacket A) (rest : cchain A) : option (cchain A) :=
  match p with
  | Pkt body n =>
      match node_color (chain_has_node rest) n with
      | CR =>
          match n with
          | Node KLeft p1 s1 => repair_front KLeft body p1 s1 rest
          | Node KRight p1 s1 => repair_back KRight body p1 s1 rest
          | Node KOnly p1 s1 =>
              if 8 <=? length s1 then repair_front KOnly body p1 s1 rest
              else if 8 <=? length p1 then repair_back KOnly body p1 s1 rest
              else repair_both body p1 s1 rest
          end
      | _ => Some (CSingle p rest)
      end
  end.

(** After a pop, only the left/single tree's terminal can have gone red;
    after an eject, only the right/single one. *)
Definition repair_pop_side {A : Type} (c : cchain A) : option (cchain A) :=
  match c with
  | CEmpty => Some CEmpty
  | CSingle p rest => repair_packet p rest
  | CPair (CSingle pl rl) r =>
      match repair_packet pl rl with
      | Some l' => Some (CPair l' r)
      | None => None
      end
  | CPair _ _ => None
  end.

Definition repair_eject_side {A : Type} (c : cchain A) : option (cchain A) :=
  match c with
  | CEmpty => Some CEmpty
  | CSingle p rest => repair_packet p rest
  | CPair l (CSingle pr rr) =>
      match repair_packet pr rr with
      | Some r' => Some (CPair l r')
      | None => None
      end
  | CPair _ _ => None
  end.

(** Public pop/eject: the popped element must be a ground element — the
    level-0 statement that will make [J] grow its stratification clause
    when this totality obligation is discharged. *)
Definition cad_pop {A : Type} (d : cadeque A) : option (A * cadeque A) :=
  match pop_raw d with
  | Some (SGround x, d') =>
      match repair_pop_side d' with
      | Some d'' => Some (x, d'')
      | None => None
      end
  | _ => None
  end.

Definition cad_eject {A : Type} (d : cadeque A) : option (cadeque A * A) :=
  match eject_raw d with
  | Some (d', SGround x) =>
      match repair_eject_side d' with
      | Some d'' => Some (d'', x)
      | None => None
      end
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)
(* Pop/eject sequence sanity.                                                  *)
(* -------------------------------------------------------------------------- *)

Example cad_pop_two :
  match cad_pop (mk [1; 2; 3]) with
  | Some (x, d') => (x, cad_to_list d')
  | None => (0, [])
  end = (1, [2; 3]).
Proof. reflexivity. Qed.

Example cad_eject_two :
  match cad_eject (mk [1; 2; 3]) with
  | Some (d', x) => (cad_to_list d', x)
  | None => ([], 0)
  end = ([1; 2], 3).
Proof. reflexivity. Qed.

(** Pop through a Case-1 concat result (a CPair with stored triples). *)
Example cad_pop_after_concat :
  match cad_concat (mk [1;2;3;4;5;6;7;8]) (mk [11;12;13;14;15;16;17;18]) with
  | Some de =>
      match cad_concat de de with
      | Some f =>
          match cad_pop f with
          | Some (x, f') => (x, cad_to_list f')
          | None => (0, [])
          end
      | None => (0, [])
      end
  | None => (0, [])
  end
  = (1, [2;3;4;5;6;7;8;11;12;13;14;15;16;17;18;
         1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18]).
Proof. vm_compute. reflexivity. Qed.

(** Drain a concatenated deque fully from the front: exercises tree_of
    reroutes, pair collapapse, and the red repair across many pops. *)
Fixpoint drain (fuel : nat) (d : cadeque nat) : list nat :=
  match fuel with
  | 0 => []
  | S f =>
      match cad_pop d with
      | Some (x, d') => x :: drain f d'
      | None => []
      end
  end.

Example cad_drain_concat :
  match cad_concat (mk [1;2;3;4;5;6;7;8]) (mk [11;12;13;14;15;16;17;18]) with
  | Some de => drain 20 de
  | None => []
  end
  = [1;2;3;4;5;6;7;8;11;12;13;14;15;16;17;18].
Proof. vm_compute. reflexivity. Qed.
