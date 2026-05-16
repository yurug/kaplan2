(** * Module: KTDeque.Cadeque7.Concat — catenation on KCadeque.

    Phase 5c version.

    ## What this version is

    [kcad_concat k1 k2] now wraps both inputs as [Stored] cells
    inside a fresh single-packet [KSingle] (instead of building a
    [KPair]):

      [KSingle RegG (Pkt Hole (NOnly [XStored (StoredBig [] k1 [])]
                                    [XStored (StoredBig [] k2 [])]))
              KEmpty]

    The motivation comes from Phase 5b's tradeoff: with [KPair] as
    the concat result, every subsequent [kcad_inject] would wrap
    things into another [KPair] (because the outer [KSingle]'s
    child was non-empty), building a left-deep [KPair] tree.
    Pop on that tree degenerates to O(depth) per call.

    With the new [Stored]-cell encoding the concat result is a
    [KSingle r p KEmpty].  Subsequent [kcad_inject]s match the
    [KSingle r p KEmpty] branch in [PushInject.v] and stay inside
    the packet's buffer — no [KPair] tree growth.

    ## Trade-off (residual gap)

    The first [kcad_pop] after a concat hits the fallback in
    [PopEject.v]'s public [kcad_pop]: [pop_node_leftmost] doesn't
    unfold [XStored] cells, so it returns [None] and the public
    op falls back to [kcad_to_list] + [kcad_from_list] (O(n)).
    *After* the fallback rebuilds a flat [KSingle] chain,
    subsequent pops are O(1).

    Total drain cost after concat + N injects + N pops:
      - Phase 5b: O(N²) — N pops × O(depth N) each
      - Phase 5c: O(N)  — one O(N) rebuild + (N−1) × O(1)

    Strict WC O(1) per pop (the KT99 §6 promise) would require
    incremental unfolding of the [Stored] cells via the §12.4
    [adopt6] dance.  That is the next step beyond this commit
    and lives in [Cadeque6/Adopt6.v]'s heap layer.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6  Require Import SizedBuffer.
From KTDeque.Cadeque7 Require Import Model.

(** ** [kcad_concat]. *)

Definition kcad_concat {X : Type} (k1 k2 : KCadeque X) : KCadeque X :=
  match k1, k2 with
  | KEmpty, _ => k2
  | _, KEmpty => k1
  | _, _      =>
      KSingle RegG
              (Pkt Hole
                (NOnly
                   (mkBuf6 [XStored (StoredBig (mkBuf6 []) k1 (mkBuf6 []))])
                   (mkBuf6 [XStored (StoredBig (mkBuf6 []) k2 (mkBuf6 []))])))
              KEmpty
  end.

(** ** Sequence law. *)

Theorem kcad_concat_seq :
  forall (X : Type) (k1 k2 : KCadeque X),
    kcad_to_list (kcad_concat k1 k2) = kcad_to_list k1 ++ kcad_to_list k2.
Proof.
  intros X k1 k2.
  destruct k1 as [|r1 p1 c1|l1 r1].
  - (* k1 = KEmpty *) cbn. reflexivity.
  - (* k1 = KSingle *)
    destruct k2 as [|r2 p2 c2|l2 r2].
    + cbn. rewrite app_nil_r. reflexivity.
    + cbn [kcad_concat kcad_to_list].
      unfold buf6_elems; cbn [buf6_elems buf6_flat_kelem kelem_to_list
                              stored_to_list packet_to_list body_to_list
                              node_to_list].
      repeat rewrite app_nil_r. reflexivity.
    + cbn [kcad_concat kcad_to_list].
      unfold buf6_elems; cbn [buf6_elems buf6_flat_kelem kelem_to_list
                              stored_to_list packet_to_list body_to_list
                              node_to_list].
      repeat rewrite app_nil_r. reflexivity.
  - (* k1 = KPair *)
    destruct k2 as [|r2 p2 c2|l2 r2].
    + cbn. rewrite app_nil_r. reflexivity.
    + cbn [kcad_concat kcad_to_list].
      unfold buf6_elems; cbn [buf6_elems buf6_flat_kelem kelem_to_list
                              stored_to_list packet_to_list body_to_list
                              node_to_list].
      repeat rewrite app_nil_r. reflexivity.
    + cbn [kcad_concat kcad_to_list].
      unfold buf6_elems; cbn [buf6_elems buf6_flat_kelem kelem_to_list
                              stored_to_list packet_to_list body_to_list
                              node_to_list].
      repeat rewrite app_nil_r. reflexivity.
Qed.

Example concat_correct :
  let a := kcad_singleton 1 in
  let b := kcad_singleton 2 in
  kcad_to_list (kcad_concat a b) = [1; 2].
Proof. reflexivity. Qed.

Example concat_empty_left :
  forall (X : Type) (k : KCadeque X),
    kcad_to_list (kcad_concat KEmpty k) = kcad_to_list k.
Proof. intros. cbn. reflexivity. Qed.

Example concat_empty_right :
  forall (X : Type) (k : KCadeque X),
    kcad_to_list (kcad_concat k KEmpty) = kcad_to_list k.
Proof.
  intros X k. rewrite kcad_concat_seq. rewrite app_nil_r. reflexivity.
Qed.
