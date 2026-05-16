(** * Module: KTDeque.Cadeque7.Regularity — structural well-formedness
      for [KCadeque X].

    Phase 5 of the [Cadeque7] development (initial cut).

    ## What this captures

    [well_formed_kcad k] asserts that [k] respects the structural
    invariants on which the public operations rely.  The single
    non-trivial invariant — and the only one Phase 5b's redesign
    actually requires — is:

      [KPair l r] is reachable only when [l ≠ KEmpty] and [r ≠ KEmpty].

    All builders enforce this:

    - [kcad_concat] short-circuits when either side is [KEmpty];
    - [kpair_smart] (in [PopEject.v]) collapses empty sides;
    - [kcad_inject]'s [KSingle r p c] branch only matches when
      [c ≠ KEmpty], and combines [c] with the non-empty
      [kcad_singleton x];
    - [kcad_inject]'s [KPair _ _] branch combines [k] with a
      non-empty [kcad_singleton x].

    This file does NOT (yet) speak about colour-tag (RegG/RegR)
    consistency, packet-buffer size discipline, or Stored-cell
    well-formedness.  Those layers remain spec-level (Cadeque6) and
    can be added later if the proofs need them.

    ## Why this matters

    [kpair_smart_seq] and [kcad_concat_seq] both presume "if [KPair
    l r] is in the term, then [l] and [r] are non-empty" via case
    analysis; making this invariant explicit lets us mechanize that
    presumption and lift the seq-laws to invariant-respecting input.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6  Require Import SizedBuffer.
From KTDeque.Cadeque7 Require Import Model PushInject PopEject Concat.

(** ** The predicate. *)

Fixpoint well_formed_kcad {X : Type} (k : KCadeque X) : Prop :=
  match k with
  | KEmpty         => True
  | KSingle _ _ c  => well_formed_kcad c
  | KPair l r      =>
      l <> KEmpty /\ r <> KEmpty
      /\ well_formed_kcad l /\ well_formed_kcad r
  end.

(** ** Constructors preserve well-formedness. *)

Lemma well_formed_kcad_empty :
  forall (X : Type), well_formed_kcad (@KEmpty X).
Proof. intros; cbn; trivial. Qed.

Lemma well_formed_kcad_singleton :
  forall (X : Type) (x : X), well_formed_kcad (kcad_singleton x).
Proof. intros; cbn; trivial. Qed.

Lemma kcad_singleton_not_empty :
  forall (X : Type) (x : X), kcad_singleton x <> KEmpty.
Proof. intros; discriminate. Qed.

(** ** Operations preserve well-formedness. *)

Lemma well_formed_kcad_push :
  forall (X : Type) (x : X) (k : KCadeque X),
    well_formed_kcad k -> well_formed_kcad (kcad_push x k).
Proof.
  intros X x k Hwf.
  destruct k as [|r p c|l r]; cbn in *.
  - (* KEmpty *) trivial.
  - (* KSingle *) exact Hwf.
  - (* KPair *)
    (* kcad_push wraps as fresh KSingle with KPair as child. *)
    cbn. exact Hwf.
Qed.

Lemma well_formed_kcad_inject :
  forall (X : Type) (k : KCadeque X) (x : X),
    well_formed_kcad k -> well_formed_kcad (kcad_inject k x).
Proof.
  intros X k x Hwf.
  destruct k as [|r p c|l r]; cbn in Hwf.
  - (* KEmpty *) cbn. trivial.
  - (* KSingle r p c *)
    destruct c as [|r' p' c'|l' r'].
    + (* c = KEmpty: stays KSingle r _ KEmpty *) cbn. trivial.
    + (* c = KSingle: becomes KSingle r p (KPair c (singleton x)) *)
      cbn. repeat split; try discriminate; try exact I.
      cbn in Hwf. exact Hwf.
    + (* c = KPair: becomes KSingle r p (KPair l' r' (kcad_singleton x)) *)
      destruct Hwf as (Hl_ne & Hr_ne & Hwfl & Hwfr).
      cbn. repeat split; try discriminate; try exact I.
      * exact Hl_ne.
      * exact Hr_ne.
      * exact Hwfl.
      * exact Hwfr.
  - (* KPair l r: becomes KPair (KPair l r) (singleton x) *)
    destruct Hwf as (Hl_ne & Hr_ne & Hwfl & Hwfr).
    cbn. repeat split; try discriminate; try exact I.
    + exact Hl_ne.
    + exact Hr_ne.
    + exact Hwfl.
    + exact Hwfr.
Qed.

Lemma well_formed_kcad_concat :
  forall (X : Type) (a b : KCadeque X),
    well_formed_kcad a -> well_formed_kcad b ->
    well_formed_kcad (kcad_concat a b).
Proof.
  intros X a b Ha Hb.
  unfold kcad_concat.
  (* Phase 5c: kcad_concat now produces [KSingle r p KEmpty] when both
     inputs are non-empty (the Stored-cell wrap); well_formed_kcad
     of [KSingle _ _ KEmpty] reduces to [well_formed_kcad KEmpty = True]. *)
  destruct a as [|ra pa ca|al ar]; [exact Hb | |].
  - destruct b as [|rb pb cb|bl br]; [exact Ha | exact I | exact I].
  - destruct b as [|rb pb cb|bl br]; [exact Ha | exact I | exact I].
Qed.

(** ** [kpair_smart] preserves and concludes well-formedness. *)

Lemma well_formed_kcad_kpair_smart :
  forall (X : Type) (l r : KCadeque X),
    well_formed_kcad l -> well_formed_kcad r ->
    well_formed_kcad (kpair_smart l r).
Proof.
  intros X l r Hl Hr.
  unfold kpair_smart.
  destruct l as [|rl pl cl|ll lr]; [exact Hr | |].
  - destruct r as [|rrr prr crr|rlr rrr]; [exact Hl | |].
    + cbn. split; [discriminate | split; [discriminate | split; assumption]].
    + cbn. split; [discriminate | split; [discriminate | split; assumption]].
  - destruct r as [|rrr prr crr|rlr rrr]; [exact Hl | |].
    + cbn. split; [discriminate | split; [discriminate | split; assumption]].
    + cbn. split; [discriminate | split; [discriminate | split; assumption]].
Qed.

(** ** Pop / eject return well-formed residuals. *)

Lemma well_formed_kcad_pop_struct :
  forall (X : Type) (k : KCadeque X),
    well_formed_kcad k ->
    forall (k' : KCadeque X) (x : X),
      kcad_pop_struct k = Some (x, k') ->
      well_formed_kcad k'.
Proof.
  intros X k.
  induction k as [|r p c IHc|l IHl r IHr]; intros Hwf k' x Hpop.
  - (* KEmpty *) cbn in Hpop. discriminate.
  - (* KSingle r p c *)
    cbn in Hpop.
    destruct (pop_packet_leftmost p) as [[xv p']|]; [|discriminate].
    injection Hpop as Hx Hk. subst x k'.
    cbn. cbn in Hwf. exact Hwf.
  - (* KPair l r *)
    cbn in Hpop.
    destruct (kcad_pop_struct l) as [[xv l']|] eqn:Hl; [|discriminate].
    injection Hpop as Hx Hk. subst x k'.
    cbn in Hwf. destruct Hwf as (_Hl_ne & _Hr_ne & Hwfl & Hwfr).
    apply well_formed_kcad_kpair_smart; [| exact Hwfr].
    apply (IHl Hwfl l' xv). reflexivity.
Qed.

Lemma well_formed_kcad_eject_struct :
  forall (X : Type) (k : KCadeque X),
    well_formed_kcad k ->
    forall (k' : KCadeque X) (x : X),
      kcad_eject_struct k = Some (k', x) ->
      well_formed_kcad k'.
Proof.
  intros X k.
  induction k as [|r p c IHc|l IHl r IHr]; intros Hwf k' x Heject.
  - (* KEmpty *) cbn in Heject. discriminate.
  - (* KSingle r p c *)
    cbn in Heject.
    destruct c as [|rc pc cc|lc rc].
    + (* c = KEmpty: eject from packet *)
      destruct (eject_packet_rightmost p) as [[p' xv]|]; [|discriminate].
      injection Heject as Hk Hx. subst x k'.
      cbn. trivial.
    + (* c = KSingle: recurse via IHc *)
      destruct (kcad_eject_struct (KSingle rc pc cc)) as [[c' xv]|] eqn:Hc;
        [|discriminate].
      injection Heject as Hk Hx. subst x k'.
      cbn. cbn in Hwf.
      apply (IHc Hwf c' xv). reflexivity.
    + (* c = KPair: recurse via IHc *)
      destruct (kcad_eject_struct (KPair lc rc)) as [[c' xv]|] eqn:Hc;
        [|discriminate].
      injection Heject as Hk Hx. subst x k'.
      cbn. cbn in Hwf.
      apply (IHc Hwf c' xv). reflexivity.
  - (* KPair l r *)
    cbn in Heject.
    destruct (kcad_eject_struct r) as [[r' xv]|] eqn:Hr; [|discriminate].
    injection Heject as Hk Hx. subst x k'.
    cbn in Hwf. destruct Hwf as (_Hl_ne & _Hr_ne & Hwfl & Hwfr).
    apply well_formed_kcad_kpair_smart; [exact Hwfl |].
    apply (IHr Hwfr r' xv). reflexivity.
Qed.

(** ** [kcad_from_list] always builds a well-formed chain. *)

Lemma well_formed_kcad_from_list_empty :
  forall (X : Type) (xs : list X),
    well_formed_kcad (kcad_from_list xs).
Proof.
  intros X xs. unfold kcad_from_list.
  assert (Hk0 : well_formed_kcad (@KEmpty X)) by exact I.
  generalize Hk0. generalize (@KEmpty X). clear Hk0.
  induction xs as [|y ys IH]; intros k0 Hwf.
  - cbn. exact Hwf.
  - cbn. apply IH. apply well_formed_kcad_inject. exact Hwf.
Qed.

(** ** Public [kcad_pop] / [kcad_eject] preserve well-formedness. *)

Lemma well_formed_kcad_pop :
  forall (X : Type) (k k' : KCadeque X) (x : X),
    well_formed_kcad k ->
    kcad_pop k = Some (x, k') ->
    well_formed_kcad k'.
Proof.
  intros X k k' x Hwf Hpop.
  unfold kcad_pop in Hpop.
  destruct (kcad_pop_struct k) as [[xv kv]|] eqn:Hstruct.
  - injection Hpop as Hx Hk. subst x k'.
    eapply well_formed_kcad_pop_struct; eassumption.
  - destruct (kcad_to_list_fast k) as [|y ys] eqn:Htl; [discriminate|].
    injection Hpop as Hx Hk. subst x k'.
    apply well_formed_kcad_from_list_empty.
Qed.

Lemma well_formed_kcad_eject :
  forall (X : Type) (k k' : KCadeque X) (x : X),
    well_formed_kcad k ->
    kcad_eject k = Some (k', x) ->
    well_formed_kcad k'.
Proof.
  intros X k k' x Hwf Heject.
  unfold kcad_eject in Heject.
  destruct (kcad_eject_struct k) as [[kv xv]|] eqn:Hstruct.
  - injection Heject as Hk Hx. subst x k'.
    eapply well_formed_kcad_eject_struct; eassumption.
  - destruct (rev (kcad_to_list_fast k)) as [|y ys] eqn:Htl; [discriminate|].
    injection Heject as Hk Hx. subst x k'.
    apply well_formed_kcad_from_list_empty.
Qed.

(** ** Headline: every public op on a well-formed input produces a
       well-formed output. *)

Theorem well_formed_kcad_preservation :
  forall (X : Type) (k : KCadeque X),
    well_formed_kcad k ->
    (forall (x : X), well_formed_kcad (kcad_push x k))
    /\ (forall (x : X), well_formed_kcad (kcad_inject k x))
    /\ (forall (k' : KCadeque X) (x : X),
          kcad_pop k = Some (x, k') -> well_formed_kcad k')
    /\ (forall (k' : KCadeque X) (x : X),
          kcad_eject k = Some (k', x) -> well_formed_kcad k')
    /\ (forall (b : KCadeque X),
          well_formed_kcad b -> well_formed_kcad (kcad_concat k b)).
Proof.
  intros X k Hwf.
  repeat split.
  - intros x; apply well_formed_kcad_push; assumption.
  - intros x; apply well_formed_kcad_inject; assumption.
  - intros k' x Hpop; eapply well_formed_kcad_pop; eassumption.
  - intros k' x Hej; eapply well_formed_kcad_eject; eassumption.
  - intros b Hb; apply well_formed_kcad_concat; assumption.
Qed.

(** ** Sanity checks: well-formedness is preserved on the Phase 5b
       branches that build [KPair] non-recursively. *)

Example wf_singleton_kpair :
  well_formed_kcad (KPair (kcad_singleton 1) (kcad_singleton 2)).
Proof.
  cbn. repeat split; try discriminate.
Qed.

Example wf_push_on_kpair :
  well_formed_kcad (kcad_push 0
                              (KPair (kcad_singleton 1) (kcad_singleton 2))).
Proof.
  apply well_formed_kcad_push. apply wf_singleton_kpair.
Qed.

Example wf_inject_on_kpair :
  well_formed_kcad (kcad_inject
                      (KPair (kcad_singleton 1) (kcad_singleton 2)) 3).
Proof.
  apply well_formed_kcad_inject. apply wf_singleton_kpair.
Qed.

Example wf_concat_two_singletons :
  well_formed_kcad (kcad_concat (kcad_singleton 1) (kcad_singleton 2)).
Proof.
  apply well_formed_kcad_concat;
    apply well_formed_kcad_singleton.
Qed.
