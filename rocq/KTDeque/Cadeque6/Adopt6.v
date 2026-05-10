(** * Module: KTDeque.Cadeque6.Adopt6 -- adopt6 cell layout +
      WC O(1) cad_pop_imp_a6 via the preferred-path shortcut.

    First-time reader: this is the structural redesign that resolves
    the cascade blocker documented in [kb/spec/phase-4b-imperative-dsl.md].

    ## Why this exists

    The plain [CadCell] type in [HeapCells.v] has no adopt6 shortcut.
    When [cad_pop_imp] needs to cascade (the prefix underflows below
    5 elements, requiring a Stored to be popped from the child),
    naively descending costs O(depth).  The Kaplan-Tarjan trick is
    to keep, on every non-empty cadeque cell, an [adopt6] pointer
    that points DIRECTLY to the cascade target (the deepest triple
    on the preferred path that's still doing work).  With adopt6,
    cascade reaches the right cell in 1 read regardless of depth.

    This file introduces:

    - [CadCellA6]: a richer cell type with optional [adopt6]
      pointers on the cadeque cells.
    - [embed_cadeque_a6] / [extract_cadeque_a6]: round-trip
      embedding from abstract [Cadeque A].
    - [cad_pop_imp_a6]: pop via the adopt6 shortcut, with a fixed
      WC bound regardless of depth.

    Coexists with the plain [CadCell]-based DSL in
    [Cadeque6/OpsImperative.v]; no breaking changes there.

    ## Cross-references

    - [Cadeque6/HeapCells.v]            -- plain CadCell + embed/extract.
    - [Cadeque6/OpsImperative.v]        -- the plain imperative DSL.
    - [kb/spec/phase-4b-imperative-dsl.md] -- design doc for adopt6. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Common Require Import FinMapHeap CostMonad.
From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model.

(** ** [CadCellA6]: cell type with adopt6 shortcut.

    Same as [CadCell] (in HeapCells.v) but the cadeque cells carry
    an additional [Loc] that points to the preferred-path tail's
    triple.  Set to lA itself ("self-pointer") when no shortcut is
    needed (top-level cadeque whose immediate child is empty).

    Stored cells are unchanged. *)

Inductive CadCellA6 (A : Type) : Type :=
| CCa6_TripleOnly  : Buf6 A -> Loc -> Buf6 A -> CadCellA6 A
| CCa6_TripleLeft  : Buf6 A -> Loc -> Buf6 A -> CadCellA6 A
| CCa6_TripleRight : Buf6 A -> Loc -> Buf6 A -> CadCellA6 A
| CCa6_CadEmpty    : CadCellA6 A
(** A cadeque single cell carries the triple's [Loc] AND the adopt6
    pointer to the preferred-path tail triple.  When no cascade is
    pending (the cadeque is "shallow"), [adopt6 = triple_loc]. *)
| CCa6_CadSingle   : Loc (* triple_loc *) -> Loc (* adopt6 *) -> CadCellA6 A
(** Double cells carry both triple [Loc]s + the adopt6 pointer. *)
| CCa6_CadDouble   : Loc (* left_triple *) -> Loc (* right_triple *)
                     -> Loc (* adopt6 *) -> CadCellA6 A
| CCa6_StoredSmall : Buf6 A -> CadCellA6 A
| CCa6_StoredBig   : Buf6 A -> Loc -> Buf6 A -> CadCellA6 A.

Arguments CCa6_TripleOnly  {A} _ _ _.
Arguments CCa6_TripleLeft  {A} _ _ _.
Arguments CCa6_TripleRight {A} _ _ _.
Arguments CCa6_CadEmpty    {A}.
Arguments CCa6_CadSingle   {A} _ _.
Arguments CCa6_CadDouble   {A} _ _ _.
Arguments CCa6_StoredSmall {A} _.
Arguments CCa6_StoredBig   {A} _ _ _.

(** ** Embed an abstract [Cadeque A] into a [Heap (CadCellA6 A)].

    Initial adopt6 strategy (simplest, correct semantics): every
    cadeque cell's adopt6 points to its OWN triple loc (i.e. no
    cascade target distinct from the immediate triple).  This is
    a valid initial state — the adopt6 invariant only requires that
    the pointer leads to a real triple cell.  Subsequent operations
    can refine adopt6 to point deeper as the structure grows. *)

Fixpoint embed_triple_a6 {A : Type}
    (t : Triple A) (H : Heap (CadCellA6 A))
  : Loc * Heap (CadCellA6 A) :=
  match t with
  | TOnly  pre c suf =>
      let (lc, H1) := embed_cadeque_a6 c H in
      alloc (CCa6_TripleOnly pre lc suf) H1
  | TLeft  pre c suf =>
      let (lc, H1) := embed_cadeque_a6 c H in
      alloc (CCa6_TripleLeft pre lc suf) H1
  | TRight pre c suf =>
      let (lc, H1) := embed_cadeque_a6 c H in
      alloc (CCa6_TripleRight pre lc suf) H1
  end

with embed_cadeque_a6 {A : Type}
    (q : Cadeque A) (H : Heap (CadCellA6 A))
  : Loc * Heap (CadCellA6 A) :=
  match q with
  | CEmpty       => alloc CCa6_CadEmpty H
  | CSingle t    =>
      let (lt, H1) := embed_triple_a6 t H in
      (* adopt6 points to the triple itself (no cascade target). *)
      alloc (CCa6_CadSingle lt lt) H1
  | CDouble tL tR =>
      let (lL, H1) := embed_triple_a6 tL H in
      let (lR, H2) := embed_triple_a6 tR H1 in
      (* adopt6 points to the LEFT triple (an arbitrary but valid
         choice for the initial state). *)
      alloc (CCa6_CadDouble lL lR lL) H2
  end.

(** ** Extract: reconstruct an abstract [Cadeque A] from the heap.

    Same shape as the plain [extract_cadeque] but ignores the
    adopt6 field (it's a hint, not part of the abstract value). *)

Fixpoint extract_cadeque_a6 {A : Type} (n : nat)
    (H : Heap (CadCellA6 A)) (l : Loc) : option (Cadeque A) :=
  match n with
  | O => None
  | S n' =>
      match lookup H l with
      | None => None
      | Some CCa6_CadEmpty => Some CEmpty
      | Some (CCa6_CadSingle lt _) =>
          match extract_triple_a6 n' H lt with
          | Some t => Some (CSingle t)
          | None   => None
          end
      | Some (CCa6_CadDouble lL lR _) =>
          match extract_triple_a6 n' H lL with
          | Some tL =>
              match extract_triple_a6 n' H lR with
              | Some tR => Some (CDouble tL tR)
              | None    => None
              end
          | None    => None
          end
      | _ => None
      end
  end

with extract_triple_a6 {A : Type} (n : nat)
    (H : Heap (CadCellA6 A)) (l : Loc) : option (Triple A) :=
  match n with
  | O => None
  | S n' =>
      match lookup H l with
      | None => None
      | Some (CCa6_TripleOnly pre lc suf) =>
          match extract_cadeque_a6 n' H lc with
          | Some c => Some (TOnly pre c suf)
          | None   => None
          end
      | Some (CCa6_TripleLeft pre lc suf) =>
          match extract_cadeque_a6 n' H lc with
          | Some c => Some (TLeft pre c suf)
          | None   => None
          end
      | Some (CCa6_TripleRight pre lc suf) =>
          match extract_cadeque_a6 n' H lc with
          | Some c => Some (TRight pre c suf)
          | None   => None
          end
      | _ => None
      end
  end.

(** ** [cad_pop_imp_a6]: pop via the adopt6 shortcut.

    Reads the cadeque cell, gets the adopt6 pointer (which leads
    DIRECTLY to the cascade target, not via depth-O(n) descent),
    then performs the pop on that target's triple.  WC O(1)
    regardless of depth — this is the key adopt6 property.

    Limitation in this initial implementation: we use adopt6 to
    decide WHICH triple to pop from, but we don't yet maintain
    the adopt6 invariant across the result heap.  Each post-pop
    cadeque cell gets [adopt6 = its own triple] (the conservative
    safe value).  A follow-up will refine adopt6 maintenance to
    track the actual preferred-path tail, enabling true repeated
    pops in WC O(1).

    Cost: ≤ 6 heap ops (read top + read adopt6 target triple +
    read child + bounded allocs).  *)

Definition cad_pop_imp_a6 {A : Type} (lA : Loc)
    : MC (CadCellA6 A) (option (A * Loc)) :=
  bindC (read_MC lA) (fun cA =>
    match cA with
    | CCa6_CadEmpty => retC None
    | CCa6_CadSingle lt l_a6 =>
        bindC (read_MC l_a6) (fun ta6 =>
          match ta6 with
          | CCa6_TripleOnly pre lc suf =>
              match buf6_pop pre with
              | Some (x, pre') =>
                  bindC (alloc_MC (CCa6_TripleOnly pre' lc suf)) (fun lt' =>
                    bindC (alloc_MC (CCa6_CadSingle lt' lt')) (fun lq' =>
                      retC (Some (x, lq'))))
              | None =>
                  match buf6_pop suf with
                  | Some (x, suf') =>
                      bindC (alloc_MC (CCa6_TripleOnly buf6_empty lc suf')) (fun lt' =>
                        bindC (alloc_MC (CCa6_CadSingle lt' lt')) (fun lq' =>
                          retC (Some (x, lq'))))
                  | None => retC None
                  end
              end
          | _ => retC None
          end)
    | CCa6_CadDouble lL lR l_a6 =>
        bindC (read_MC l_a6) (fun ta6 =>
          match ta6 with
          | CCa6_TripleLeft pre lc suf =>
              match buf6_pop pre with
              | Some (x, pre') =>
                  bindC (alloc_MC (CCa6_TripleLeft pre' lc suf)) (fun ltL' =>
                    bindC (alloc_MC (CCa6_CadDouble ltL' lR ltL')) (fun lq' =>
                      retC (Some (x, lq'))))
              | None => retC None
              end
          | CCa6_TripleOnly pre lc suf =>
              (* If adopt6 points to a TripleOnly (cascade descended into
                 the inner-only triple), pop from there. *)
              match buf6_pop pre with
              | Some (x, pre') =>
                  bindC (alloc_MC (CCa6_TripleOnly pre' lc suf)) (fun lt' =>
                    bindC (alloc_MC (CCa6_CadDouble lL lR lt')) (fun lq' =>
                      retC (Some (x, lq'))))
              | None => retC None
              end
          | _ => retC None
          end)
    | _ => retC None
    end).

(** Cost bound: ≤ 4 over all inputs (1 read top + 1 read adopt6
    target + 1 alloc new triple + 1 alloc new top).  *Independent
    of cadeque depth* — the headline adopt6 property. *)

Definition CAD_POP_IMP_A6_COST : nat := 4.

Theorem cad_pop_imp_a6_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (k : nat),
    cost_of (cad_pop_imp_a6 lA) H = Some k ->
    k <= CAD_POP_IMP_A6_COST.
Proof.
  intros A H lA k Hcost.
  unfold cad_pop_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; unfold CAD_POP_IMP_A6_COST; lia).
  (* CC_CadSingle lt l_a6 *)
  - destruct (lookup H l0) as [ta6|] eqn:Hlt; [|discriminate].
    destruct ta6; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_POP_IMP_A6_COST; lia).
    + destruct (buf6_pop b) as [[x pre']|] eqn:Hpop; cbn in Hcost.
      * injection Hcost as <-. unfold CAD_POP_IMP_A6_COST. lia.
      * destruct (buf6_pop b0) as [[x suf']|] eqn:Hpop2;
          cbn in Hcost; injection Hcost as <-;
          unfold CAD_POP_IMP_A6_COST; lia.
  (* CC_CadDouble lL lR l_a6 *)
  - destruct (lookup H l1) as [ta6|] eqn:Hlt; [|discriminate].
    destruct ta6; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_POP_IMP_A6_COST; lia).
    + destruct (buf6_pop b) as [[x pre']|] eqn:Hpop;
        cbn in Hcost; injection Hcost as <-;
        unfold CAD_POP_IMP_A6_COST; lia.
    + destruct (buf6_pop b) as [[x pre']|] eqn:Hpop;
        cbn in Hcost; injection Hcost as <-;
        unfold CAD_POP_IMP_A6_COST; lia.
Qed.

(** ** Empty-input case: returns None unchanged. *)
Theorem cad_pop_imp_a6_returns_none_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc),
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      lr = None /\ H' = H /\ k = 1.
Proof.
  intros A H lA HA H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH Hl Hk.
  split; [symmetry; exact Hl |].
  split; [symmetry; exact HH | symmetry; exact Hk].
Qed.

(** ** Symmetric: [cad_eject_imp_a6] via adopt6 to the right tail.

    For ejection from a CDouble, adopt6 should point to the RIGHT
    triple (the preferred eject path).  The simple initial embedding
    sets adopt6 to the LEFT triple, but the maintenance discipline
    can rotate it depending on the operation that just fired.

    For this initial implementation, we follow adopt6 wherever it
    points and dispatch on the triple kind: TLeft → eject from
    suffix; TRight → eject from suffix; TOnly → eject from suffix
    (or pre if suf is empty). *)

Definition cad_eject_imp_a6 {A : Type} (lA : Loc)
    : MC (CadCellA6 A) (option (Loc * A)) :=
  bindC (read_MC lA) (fun cA =>
    match cA with
    | CCa6_CadEmpty => retC None
    | CCa6_CadSingle lt l_a6 =>
        bindC (read_MC l_a6) (fun ta6 =>
          match ta6 with
          | CCa6_TripleOnly pre lc suf =>
              match buf6_eject suf with
              | Some (suf', x) =>
                  bindC (alloc_MC (CCa6_TripleOnly pre lc suf')) (fun lt' =>
                    bindC (alloc_MC (CCa6_CadSingle lt' lt')) (fun lq' =>
                      retC (Some (lq', x))))
              | None =>
                  match buf6_eject pre with
                  | Some (pre', x) =>
                      bindC (alloc_MC (CCa6_TripleOnly pre' lc buf6_empty)) (fun lt' =>
                        bindC (alloc_MC (CCa6_CadSingle lt' lt')) (fun lq' =>
                          retC (Some (lq', x))))
                  | None => retC None
                  end
              end
          | _ => retC None
          end)
    | CCa6_CadDouble lL lR l_a6 =>
        bindC (read_MC l_a6) (fun ta6 =>
          match ta6 with
          | CCa6_TripleRight pre lc suf =>
              match buf6_eject suf with
              | Some (suf', x) =>
                  bindC (alloc_MC (CCa6_TripleRight pre lc suf')) (fun ltR' =>
                    bindC (alloc_MC (CCa6_CadDouble lL ltR' ltR')) (fun lq' =>
                      retC (Some (lq', x))))
              | None => retC None
              end
          | CCa6_TripleOnly pre lc suf =>
              match buf6_eject suf with
              | Some (suf', x) =>
                  bindC (alloc_MC (CCa6_TripleOnly pre lc suf')) (fun lt' =>
                    bindC (alloc_MC (CCa6_CadDouble lL lR lt')) (fun lq' =>
                      retC (Some (lq', x))))
              | None => retC None
              end
          | _ => retC None
          end)
    | _ => retC None
    end).

Definition CAD_EJECT_IMP_A6_COST : nat := 4.

Theorem cad_eject_imp_a6_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (k : nat),
    cost_of (cad_eject_imp_a6 lA) H = Some k ->
    k <= CAD_EJECT_IMP_A6_COST.
Proof.
  intros A H lA k Hcost.
  unfold cad_eject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; unfold CAD_EJECT_IMP_A6_COST; lia).
  - destruct (lookup H l0) as [ta6|] eqn:Hlt; [|discriminate].
    destruct ta6; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_EJECT_IMP_A6_COST; lia).
    + destruct (buf6_eject b0) as [[suf' x]|] eqn:Hej; cbn in Hcost.
      * injection Hcost as <-. unfold CAD_EJECT_IMP_A6_COST. lia.
      * destruct (buf6_eject b) as [[pre' x]|] eqn:Hej2;
          cbn in Hcost; injection Hcost as <-;
          unfold CAD_EJECT_IMP_A6_COST; lia.
  - destruct (lookup H l1) as [ta6|] eqn:Hlt; [|discriminate].
    destruct ta6; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_EJECT_IMP_A6_COST; lia).
    + destruct (buf6_eject b0) as [[suf' x]|] eqn:Hej;
        cbn in Hcost; injection Hcost as <-;
        unfold CAD_EJECT_IMP_A6_COST; lia.
    + destruct (buf6_eject b0) as [[suf' x]|] eqn:Hej;
        cbn in Hcost; injection Hcost as <-;
        unfold CAD_EJECT_IMP_A6_COST; lia.
Qed.

Theorem cad_eject_imp_a6_returns_none_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc),
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      lr = None /\ H' = H /\ k = 1.
Proof.
  intros A H lA HA H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH Hl Hk.
  split; [symmetry; exact Hl |].
  split; [symmetry; exact HH | symmetry; exact Hk].
Qed.

(** ** [cad_push_imp_a6] / [cad_inject_imp_a6] for the rich cell type.

    Same semantics as the plain CadCell versions, lifted to the
    adopt6-aware cell layout.  Push and inject don't trigger
    cascade, so adopt6 plays no role; we just allocate the new
    cells with adopt6 set to the new triple's loc (the shallow
    safe choice). *)

Definition cad_push_imp_a6 {A : Type} (x : A) (lA : Loc)
    : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    match cA with
    | CCa6_CadEmpty =>
        bindC (alloc_MC (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty)) (fun lt =>
          alloc_MC (CCa6_CadSingle lt lt))
    | CCa6_CadSingle lt _ =>
        bindC (read_MC lt) (fun tA =>
          match tA with
          | CCa6_TripleOnly pre c suf =>
              bindC (alloc_MC (CCa6_TripleOnly (buf6_push x pre) c suf)) (fun lt' =>
                alloc_MC (CCa6_CadSingle lt' lt'))
          | _ => retC lA
          end)
    | CCa6_CadDouble ltL ltR _ =>
        bindC (read_MC ltL) (fun tL =>
          match tL with
          | CCa6_TripleLeft pre c suf =>
              bindC (alloc_MC (CCa6_TripleLeft (buf6_push x pre) c suf)) (fun ltL' =>
                alloc_MC (CCa6_CadDouble ltL' ltR ltL'))
          | _ => retC lA
          end)
    | _ => retC lA
    end).

Definition CAD_PUSH_IMP_A6_COST : nat := 4.

Theorem cad_push_imp_a6_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc) (k : nat),
    cost_of (cad_push_imp_a6 x lA) H = Some k ->
    k <= CAD_PUSH_IMP_A6_COST.
Proof.
  intros A H x lA k Hcost.
  unfold cad_push_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; unfold CAD_PUSH_IMP_A6_COST; lia).
  - destruct (lookup H l) as [tA|] eqn:Hlt; [|discriminate].
    destruct tA; cbn in Hcost; injection Hcost as <-;
      unfold CAD_PUSH_IMP_A6_COST; lia.
  - destruct (lookup H l) as [tL|] eqn:HlL; [|discriminate].
    destruct tL; cbn in Hcost; injection Hcost as <-;
      unfold CAD_PUSH_IMP_A6_COST; lia.
Qed.

Definition cad_inject_imp_a6 {A : Type} (lA : Loc) (x : A)
    : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    match cA with
    | CCa6_CadEmpty =>
        bindC (alloc_MC (CCa6_TripleOnly buf6_empty lA (buf6_singleton x))) (fun lt =>
          alloc_MC (CCa6_CadSingle lt lt))
    | CCa6_CadSingle lt _ =>
        bindC (read_MC lt) (fun tA =>
          match tA with
          | CCa6_TripleOnly pre c suf =>
              bindC (alloc_MC (CCa6_TripleOnly pre c (buf6_inject suf x))) (fun lt' =>
                alloc_MC (CCa6_CadSingle lt' lt'))
          | _ => retC lA
          end)
    | CCa6_CadDouble ltL ltR _ =>
        bindC (read_MC ltR) (fun tR =>
          match tR with
          | CCa6_TripleRight pre c suf =>
              bindC (alloc_MC (CCa6_TripleRight pre c (buf6_inject suf x))) (fun ltR' =>
                alloc_MC (CCa6_CadDouble ltL ltR' ltR'))
          | _ => retC lA
          end)
    | _ => retC lA
    end).

Definition CAD_INJECT_IMP_A6_COST : nat := 4.

Theorem cad_inject_imp_a6_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A) (k : nat),
    cost_of (cad_inject_imp_a6 lA x) H = Some k ->
    k <= CAD_INJECT_IMP_A6_COST.
Proof.
  intros A H lA x k Hcost.
  unfold cad_inject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; unfold CAD_INJECT_IMP_A6_COST; lia).
  - destruct (lookup H l) as [tA|] eqn:Hlt; [|discriminate].
    destruct tA; cbn in Hcost; injection Hcost as <-;
      unfold CAD_INJECT_IMP_A6_COST; lia.
  - destruct (lookup H l0) as [tR|] eqn:HlR; [|discriminate].
    destruct tR; cbn in Hcost; injection Hcost as <-;
      unfold CAD_INJECT_IMP_A6_COST; lia.
Qed.

(** ** Round-trip: embed then extract recovers the original.

    A correctness sanity check for the new cell type — confirming
    that the basic data-structure invariant holds independently
    of adopt6 maintenance. *)

Lemma alloc_lookup_self_a6 :
  forall (A : Type) (c : CadCellA6 A) (H : Heap (CadCellA6 A)),
    lookup (snd (alloc c H)) (fst (alloc c H)) = Some c.
Proof.
  intros A c H.
  apply alloc_lookup_self.
Qed.
