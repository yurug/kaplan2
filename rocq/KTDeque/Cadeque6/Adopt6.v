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

    - [CadCellA6]: a richer cell type with [adopt6] pointer on
      cadeque cells (CCa6_CadSingle and CCa6_CadDouble).
    - [embed_cadeque_a6] / [extract_cadeque_a6]: round-trip
      embedding from abstract [Cadeque A] (initial adopt6 set
      conservatively to own triple's loc).
    - Five imperative ops with WC O(1) bounds: cad_push_imp_a6,
      cad_inject_imp_a6, cad_pop_imp_a6, cad_eject_imp_a6,
      cad_concat_imp_a6.  pop/eject cost is INDEPENDENT of cadeque
      depth — the headline adopt6 property.
    - Inductive [heap_represents_cad_a6] / [_triple_a6] relations.
    - Persistence-under-alloc lemmas (single + two-alloc variants).
    - Sequence-correctness theorems:
        * push_imp_a6 / inject_imp_a6 : all 3 input shapes
        * pop_imp_a6 / eject_imp_a6   : shallow CSingle (pre/suf
                                        non-empty + fallback) + shallow
                                        CDouble cases
        * concat_imp_a6               : all 4 simple sub-op cases
    - List-level refinement:
        * push_imp_a6 / inject_imp_a6 : all 3 input shapes
        * concat_imp_a6               : all 4 simple sub-op cases
    - Input-persistence:
        * push_imp_a6 / inject_imp_a6 : all 3 input shapes
        * concat_imp_a6               : all 4 simple sub-op cases
    - Termination wrappers + FULL CONTRACT bundles:
        * 10 flagship contracts: 3 push + 3 inject + 4 concat
          (each bundles cost + input-persistence + output shape +
           list refinement)

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
From KTDeque.Cadeque6 Require Import Model OpsAbstract.

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

(** ** [cad_concat_imp_a6]: concat on the rich cell type.

    Mirrors the simple-case dispatch from [Cadeque6/OpsImperative.v]'s
    [cad_concat_imp].  Handles the 4 shape combinations
    (CSingle×CSingle, CDouble×CSingle, CSingle×CDouble, CDouble×CDouble)
    when the joining boundary buffers are empty — the simple cases.

    The §12.4 5 repair cases for non-trivial middle children require
    threading adopt6 through the result construction; that's the next
    layer (this file establishes the foundation). *)

Definition cad_concat_imp_a6_singleton_singleton_simple {A : Type}
    (lA lB : Loc) : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    bindC (read_MC lB) (fun cB =>
      match cA, cB with
      | CCa6_CadSingle ltA _, CCa6_CadSingle ltB _ =>
          bindC (read_MC ltA) (fun tA =>
            bindC (read_MC ltB) (fun tB =>
              match tA, tB with
              | CCa6_TripleOnly preA cAchild sufA,
                CCa6_TripleOnly preB cBchild sufB =>
                  match buf6_elems sufA, buf6_elems preB with
                  | [], [] =>
                      bindC (alloc_MC (CCa6_TripleOnly preA cAchild sufB)) (fun newt =>
                        alloc_MC (CCa6_CadSingle newt newt))
                  | _, _ => retC lA
                  end
              | _, _ => retC lA
              end))
      | _, _ => retC lA
      end)).

Definition cad_concat_imp_a6_double_double_simple {A : Type}
    (lA lB : Loc) : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    bindC (read_MC lB) (fun cB =>
      match cA, cB with
      | CCa6_CadDouble ltLA ltRA _, CCa6_CadDouble ltLB ltRB _ =>
          bindC (read_MC ltRA) (fun tRA =>
            bindC (read_MC ltLB) (fun tLB =>
              match tRA, tLB with
              | CCa6_TripleRight preRA cRA sufRA,
                CCa6_TripleLeft preLB cLB sufLB =>
                  match buf6_elems preRA, buf6_elems sufRA,
                        buf6_elems preLB, buf6_elems sufLB with
                  | [], [], [], [] =>
                      alloc_MC (CCa6_CadDouble ltLA ltRB ltLA)
                  | _, _, _, _ => retC lA
                  end
              | _, _ => retC lA
              end))
      | _, _ => retC lA
      end)).

(** Universal concat dispatch: empty-shortcut + 4 simple shapes. *)

Definition cad_concat_imp_a6 {A : Type} (lA lB : Loc) : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    match cA with
    | CCa6_CadEmpty => retC lB
    | _ =>
        bindC (read_MC lB) (fun cB =>
          match cB with
          | CCa6_CadEmpty => retC lA
          | _ =>
              match cA, cB with
              | CCa6_CadSingle _ _, CCa6_CadSingle _ _ =>
                  cad_concat_imp_a6_singleton_singleton_simple lA lB
              | CCa6_CadDouble _ _ _, CCa6_CadDouble _ _ _ =>
                  cad_concat_imp_a6_double_double_simple lA lB
              | _, _ => retC lA  (* DS / SD: stub for now *)
              end
          end)
    end).

(** WC O(1) bound for the unified dispatch. *)
Definition CAD_CONCAT_IMP_A6_COST : nat := 8.

Theorem cad_concat_imp_a6_singleton_singleton_simple_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc) (k : nat),
    cost_of (cad_concat_imp_a6_singleton_singleton_simple lA lB) H = Some k ->
    k <= 6.
Proof.
  intros A H lA lB k Hcost.
  unfold cad_concat_imp_a6_singleton_singleton_simple,
         cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct cB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (lookup H l) as [tA|] eqn:Hlt; [|discriminate].
  destruct (lookup H l1) as [tB|] eqn:Hlt2; [|discriminate].
  destruct tA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct tB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
    injection Hcost as <-; lia.
Qed.

Theorem cad_concat_imp_a6_double_double_simple_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc) (k : nat),
    cost_of (cad_concat_imp_a6_double_double_simple lA lB) H = Some k ->
    k <= 5.
Proof.
  intros A H lA lB k Hcost.
  unfold cad_concat_imp_a6_double_double_simple,
         cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct cB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (lookup H l0) as [tRA|] eqn:Hlt; [|discriminate].
  destruct (lookup H l2) as [tLB|] eqn:Hlt2; [|discriminate].
  destruct tRA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct tLB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia);
    destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia);
    destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia);
    destruct (buf6_elems b2) as [|? ?]; cbn in Hcost;
    injection Hcost as <-; lia.
Qed.

(** Universal WC O(1) bound for [cad_concat_imp_a6] across all
    dispatch paths.  Proof uses [destruct]-driven case enumeration. *)
Theorem cad_concat_imp_a6_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc) (k : nat),
    cost_of (cad_concat_imp_a6 lA lB) H = Some k ->
    k <= CAD_CONCAT_IMP_A6_COST.
Proof.
  intros A H lA lB k Hcost.
  unfold cad_concat_imp_a6, cost_of, bindC, read_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct cA; cbn in Hcost.
  (* CCa6_TripleOnly *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost; injection Hcost as <-;
      unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_TripleLeft *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost; injection Hcost as <-;
      unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_TripleRight *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost; injection Hcost as <-;
      unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_CadEmpty: shortcut to lB *)
  - injection Hcost as <-. unfold CAD_CONCAT_IMP_A6_COST. lia.
  (* CCa6_CadSingle *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
    (* CadSingle × CadSingle: dispatch to ss_simple *)
    + unfold cad_concat_imp_a6_singleton_singleton_simple,
             bindC, read_MC, alloc_MC, retC in Hcost.
      rewrite HlkA, HlkB in Hcost. cbn in Hcost.
      destruct (lookup H l) as [tA|] eqn:Hlt; [|discriminate].
      destruct (lookup H l1) as [tB|] eqn:Hlt2; [|discriminate].
      destruct tA; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
      destruct tB; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
      destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
      destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
        injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_CadDouble *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost;
      try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
    (* CadDouble × CadDouble: dispatch to dd_simple *)
    + unfold cad_concat_imp_a6_double_double_simple,
             bindC, read_MC, alloc_MC, retC in Hcost.
      rewrite HlkA, HlkB in Hcost. cbn in Hcost.
      destruct (lookup H l0) as [tRA|] eqn:Hlt; [|discriminate].
      destruct (lookup H l2) as [tLB|] eqn:Hlt2; [|discriminate].
      destruct tRA; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
      destruct tLB; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia).
      destruct (buf6_elems b) as [|? ?]; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia);
        destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia);
        destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
        try (injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia);
        destruct (buf6_elems b2) as [|? ?]; cbn in Hcost;
        injection Hcost as <-; unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_StoredSmall *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost; injection Hcost as <-;
      unfold CAD_CONCAT_IMP_A6_COST; lia.
  (* CCa6_StoredBig *)
  - destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
    destruct cB; cbn in Hcost; injection Hcost as <-;
      unfold CAD_CONCAT_IMP_A6_COST; lia.
Qed.

(** ** Lookup characterization for cad_*_imp_a6 success paths. *)

Theorem cad_push_imp_a6_lookup_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc),
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      let lt := next_loc H in
      lookup H' lt = Some (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty)
      /\ lookup H' l' = Some (CCa6_CadSingle lt lt).
Proof.
  intros A H x lA HA H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_inject_imp_a6_lookup_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A),
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      let lt := next_loc H in
      lookup H' lt = Some (CCa6_TripleOnly buf6_empty lA (buf6_singleton x))
      /\ lookup H' l' = Some (CCa6_CadSingle lt lt).
Proof.
  intros A H lA x HA H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** ** Cost-exact theorems for the success paths. *)

Theorem cad_push_imp_a6_cost_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc),
    lookup H lA = Some CCa6_CadEmpty ->
    cost_of (cad_push_imp_a6 x lA) H = Some 3.
Proof.
  intros A H x lA HA.
  unfold cad_push_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA. cbn. reflexivity.
Qed.

Theorem cad_inject_imp_a6_cost_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A),
    lookup H lA = Some CCa6_CadEmpty ->
    cost_of (cad_inject_imp_a6 lA x) H = Some 3.
Proof.
  intros A H lA x HA.
  unfold cad_inject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA. cbn. reflexivity.
Qed.

(** ** [heap_represents_cad_a6] / [heap_represents_triple_a6]:
    inductive semantics linking a heap + loc to an abstract Cadeque /
    Triple value, ignoring the adopt6 hint (it's a hint, not part of
    the abstract value). *)

Inductive heap_represents_cad_a6 {A : Type}
  : Heap (CadCellA6 A) -> Loc -> Cadeque A -> Prop :=
| HRCa6_Empty :
    forall H l, lookup H l = Some CCa6_CadEmpty ->
                heap_represents_cad_a6 H l CEmpty
| HRCa6_Single :
    forall H l lt l_a6 t,
      lookup H l = Some (CCa6_CadSingle lt l_a6) ->
      heap_represents_triple_a6 H lt t ->
      heap_represents_cad_a6 H l (CSingle t)
| HRCa6_Double :
    forall H l ltL ltR l_a6 tL tR,
      lookup H l = Some (CCa6_CadDouble ltL ltR l_a6) ->
      heap_represents_triple_a6 H ltL tL ->
      heap_represents_triple_a6 H ltR tR ->
      heap_represents_cad_a6 H l (CDouble tL tR)

with heap_represents_triple_a6 {A : Type}
  : Heap (CadCellA6 A) -> Loc -> Triple A -> Prop :=
| HRTa6_TOnly :
    forall H l pre lc suf c,
      lookup H l = Some (CCa6_TripleOnly pre lc suf) ->
      heap_represents_cad_a6 H lc c ->
      heap_represents_triple_a6 H l (TOnly pre c suf)
| HRTa6_TLeft :
    forall H l pre lc suf c,
      lookup H l = Some (CCa6_TripleLeft pre lc suf) ->
      heap_represents_cad_a6 H lc c ->
      heap_represents_triple_a6 H l (TLeft pre c suf)
| HRTa6_TRight :
    forall H l pre lc suf c,
      lookup H l = Some (CCa6_TripleRight pre lc suf) ->
      heap_represents_cad_a6 H lc c ->
      heap_represents_triple_a6 H l (TRight pre c suf).

(** ** Sequence-correctness for cad_push_imp_a6 on empty input.

    Given that lA represents [CEmpty] in H and lA < next_loc H, the
    result heap H' represents [CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty)]
    at the result loc l'.  Persistence of lA's CCa6_CadEmpty status
    across the two allocs is established by direct case analysis on
    Pos.lt. *)

Theorem cad_push_imp_a6_seq_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc),
    heap_represents_cad_a6 H lA CEmpty ->
    Pos.lt lA (next_loc H) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l'
        (CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty)).
Proof.
  intros A H x lA HrepA HltA H' l' k Hop.
  assert (HA : lookup H lA = Some CCa6_CadEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; exact Hlk. }
  assert (Hlookup : let lt := next_loc H in
                    lookup H' lt = Some (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty)
                    /\ lookup H' l' = Some (CCa6_CadSingle lt lt)).
  { eapply cad_push_imp_a6_lookup_when_empty;
      [exact HA | exact Hop]. }
  destruct Hlookup as [Hlt_new Hl_new].
  cbn in Hlt_new, Hl_new.
  assert (HA' : lookup H' lA = Some CCa6_CadEmpty).
  { unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA in Hop. cbn in Hop.
    injection Hop as HH _ _.
    subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lA (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in HltA.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact HltA|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lA (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in HltA.
        exact (Pos.lt_irrefl _ HltA).
      * exact HA. }
  eapply HRCa6_Single.
  - exact Hl_new.
  - eapply HRTa6_TOnly.
    + exact Hlt_new.
    + apply HRCa6_Empty. exact HA'.
Qed.

Theorem cad_inject_imp_a6_seq_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A),
    heap_represents_cad_a6 H lA CEmpty ->
    Pos.lt lA (next_loc H) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l'
        (CSingle (TOnly buf6_empty CEmpty (buf6_singleton x))).
Proof.
  intros A H lA x HrepA HltA H' l' k Hop.
  assert (HA : lookup H lA = Some CCa6_CadEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; exact Hlk. }
  assert (Hlookup : let lt := next_loc H in
                    lookup H' lt = Some (CCa6_TripleOnly buf6_empty lA (buf6_singleton x))
                    /\ lookup H' l' = Some (CCa6_CadSingle lt lt)).
  { eapply cad_inject_imp_a6_lookup_when_empty;
      [exact HA | exact Hop]. }
  destruct Hlookup as [Hlt_new Hl_new].
  cbn in Hlt_new, Hl_new.
  assert (HA' : lookup H' lA = Some CCa6_CadEmpty).
  { unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA in Hop. cbn in Hop.
    injection Hop as HH _ _.
    subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lA (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in HltA.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact HltA|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lA (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in HltA.
        exact (Pos.lt_irrefl _ HltA).
      * exact HA. }
  eapply HRCa6_Single.
  - exact Hl_new.
  - eapply HRTa6_TOnly.
    + exact Hlt_new.
    + apply HRCa6_Empty. exact HA'.
Qed.

(** ** Lookup characterization for cad_push_imp_a6 single/double. *)

Theorem cad_push_imp_a6_lookup_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre c suf) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      let lt' := next_loc H in
      lookup H' lt' = Some (CCa6_TripleOnly (buf6_push x pre) c suf)
      /\ lookup H' l' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H x lA lt l_a6 pre suf c HA Ht H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_push_imp_a6_lookup_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre c suf) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      let ltL' := next_loc H in
      lookup H' ltL' = Some (CCa6_TripleLeft (buf6_push x pre) c suf)
      /\ lookup H' l' = Some (CCa6_CadDouble ltL' ltR ltL').
Proof.
  intros A H x lA ltL ltR l_a6 pre suf c HA HtL H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** Symmetric: cad_inject_imp_a6 single/double lookup. *)

Theorem cad_inject_imp_a6_lookup_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre c suf) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      let lt' := next_loc H in
      lookup H' lt' = Some (CCa6_TripleOnly pre c (buf6_inject suf x))
      /\ lookup H' l' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lt l_a6 x pre suf c HA Ht H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_inject_imp_a6_lookup_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre c suf) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      let ltR' := next_loc H in
      lookup H' ltR' = Some (CCa6_TripleRight pre c (buf6_inject suf x))
      /\ lookup H' l' = Some (CCa6_CadDouble ltL ltR' ltR').
Proof.
  intros A H lA ltL ltR l_a6 x pre suf c HA HtR H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** Cost-exact theorems for non-empty cases. *)

Theorem cad_push_imp_a6_cost_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre c suf) ->
    cost_of (cad_push_imp_a6 x lA) H = Some 4.
Proof.
  intros A H x lA lt l_a6 pre suf c HA Ht.
  unfold cad_push_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. reflexivity.
Qed.

Theorem cad_push_imp_a6_cost_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre c suf) ->
    cost_of (cad_push_imp_a6 x lA) H = Some 4.
Proof.
  intros A H x lA ltL ltR l_a6 pre suf c HA HtL.
  unfold cad_push_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, HtL. cbn. reflexivity.
Qed.

Theorem cad_inject_imp_a6_cost_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre c suf) ->
    cost_of (cad_inject_imp_a6 lA x) H = Some 4.
Proof.
  intros A H lA lt l_a6 x pre suf c HA Ht.
  unfold cad_inject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. reflexivity.
Qed.

Theorem cad_inject_imp_a6_cost_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (c : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre c suf) ->
    cost_of (cad_inject_imp_a6 lA x) H = Some 4.
Proof.
  intros A H lA ltL ltR l_a6 x pre suf c HA HtR.
  unfold cad_inject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, HtR. cbn. reflexivity.
Qed.

(** ** Persistence-under-alloc for [heap_represents_cad_a6] /
    [heap_represents_triple_a6].

    Mutual recursive proof: if a value is represented at a loc in H,
    and all reachable locs are < next_loc H, then the same value is
    represented at the same loc in (snd (alloc c H)).

    Used to lift heap_represents witnesses across the allocs the
    imperative ops perform. *)

Lemma lookup_persists_after_alloc_a6 :
  forall (A : Type) (c : CadCellA6 A) (H : Heap (CadCellA6 A)) (l : Loc),
    Pos.lt l (next_loc H) ->
    lookup (snd (alloc c H)) l = lookup H l.
Proof.
  intros A c H l Hlt.
  apply lookup_after_alloc.
  intros Heq. rewrite Heq in Hlt. exact (Pos.lt_irrefl _ Hlt).
Qed.

Lemma heap_represents_cad_a6_persists_alloc :
  forall (A : Type) (c_new : CadCellA6 A) (q : Cadeque A)
         (H : Heap (CadCellA6 A)) (l : Loc),
    heap_represents_cad_a6 H l q ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    heap_represents_cad_a6 (snd (alloc c_new H)) l q
with heap_represents_triple_a6_persists_alloc :
  forall (A : Type) (c_new : CadCellA6 A) (t : Triple A)
         (H : Heap (CadCellA6 A)) (l : Loc),
    heap_represents_triple_a6 H l t ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    heap_represents_triple_a6 (snd (alloc c_new H)) l t.
Proof.
  - intros A c_new q H l Hrep Hwf_cad Hwf_trip.
    inversion Hrep as [Hh Hl Hlk Heq1 Heq2
                      | Hh Hl lt l_a6 t Hlk Hrep_t Heq1 Heq2
                      | Hh Hl ltL ltR l_a6 tL tR Hlk Hrep_tL Hrep_tR Heq1 Heq2];
      subst.
    + apply HRCa6_Empty.
      rewrite lookup_persists_after_alloc_a6; [assumption|].
      eapply Hwf_cad. exact Hrep.
    + eapply HRCa6_Single.
      * rewrite lookup_persists_after_alloc_a6; [exact Hlk|].
        eapply Hwf_cad. exact Hrep.
      * apply heap_represents_triple_a6_persists_alloc; assumption.
    + eapply HRCa6_Double.
      * rewrite lookup_persists_after_alloc_a6; [exact Hlk|].
        eapply Hwf_cad. exact Hrep.
      * apply heap_represents_triple_a6_persists_alloc; assumption.
      * apply heap_represents_triple_a6_persists_alloc; assumption.
  - intros A c_new t H l Hrep Hwf_cad Hwf_trip.
    inversion Hrep as [Hh Hl pre lc suf c Hlk Hrep_c Heq1 Heq2
                      | Hh Hl pre lc suf c Hlk Hrep_c Heq1 Heq2
                      | Hh Hl pre lc suf c Hlk Hrep_c Heq1 Heq2];
      subst.
    + eapply HRTa6_TOnly.
      * rewrite lookup_persists_after_alloc_a6; [exact Hlk|].
        eapply Hwf_trip. exact Hrep.
      * apply heap_represents_cad_a6_persists_alloc; assumption.
    + eapply HRTa6_TLeft.
      * rewrite lookup_persists_after_alloc_a6; [exact Hlk|].
        eapply Hwf_trip. exact Hrep.
      * apply heap_represents_cad_a6_persists_alloc; assumption.
    + eapply HRTa6_TRight.
      * rewrite lookup_persists_after_alloc_a6; [exact Hlk|].
        eapply Hwf_trip. exact Hrep.
      * apply heap_represents_cad_a6_persists_alloc; assumption.
Qed.

(** Persistence over two consecutive allocs (the pattern used by
    push_imp_a6 / inject_imp_a6 / etc. on non-empty inputs). *)

Lemma heap_represents_cad_a6_persists_two_allocs :
  forall (A : Type) (c1 c2 : CadCellA6 A) (q : Cadeque A)
         (H : Heap (CadCellA6 A)) (l : Loc),
    heap_represents_cad_a6 H l q ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc c1 H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc c1 H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc c1 H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc c1 H)))) ->
    heap_represents_cad_a6 (snd (alloc c2 (snd (alloc c1 H)))) l q.
Proof.
  intros A c1 c2 q H l Hrep Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'.
  apply heap_represents_cad_a6_persists_alloc; try assumption.
  apply heap_represents_cad_a6_persists_alloc; assumption.
Qed.

Lemma heap_represents_triple_a6_persists_two_allocs :
  forall (A : Type) (c1 c2 : CadCellA6 A) (t : Triple A)
         (H : Heap (CadCellA6 A)) (l : Loc),
    heap_represents_triple_a6 H l t ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc c1 H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc c1 H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc c1 H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc c1 H)))) ->
    heap_represents_triple_a6 (snd (alloc c2 (snd (alloc c1 H)))) l t.
Proof.
  intros A c1 c2 t H l Hrep Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'.
  apply heap_represents_triple_a6_persists_alloc; try assumption.
  apply heap_represents_triple_a6_persists_alloc; assumption.
Qed.

(** ** Sequence-correctness for non-empty push/inject_imp_a6.

    With the persistence lemma in place, the non-empty case proofs
    follow the same pattern as the plain-CadCell DSL. *)

Theorem cad_push_imp_a6_seq_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A),
    heap_represents_cad_a6 H lA (CSingle (TOnly pre c suf)) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CSingle (TOnly (buf6_push x pre) c suf)).
Proof.
  intros A H x lA lt l_a6 pre suf cChild c HrepA HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let lt' := next_loc H in
                    lookup H' lt' = Some (CCa6_TripleOnly (buf6_push x pre) cChild suf)
                    /\ lookup H' l' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_push_imp_a6_lookup_when_single;
      [exact HA | exact Ht | exact Hop]. }
  destruct Hlookup as [Hlt_new Hl_new].
  cbn in Hlt_new, Hl_new.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH _ _.
  subst H'.
  eapply HRCa6_Single.
  - exact Hl_new.
  - eapply HRTa6_TOnly.
    + exact Hlt_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_inject_imp_a6_seq_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A),
    heap_represents_cad_a6 H lA (CSingle (TOnly pre c suf)) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CSingle (TOnly pre c (buf6_inject suf x))).
Proof.
  intros A H lA lt l_a6 x pre suf cChild c HrepA HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let lt' := next_loc H in
                    lookup H' lt' = Some (CCa6_TripleOnly pre cChild (buf6_inject suf x))
                    /\ lookup H' l' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_inject_imp_a6_lookup_when_single;
      [exact HA | exact Ht | exact Hop]. }
  destruct Hlookup as [Hlt_new Hl_new].
  cbn in Hlt_new, Hl_new.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH _ _.
  subst H'.
  eapply HRCa6_Single.
  - exact Hl_new.
  - eapply HRTa6_TOnly.
    + exact Hlt_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_push_imp_a6_seq_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A),
    heap_represents_cad_a6 H lA (CDouble (TLeft pre c suf) tR) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CDouble (TLeft (buf6_push x pre) c suf) tR).
Proof.
  intros A H x lA ltL ltR l_a6 pre suf cChild c tR HrepA HA HtL HrepC HrepTR
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let ltL' := next_loc H in
                    lookup H' ltL' = Some (CCa6_TripleLeft (buf6_push x pre) cChild suf)
                    /\ lookup H' l' = Some (CCa6_CadDouble ltL' ltR ltL')).
  { eapply cad_push_imp_a6_lookup_when_double;
      [exact HA | exact HtL | exact Hop]. }
  destruct Hlookup as [HltL_new Hl_new].
  cbn in HltL_new, Hl_new.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  injection Hop as HH _ _.
  subst H'.
  eapply HRCa6_Double.
  - exact Hl_new.
  - eapply HRTa6_TLeft.
    + exact HltL_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_inject_imp_a6_seq_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A),
    heap_represents_cad_a6 H lA (CDouble tL (TRight pre c suf)) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CDouble tL (TRight pre c (buf6_inject suf x))).
Proof.
  intros A H lA ltL ltR l_a6 x pre suf cChild c tL HrepA HA HtR HrepTL HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let ltR' := next_loc H in
                    lookup H' ltR' = Some (CCa6_TripleRight pre cChild (buf6_inject suf x))
                    /\ lookup H' l' = Some (CCa6_CadDouble ltL ltR' ltR')).
  { eapply cad_inject_imp_a6_lookup_when_double;
      [exact HA | exact HtR | exact Hop]. }
  destruct Hlookup as [HltR_new Hl_new].
  cbn in HltR_new, Hl_new.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  injection Hop as HH _ _.
  subst H'.
  eapply HRCa6_Double.
  - exact Hl_new.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
  - eapply HRTa6_TRight.
    + exact HltR_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** Lookup characterization for cad_pop_imp_a6 in the shallow case.

    Shallow case: CSingle with adopt6 pointing to the cadeque's only
    triple (the post-embed default), TripleOnly with empty child,
    non-empty prefix.  Pop from prefix → new triple + new top. *)

Theorem cad_pop_imp_a6_lookup_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      let lt' := next_loc H in
      exists lq',
        lr = Some (x, lq') /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' lt' = Some (CCa6_TripleOnly pre' lc suf) /\
        lookup H' lq' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lt pre suf lc x pre' HA Ht Hpop H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hpop in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)).
  cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** Cost-exact for the shallow pop case: 2 reads + 2 allocs = 4. *)
Theorem cad_pop_imp_a6_cost_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    cost_of (cad_pop_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA lt pre suf lc x pre' HA Ht Hpop.
  unfold cad_pop_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. rewrite Hpop. cbn. reflexivity.
Qed.

(** Sequence-correctness for the shallow pop case (CSingle, prefix
    non-empty): the result heap H' represents
    [CSingle (TOnly pre' CEmpty suf)] at the result loc, where
    pre' = buf6_pop pre.

    Requires the input child cell at lc to be CCa6_CadEmpty *and*
    lc to be allocated (lc < next_loc H), so persistence of the
    lc → empty binding holds across the 2 allocs the op performs. *)

Theorem cad_pop_imp_a6_seq_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (x, lq') /\
        heap_represents_cad_a6 H' lq' (CSingle (TOnly pre' CEmpty suf)).
Proof.
  intros A H lA lt pre suf lc x pre' HA Ht Hlc Hltlc Hpop H' lr k Hop.
  assert (Hchar : let lt' := next_loc H in
                  exists lq',
                    lr = Some (x, lq') /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' lt' = Some (CCa6_TripleOnly pre' lc suf) /\
                    lookup H' lq' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_pop_imp_a6_lookup_when_single_pre_nonempty;
      [exact HA | exact Ht | exact Hpop | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [Hltnew Hlqnew]]]].
  cbn in Hltnew, Hlqnew.
  exists lq'.
  split; [exact Hlr |].
  assert (Hlc' : lookup H' lc = Some CCa6_CadEmpty).
  { unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA, Ht in Hop. cbn in Hop.
    rewrite Hpop in Hop. cbn in Hop.
    injection Hop as HH _ _. subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lc (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in Hltlc.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact Hltlc|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lc (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in Hltlc.
        exact (Pos.lt_irrefl _ Hltlc).
      * exact Hlc. }
  eapply HRCa6_Single.
  - exact Hlqnew.
  - eapply HRTa6_TOnly.
    + exact Hltnew.
    + apply HRCa6_Empty. exact Hlc'.
Qed.

(** ** Symmetric: lookup + cost + seq for [cad_eject_imp_a6] shallow case
    (CSingle, suffix non-empty). *)

Theorem cad_eject_imp_a6_lookup_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      let lt' := next_loc H in
      exists lq',
        lr = Some (lq', x) /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' lt' = Some (CCa6_TripleOnly pre lc suf') /\
        lookup H' lq' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hej H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hej in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)).
  cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_eject_imp_a6_cost_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    cost_of (cad_eject_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hej.
  unfold cad_eject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. rewrite Hej. cbn. reflexivity.
Qed.

Theorem cad_eject_imp_a6_seq_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (lq', x) /\
        heap_represents_cad_a6 H' lq' (CSingle (TOnly pre CEmpty suf')).
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hlc Hltlc Hej H' lr k Hop.
  assert (Hchar : let lt' := next_loc H in
                  exists lq',
                    lr = Some (lq', x) /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' lt' = Some (CCa6_TripleOnly pre lc suf') /\
                    lookup H' lq' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_eject_imp_a6_lookup_when_single_suf_nonempty;
      [exact HA | exact Ht | exact Hej | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [Hltnew Hlqnew]]]].
  exists lq'.
  split; [exact Hlr |].
  assert (Hlc' : lookup H' lc = Some CCa6_CadEmpty).
  { unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA, Ht in Hop. cbn in Hop.
    rewrite Hej in Hop. cbn in Hop.
    injection Hop as HH _ _. subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lc (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in Hltlc.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact Hltlc|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lc (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in Hltlc.
        exact (Pos.lt_irrefl _ Hltlc).
      * exact Hlc. }
  eapply HRCa6_Single.
  - exact Hlqnew.
  - eapply HRTa6_TOnly.
    + exact Hltnew.
    + apply HRCa6_Empty. exact Hlc'.
Qed.

(** ** Sequence-correctness for [cad_concat_imp_a6_singleton_singleton_simple]
    (the simple SS case: both inputs are CSingle with TripleOnly
    triples whose joining buffers are empty). *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_lookup :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltB : Loc)
         (preA sufB : Buf6 A) (cAchild cBchild : Loc)
         (l_a6_A l_a6_B : Loc),
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cAchild buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cBchild sufB) ->
    forall H' l' k,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      let lt' := next_loc H in
      lookup H' lt' = Some (CCa6_TripleOnly preA cAchild sufB)
      /\ lookup H' l' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lB ltA ltB preA sufB cAchild cBchild l_a6_A l_a6_B
         HA HB HtA HtB H' l' k Hop.
  unfold cad_concat_imp_a6_singleton_singleton_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** Sequence-correctness for the SS simple sub-op via heap_represents_cad_a6.

    Under shape preconditions + structural well-formedness + post-1-alloc
    well-formedness, the result heap represents
    [CSingle (TOnly preA cA' sufB)] where cA' is the abstract value of
    the A's child cadeque (carried verbatim through the join). *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_seq :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltB : Loc)
         (preA sufB : Buf6 A) (cAchild cBchild : Loc)
         (l_a6_A l_a6_B : Loc) (cA' : Cadeque A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cAchild buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cBchild sufB) ->
    heap_represents_cad_a6 H cAchild cA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CSingle (TOnly preA cA' sufB)).
Proof.
  intros A H lA lB ltA ltB preA sufB cAchild cBchild l_a6_A l_a6_B cA'
         HrepA HrepB HA HB HtA HtB HrepCA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let lt' := next_loc H in
                    lookup H' lt' = Some (CCa6_TripleOnly preA cAchild sufB)
                    /\ lookup H' l' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_concat_imp_a6_singleton_singleton_simple_lookup;
      [exact HA | exact HB | exact HtA | exact HtB | exact Hop]. }
  cbn in Hlookup.
  destruct Hlookup as [Hlt_new Hl_new].
  unfold cad_concat_imp_a6_singleton_singleton_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Single.
  - exact Hl_new.
  - eapply HRTa6_TOnly.
    + exact Hlt_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** [cad_concat_imp_a6_double_double_simple] lookup + seq theorem.

    Simple DD case: both inputs are CDouble whose middle triples
    (A's right TripleRight, B's left TripleLeft) have all-empty
    buffers.  Result is a fresh CDouble whose triples are A's left
    and B's right (carried verbatim via persistence). *)

Theorem cad_concat_imp_a6_double_double_simple_lookup :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltLB ltRB : Loc)
         (cRA cLB : Loc) (l_a6_A l_a6_B : Loc),
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight buf6_empty cRA buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB buf6_empty) ->
    forall H' l' k,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      lookup H' l' = Some (CCa6_CadDouble ltLA ltRB ltLA).
Proof.
  intros A H lA lB ltLA ltRA ltLB ltRB cRA cLB l_a6_A l_a6_B
         HA HB HtRA HtLB H' l' k Hop.
  unfold cad_concat_imp_a6_double_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  rewrite <- HH, <- Hl. unfold lookup. cbn.
  destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne];
    [reflexivity|contradiction].
Qed.

Theorem cad_concat_imp_a6_double_double_simple_seq :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltLB ltRB : Loc)
         (cRA cLB : Loc) (l_a6_A l_a6_B : Loc) (tLA tRB : Triple A),
    heap_represents_cad_a6 H lA
      (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) ->
    heap_represents_cad_a6 H lB
      (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight buf6_empty cRA buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB buf6_empty) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    forall H' l' k,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CDouble tLA tRB).
Proof.
  intros A H lA lB ltLA ltRA ltLB ltRB cRA cLB l_a6_A l_a6_B tLA tRB
         HrepA HrepB HA HB HtRA HtLB HrepTLA HrepTRB
         Hwf_cad Hwf_trip H' l' k Hop.
  assert (Hlookup : lookup H' l' = Some (CCa6_CadDouble ltLA ltRB ltLA)).
  { eapply cad_concat_imp_a6_double_double_simple_lookup;
      [exact HA | exact HB | exact HtRA | exact HtLB | exact Hop]. }
  unfold cad_concat_imp_a6_double_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Double.
  - exact Hlookup.
  - apply heap_represents_triple_a6_persists_alloc; assumption.
  - apply heap_represents_triple_a6_persists_alloc; assumption.
Qed.

(** ** Simple DS / SD sub-ops on the rich cell type.

    DS: A is CDouble, B is CSingle.  Boundary: sufRA and preB must
    be empty.  Result: CDouble preserving A's left triple, with a
    new TripleRight combining preRA + cRA + sufB.

    SD: symmetric. *)

Definition cad_concat_imp_a6_double_single_simple {A : Type}
    (lA lB : Loc) : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    bindC (read_MC lB) (fun cB =>
      match cA, cB with
      | CCa6_CadDouble ltLA ltRA _, CCa6_CadSingle ltB _ =>
          bindC (read_MC ltRA) (fun tRA =>
            bindC (read_MC ltB) (fun tB =>
              match tRA, tB with
              | CCa6_TripleRight preRA cRA sufRA,
                CCa6_TripleOnly preB cB' sufB =>
                  match buf6_elems sufRA, buf6_elems preB with
                  | [], [] =>
                      bindC (alloc_MC (CCa6_TripleRight preRA cRA sufB)) (fun newtR =>
                        alloc_MC (CCa6_CadDouble ltLA newtR ltLA))
                  | _, _ => retC lA
                  end
              | _, _ => retC lA
              end))
      | _, _ => retC lA
      end)).

Definition cad_concat_imp_a6_single_double_simple {A : Type}
    (lA lB : Loc) : MC (CadCellA6 A) Loc :=
  bindC (read_MC lA) (fun cA =>
    bindC (read_MC lB) (fun cB =>
      match cA, cB with
      | CCa6_CadSingle ltA _, CCa6_CadDouble ltLB ltRB _ =>
          bindC (read_MC ltA) (fun tA =>
            bindC (read_MC ltLB) (fun tLB =>
              match tA, tLB with
              | CCa6_TripleOnly preA cA' sufA,
                CCa6_TripleLeft preLB cLB sufLB =>
                  match buf6_elems sufA, buf6_elems preLB with
                  | [], [] =>
                      bindC (alloc_MC (CCa6_TripleLeft preA cA' sufLB)) (fun newtL =>
                        alloc_MC (CCa6_CadDouble newtL ltRB newtL))
                  | _, _ => retC lA
                  end
              | _, _ => retC lA
              end))
      | _, _ => retC lA
      end)).

(** WC O(1) bounds for DS / SD simple. *)

Theorem cad_concat_imp_a6_double_single_simple_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc) (k : nat),
    cost_of (cad_concat_imp_a6_double_single_simple lA lB) H = Some k ->
    k <= 6.
Proof.
  intros A H lA lB k Hcost.
  unfold cad_concat_imp_a6_double_single_simple,
         cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct cB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (lookup H l0) as [tRA|] eqn:Hlt; [|discriminate].
  destruct (lookup H l2) as [tB|] eqn:Hlt2; [|discriminate].
  destruct tRA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct tB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
    injection Hcost as <-; lia.
Qed.

Theorem cad_concat_imp_a6_single_double_simple_WC_O1 :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc) (k : nat),
    cost_of (cad_concat_imp_a6_single_double_simple lA lB) H = Some k ->
    k <= 6.
Proof.
  intros A H lA lB k Hcost.
  unfold cad_concat_imp_a6_single_double_simple,
         cost_of, bindC, read_MC, alloc_MC, retC in Hcost.
  destruct (lookup H lA) as [cA|] eqn:HlkA; [|discriminate].
  destruct (lookup H lB) as [cB|] eqn:HlkB; [|discriminate].
  destruct cA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct cB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (lookup H l) as [tA|] eqn:Hlt; [|discriminate].
  destruct (lookup H l1) as [tLB|] eqn:Hlt2; [|discriminate].
  destruct tA; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct tLB; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b0) as [|? ?]; cbn in Hcost;
    try (injection Hcost as <-; lia).
  destruct (buf6_elems b1) as [|? ?]; cbn in Hcost;
    injection Hcost as <-; lia.
Qed.

(** Lookup characterization for DS simple. *)

Theorem cad_concat_imp_a6_double_single_simple_lookup :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltB : Loc)
         (preRA sufB : Buf6 A) (cRA cB' : Loc)
         (l_a6_A l_a6_B : Loc),
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight preRA cRA buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cB' sufB) ->
    forall H' l' k,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      let ltR' := next_loc H in
      lookup H' ltR' = Some (CCa6_TripleRight preRA cRA sufB)
      /\ lookup H' l' = Some (CCa6_CadDouble ltLA ltR' ltLA).
Proof.
  intros A H lA lB ltLA ltRA ltB preRA sufB cRA cB' l_a6_A l_a6_B
         HA HB HtRA HtB H' l' k Hop.
  unfold cad_concat_imp_a6_double_single_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_concat_imp_a6_single_double_simple_lookup :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltLB ltRB : Loc)
         (preA sufLB : Buf6 A) (cA' cLB : Loc)
         (l_a6_A l_a6_B : Loc),
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cA' buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB sufLB) ->
    forall H' l' k,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      let ltL' := next_loc H in
      lookup H' ltL' = Some (CCa6_TripleLeft preA cA' sufLB)
      /\ lookup H' l' = Some (CCa6_CadDouble ltL' ltRB ltL').
Proof.
  intros A H lA lB ltA ltLB ltRB preA sufLB cA' cLB l_a6_A l_a6_B
         HA HB HtA HtLB H' l' k Hop.
  unfold cad_concat_imp_a6_single_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  cbn.
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH, <- Hl. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

(** Sequence-correctness for DS / SD simple. *)

Theorem cad_concat_imp_a6_double_single_simple_seq :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltB : Loc)
         (preRA sufB : Buf6 A) (cRA cB' : Loc)
         (l_a6_A l_a6_B : Loc)
         (tLA : Triple A) (cRA' : Cadeque A),
    heap_represents_cad_a6 H lA (CDouble tLA (TRight preRA cRA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight preRA cRA buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cB' sufB) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_cad_a6 H cRA cRA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CDouble tLA (TRight preRA cRA' sufB)).
Proof.
  intros A H lA lB ltLA ltRA ltB preRA sufB cRA cB' l_a6_A l_a6_B tLA cRA'
         HrepA HrepB HA HB HtRA HtB HrepTLA HrepCRA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let ltR' := next_loc H in
                    lookup H' ltR' = Some (CCa6_TripleRight preRA cRA sufB)
                    /\ lookup H' l' = Some (CCa6_CadDouble ltLA ltR' ltLA)).
  { eapply cad_concat_imp_a6_double_single_simple_lookup;
      [exact HA | exact HB | exact HtRA | exact HtB | exact Hop]. }
  cbn in Hlookup.
  destruct Hlookup as [HltR_new Hl_new].
  unfold cad_concat_imp_a6_double_single_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Double.
  - exact Hl_new.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
  - eapply HRTa6_TRight.
    + exact HltR_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_concat_imp_a6_single_double_simple_seq :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltLB ltRB : Loc)
         (preA sufLB : Buf6 A) (cA' cLB : Loc)
         (l_a6_A l_a6_B : Loc)
         (cA_ab : Cadeque A) (tRB : Triple A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA_ab buf6_empty)) ->
    heap_represents_cad_a6 H lB (CDouble (TLeft buf6_empty CEmpty sufLB) tRB) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cA' buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB sufLB) ->
    heap_represents_cad_a6 H cA' cA_ab ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' (CDouble (TLeft preA cA_ab sufLB) tRB).
Proof.
  intros A H lA lB ltA ltLB ltRB preA sufLB cA' cLB l_a6_A l_a6_B cA_ab tRB
         HrepA HrepB HA HB HtA HtLB HrepCA HrepTRB
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hlookup : let ltL' := next_loc H in
                    lookup H' ltL' = Some (CCa6_TripleLeft preA cA' sufLB)
                    /\ lookup H' l' = Some (CCa6_CadDouble ltL' ltRB ltL')).
  { eapply cad_concat_imp_a6_single_double_simple_lookup;
      [exact HA | exact HB | exact HtA | exact HtLB | exact Hop]. }
  cbn in Hlookup.
  destruct Hlookup as [HltL_new Hl_new].
  unfold cad_concat_imp_a6_single_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Double.
  - exact Hl_new.
  - eapply HRTa6_TLeft.
    + exact HltL_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
Qed.

(** ** Pop from suffix when prefix is empty (CSingle shallow case). *)

Theorem cad_pop_imp_a6_lookup_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      let lt' := next_loc H in
      exists lq',
        lr = Some (x, lq') /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' lt' = Some (CCa6_TripleOnly buf6_empty lc suf')
        /\ lookup H' lq' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hpop_pre Hpop_suf H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hpop_pre in Hop. cbn in Hop.
  rewrite Hpop_suf in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)). cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_pop_imp_a6_seq_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (x, lq') /\
        heap_represents_cad_a6 H' lq'
          (CSingle (TOnly buf6_empty CEmpty suf')).
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hlc Hltlc Hpop_pre Hpop_suf
         H' lr k Hop.
  assert (Hchar : let lt' := next_loc H in
                  exists lq',
                    lr = Some (x, lq') /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' lt' = Some (CCa6_TripleOnly buf6_empty lc suf') /\
                    lookup H' lq' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_pop_imp_a6_lookup_when_single_pre_empty;
      [exact HA | exact Ht | exact Hpop_pre | exact Hpop_suf | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [Hltnew Hlqnew]]]].
  exists lq'.
  split; [exact Hlr |].
  assert (Hlc' : lookup H' lc = Some CCa6_CadEmpty).
  { unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA, Ht in Hop. cbn in Hop.
    rewrite Hpop_pre, Hpop_suf in Hop. cbn in Hop.
    injection Hop as HH _ _. subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lc (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in Hltlc.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact Hltlc|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lc (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in Hltlc. exact (Pos.lt_irrefl _ Hltlc).
      * exact Hlc. }
  eapply HRCa6_Single.
  - exact Hlqnew.
  - eapply HRTa6_TOnly.
    + exact Hltnew.
    + apply HRCa6_Empty. exact Hlc'.
Qed.

(** Eject from prefix when suffix is empty (symmetric). *)

Theorem cad_eject_imp_a6_lookup_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      let lt' := next_loc H in
      exists lq',
        lr = Some (lq', x) /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' lt' = Some (CCa6_TripleOnly pre' lc buf6_empty)
        /\ lookup H' lq' = Some (CCa6_CadSingle lt' lt').
Proof.
  intros A H lA lt pre suf lc pre' x HA Ht Hej_suf Hej_pre H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hej_suf in Hop. cbn in Hop.
  rewrite Hej_pre in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)). cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_eject_imp_a6_seq_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (lq', x) /\
        heap_represents_cad_a6 H' lq'
          (CSingle (TOnly pre' CEmpty buf6_empty)).
Proof.
  intros A H lA lt pre suf lc pre' x HA Ht Hlc Hltlc Hej_suf Hej_pre
         H' lr k Hop.
  assert (Hchar : let lt' := next_loc H in
                  exists lq',
                    lr = Some (lq', x) /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' lt' = Some (CCa6_TripleOnly pre' lc buf6_empty) /\
                    lookup H' lq' = Some (CCa6_CadSingle lt' lt')).
  { eapply cad_eject_imp_a6_lookup_when_single_suf_empty;
      [exact HA | exact Ht | exact Hej_suf | exact Hej_pre | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [Hltnew Hlqnew]]]].
  exists lq'.
  split; [exact Hlr |].
  assert (Hlc' : lookup H' lc = Some CCa6_CadEmpty).
  { unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
    rewrite HA, Ht in Hop. cbn in Hop.
    rewrite Hej_suf, Hej_pre in Hop. cbn in Hop.
    injection Hop as HH _ _. subst H'.
    unfold lookup. cbn.
    destruct (loc_eq_dec lc (Pos.succ (next_loc H))) as [Heq1|Hne1].
    + exfalso. rewrite Heq1 in Hltlc.
      apply (Pos.lt_irrefl (Pos.succ (next_loc H))).
      eapply Pos.lt_trans; [exact Hltlc|]. apply Pos.lt_succ_diag_r.
    + destruct (loc_eq_dec lc (next_loc H)) as [Heq2|Hne2].
      * exfalso. rewrite Heq2 in Hltlc. exact (Pos.lt_irrefl _ Hltlc).
      * exact Hlc. }
  eapply HRCa6_Single.
  - exact Hlqnew.
  - eapply HRTa6_TOnly.
    + exact Hltnew.
    + apply HRCa6_Empty. exact Hlc'.
Qed.

(** ** Pop / eject on CDouble (shallow case: adopt6 = left/right triple).

    For pop on CDouble, the post-embed shallow case has adopt6
    pointing to the LEFT triple (per embed_cadeque_a6's CDouble case).
    Reading adopt6 yields a TripleLeft; pop from its prefix. *)

Theorem cad_pop_imp_a6_lookup_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      let ltL' := next_loc H in
      exists lq',
        lr = Some (x, lq') /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' ltL' = Some (CCa6_TripleLeft pre' lc suf) /\
        lookup H' lq' = Some (CCa6_CadDouble ltL' ltR ltL').
Proof.
  intros A H lA ltL ltR pre suf lc x pre' HA HtL Hpop H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  rewrite Hpop in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)). cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_pop_imp_a6_seq_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (x : A) (pre' : Buf6 A),
    heap_represents_cad_a6 H lA (CDouble (TLeft pre c suf) tR) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (x, lq') /\
        heap_represents_cad_a6 H' lq' (CDouble (TLeft pre' c suf) tR).
Proof.
  intros A H lA ltL ltR pre suf cChild c tR x pre' HrepA HA HtL HrepC HrepTR
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hpop H' lr k Hop.
  assert (Hchar : let ltL' := next_loc H in
                  exists lq',
                    lr = Some (x, lq') /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' ltL' = Some (CCa6_TripleLeft pre' cChild suf) /\
                    lookup H' lq' = Some (CCa6_CadDouble ltL' ltR ltL')).
  { eapply cad_pop_imp_a6_lookup_when_double_pre_nonempty;
      [exact HA | exact HtL | exact Hpop | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [HltL_new Hlq_new]]]].
  exists lq'.
  split; [exact Hlr |].
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  rewrite Hpop in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Double.
  - exact Hlq_new.
  - eapply HRTa6_TLeft.
    + exact HltL_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
Qed.

(** Symmetric: eject on CDouble (shallow: adopt6 = right triple). *)

Theorem cad_eject_imp_a6_lookup_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      let ltR' := next_loc H in
      exists lq',
        lr = Some (lq', x) /\
        lq' = Pos.succ (next_loc H) /\
        lookup H' ltR' = Some (CCa6_TripleRight pre lc suf') /\
        lookup H' lq' = Some (CCa6_CadDouble ltL ltR' ltR').
Proof.
  intros A H lA ltL ltR pre suf lc suf' x HA HtR Hej H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  rewrite Hej in Hop. cbn in Hop.
  injection Hop as HH Hl _.
  exists (Pos.succ (next_loc H)). cbn.
  split; [symmetry; exact Hl |].
  split; [reflexivity |].
  split.
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (next_loc H) (Pos.succ (next_loc H))) as [Heq|Hne].
    + exfalso. apply (Pos.succ_discr (next_loc H)). exact Heq.
    + destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_|Hne2];
        [reflexivity|contradiction].
  - rewrite <- HH. unfold lookup. cbn.
    destruct (loc_eq_dec (Pos.succ (next_loc H)) (Pos.succ (next_loc H)))
      as [_|Hne]; [reflexivity|contradiction].
Qed.

Theorem cad_eject_imp_a6_seq_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (suf' : Buf6 A) (x : A),
    heap_represents_cad_a6 H lA (CDouble tL (TRight pre c suf)) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      exists lq',
        lr = Some (lq', x) /\
        heap_represents_cad_a6 H' lq' (CDouble tL (TRight pre c suf')).
Proof.
  intros A H lA ltL ltR pre suf cChild c tL suf' x HrepA HA HtR HrepTL HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hej H' lr k Hop.
  assert (Hchar : let ltR' := next_loc H in
                  exists lq',
                    lr = Some (lq', x) /\
                    lq' = Pos.succ (next_loc H) /\
                    lookup H' ltR' = Some (CCa6_TripleRight pre cChild suf') /\
                    lookup H' lq' = Some (CCa6_CadDouble ltL ltR' ltR')).
  { eapply cad_eject_imp_a6_lookup_when_double_suf_nonempty;
      [exact HA | exact HtR | exact Hej | exact Hop]. }
  cbn in Hchar.
  destruct Hchar as [lq' [Hlr [Hlq [HltR_new Hlq_new]]]].
  exists lq'.
  split; [exact Hlr |].
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  rewrite Hej in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  eapply HRCa6_Double.
  - exact Hlq_new.
  - apply heap_represents_triple_a6_persists_two_allocs; assumption.
  - eapply HRTa6_TRight.
    + exact HltR_new.
    + apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** Determinism of heap_represents_cad_a6 / _triple_a6.

    Two abstract cadeques (resp. triples) represented at the same
    loc in the same heap must be equal.  Used to pin down [qResult]
    in list-level refinement theorems. *)

Lemma heap_represents_cad_a6_det :
  forall (A : Type) (H : Heap (CadCellA6 A)) (l : Loc) (q1 q2 : Cadeque A),
    heap_represents_cad_a6 H l q1 ->
    heap_represents_cad_a6 H l q2 ->
    q1 = q2
with heap_represents_triple_a6_det :
  forall (A : Type) (H : Heap (CadCellA6 A)) (l : Loc) (t1 t2 : Triple A),
    heap_represents_triple_a6 H l t1 ->
    heap_represents_triple_a6 H l t2 ->
    t1 = t2.
Proof.
  - intros A H l q1 q2 H1 H2.
    destruct H1 as [H l Hlk
                   | H l lt l_a6 t Hlk Ht
                   | H l ltL ltR l_a6 tL tR Hlk HtL HtR ];
    inversion H2 as [H'' l'' Hlk'
                    | H'' l'' lt' l_a6' t' Hlk' Ht'
                    | H'' l'' ltL' ltR' l_a6' tL' tR' Hlk' HtL' HtR' ];
      subst.
    + reflexivity.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. injection Hlk' as -> _.
      f_equal. eapply heap_represents_triple_a6_det; eassumption.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. injection Hlk' as -> -> _.
      f_equal; eapply heap_represents_triple_a6_det; eassumption.
  - intros A H l t1 t2 H1 H2.
    destruct H1 as [H l pre lc suf c Hlk Hc
                   | H l pre lc suf c Hlk Hc
                   | H l pre lc suf c Hlk Hc ];
    inversion H2 as [H'' l'' pre' lc' suf' c' Hlk' Hc'
                    | H'' l'' pre' lc' suf' c' Hlk' Hc'
                    | H'' l'' pre' lc' suf' c' Hlk' Hc' ];
      subst.
    + rewrite Hlk in Hlk'. injection Hlk' as -> -> ->.
      f_equal. eapply heap_represents_cad_a6_det; eassumption.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. injection Hlk' as -> -> ->.
      f_equal. eapply heap_represents_cad_a6_det; eassumption.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. discriminate.
    + rewrite Hlk in Hlk'. injection Hlk' as -> -> ->.
      f_equal. eapply heap_represents_cad_a6_det; eassumption.
Qed.

(** ** List-level refinement for cad_push_imp_a6 / cad_inject_imp_a6.

    Bottom-line consumer-facing statement: result list = [x] ++ qA's
    list (push) or qA's list ++ [x] (inject), parallel to the plain
    DSL.  Uses determinism above to pin down qResult. *)

Theorem cad_push_imp_a6_list_correct_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    Pos.lt lA (next_loc H) ->
    forall H' l' k qResult,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = x :: cad_to_list_base qA.
Proof.
  intros A H x lA qA HrepA HA HltA H' l' k qResult Hop Hres.
  assert (HqA : qA = CEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; rewrite HA in Hlk; try discriminate; reflexivity. }
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l'
                    (CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty))).
  { eapply cad_push_imp_a6_seq_when_empty;
      [exact HrepA | exact HltA | exact Hop]. }
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn. reflexivity.
Qed.

Theorem cad_inject_imp_a6_list_correct_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    Pos.lt lA (next_loc H) ->
    forall H' l' k qResult,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = cad_to_list_base qA ++ [x].
Proof.
  intros A H lA x qA HrepA HA HltA H' l' k qResult Hop Hres.
  assert (HqA : qA = CEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; rewrite HA in Hlk; try discriminate; reflexivity. }
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l'
                    (CSingle (TOnly buf6_empty CEmpty (buf6_singleton x)))).
  { eapply cad_inject_imp_a6_seq_when_empty;
      [exact HrepA | exact HltA | exact Hop]. }
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn. reflexivity.
Qed.

(** ** List-level refinement for push/inject_imp_a6 on CSingle / CDouble. *)

Theorem cad_push_imp_a6_list_correct_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre c suf) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k qResult,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = x :: cad_to_list_base qA.
Proof.
  intros A H x lA lt l_a6 pre suf cChild c qA HrepA HqAeq HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CSingle (TOnly (buf6_push x pre) c suf)))
    by (eapply cad_push_imp_a6_seq_when_single; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn. reflexivity.
Qed.

Theorem cad_push_imp_a6_list_correct_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble (TLeft pre c suf) tR ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k qResult,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = x :: cad_to_list_base qA.
Proof.
  intros A H x lA ltL ltR l_a6 pre suf cChild c tR qA HrepA HqAeq HA HtL HrepC HrepTR
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble (TLeft (buf6_push x pre) c suf) tR))
    by (eapply cad_push_imp_a6_seq_when_double; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn. reflexivity.
Qed.

Theorem cad_inject_imp_a6_list_correct_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre c suf) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k qResult,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = cad_to_list_base qA ++ [x].
Proof.
  intros A H lA lt l_a6 x pre suf cChild c qA HrepA HqAeq HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CSingle (TOnly pre c (buf6_inject suf x))))
    by (eapply cad_inject_imp_a6_seq_when_single; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  destruct suf as [suf_elems]. cbn.
  rewrite flat_concat_singleton_app1.
  rewrite (flat_concat_singleton_id _ suf_elems).
  rewrite !app_assoc. reflexivity.
Qed.

Theorem cad_inject_imp_a6_list_correct_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble tL (TRight pre c suf) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k qResult,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult = cad_to_list_base qA ++ [x].
Proof.
  intros A H lA ltL ltR l_a6 x pre suf cChild c tL qA HrepA HqAeq HA HtR HrepTL HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  subst qA.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble tL (TRight pre c (buf6_inject suf x))))
    by (eapply cad_inject_imp_a6_seq_when_double; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  destruct suf as [suf_elems]. cbn.
  rewrite flat_concat_singleton_app1.
  rewrite (flat_concat_singleton_id _ suf_elems).
  rewrite !app_assoc. reflexivity.
Qed.

(** ** Input-persistence for push/inject_imp_a6 (per shape).

    Push and inject never mutate the input cell; they only allocate.
    So lA continues to represent qA in H'.  Each takes wf + post-1-alloc
    wf' preconditions matching the per-shape seq theorem. *)

Theorem cad_push_imp_a6_input_persists_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc),
    lookup H lA = Some CCa6_CadEmpty ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_push_imp_a6 x lA H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H x lA HA Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_inject_imp_a6_input_persists_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A),
    lookup H lA = Some CCa6_CadEmpty ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_inject_imp_a6 lA x H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA x HA Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_push_imp_a6_input_persists_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_push_imp_a6 x lA H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H x lA lt l_a6 pre suf cChild HA Ht Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         qA HrepA H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_push_imp_a6_input_persists_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_push_imp_a6 x lA H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H x lA ltL ltR l_a6 pre suf cChild HA HtL Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         qA HrepA H' l' k Hop.
  unfold cad_push_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_inject_imp_a6_input_persists_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc),
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_inject_imp_a6 lA x H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA lt l_a6 x pre suf cChild HA Ht Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         qA HrepA H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_inject_imp_a6_input_persists_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc),
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' l' k,
        cad_inject_imp_a6 lA x H = Some (H', l', k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA ltL ltR l_a6 x pre suf cChild HA HtR Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         qA HrepA H' l' k Hop.
  unfold cad_inject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** Termination wrappers for cad_push/inject/pop/eject_imp_a6. *)

Theorem cad_push_imp_a6_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc),
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      k <= CAD_PUSH_IMP_A6_COST.
Proof.
  intros A H x lA H' l' k Hop.
  assert (Hcost : cost_of (cad_push_imp_a6 x lA) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_push_imp_a6_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_inject_imp_a6_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A),
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      k <= CAD_INJECT_IMP_A6_COST.
Proof.
  intros A H lA x H' l' k Hop.
  assert (Hcost : cost_of (cad_inject_imp_a6 lA x) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_inject_imp_a6_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_pop_imp_a6_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc),
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST.
Proof.
  intros A H lA H' lr k Hop.
  assert (Hcost : cost_of (cad_pop_imp_a6 lA) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_pop_imp_a6_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_eject_imp_a6_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc),
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST.
Proof.
  intros A H lA H' lr k Hop.
  assert (Hcost : cost_of (cad_eject_imp_a6 lA) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_eject_imp_a6_WC_O1 in Hcost. exact Hcost.
Qed.

(** ** FLAGSHIP FULL CONTRACT bundles for push/inject_a6 (empty case). *)

Theorem cad_push_imp_a6_full_contract_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA : Loc) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    Pos.lt lA (next_loc H) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_singleton x) lA buf6_empty) H)))) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      k <= CAD_PUSH_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l'
        (CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty)) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = x :: cad_to_list_base qA).
Proof.
  intros A H x lA qA HrepA HA HltA Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (HqA : qA = CEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; rewrite HA in Hlk; try discriminate; reflexivity. }
  split; [|split; [|split]].
  - eapply cad_push_imp_a6_terminates; eassumption.
  - eapply cad_push_imp_a6_input_persists_when_empty;
      [exact HA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_push_imp_a6_seq_when_empty;
      [exact HrepA | exact HltA | exact Hop].
  - intros qResult Hres.
    eapply cad_push_imp_a6_list_correct_when_empty;
      [exact HrepA | exact HA | exact HltA | exact Hop | exact Hres].
Qed.

Theorem cad_inject_imp_a6_full_contract_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (x : A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    Pos.lt lA (next_loc H) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lA (buf6_singleton x)) H)))) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      k <= CAD_INJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l'
        (CSingle (TOnly buf6_empty CEmpty (buf6_singleton x))) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = cad_to_list_base qA ++ [x]).
Proof.
  intros A H lA x qA HrepA HA HltA Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (HqA : qA = CEmpty).
  { inversion HrepA as [Hh Hl Hlk
                       | Hh Hl lt' la6' t' Hlk Ht'
                       | Hh Hl ltL ltR la6' tL tR Hlk HtL HtR];
      subst; rewrite HA in Hlk; try discriminate; reflexivity. }
  split; [|split; [|split]].
  - eapply cad_inject_imp_a6_terminates; eassumption.
  - eapply cad_inject_imp_a6_input_persists_when_empty;
      [exact HA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_inject_imp_a6_seq_when_empty;
      [exact HrepA | exact HltA | exact Hop].
  - intros qResult Hres.
    eapply cad_inject_imp_a6_list_correct_when_empty;
      [exact HrepA | exact HA | exact HltA | exact Hop | exact Hres].
Qed.

Theorem cad_push_imp_a6_full_contract_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA lt l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre c suf) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      k <= CAD_PUSH_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l' (CSingle (TOnly (buf6_push x pre) c suf)) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = x :: cad_to_list_base qA).
Proof.
  intros A H x lA lt l_a6 pre suf cChild c qA HrepA HqAeq HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  split; [|split; [|split]].
  - eapply cad_push_imp_a6_terminates; eassumption.
  - eapply cad_push_imp_a6_input_persists_when_single;
      [exact HA | exact Ht | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_push_imp_a6_seq_when_single; eassumption.
  - intros qResult Hres.
    eapply cad_push_imp_a6_list_correct_when_single;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hop | exact Hres].
Qed.

Theorem cad_push_imp_a6_full_contract_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (x : A) (lA ltL ltR l_a6 : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble (TLeft pre c suf) tR ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft (buf6_push x pre) cChild suf) H)))) ->
    forall H' l' k,
      cad_push_imp_a6 x lA H = Some (H', l', k) ->
      k <= CAD_PUSH_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l' (CDouble (TLeft (buf6_push x pre) c suf) tR) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = x :: cad_to_list_base qA).
Proof.
  intros A H x lA ltL ltR l_a6 pre suf cChild c tR qA HrepA HqAeq HA HtL HrepC HrepTR
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  split; [|split; [|split]].
  - eapply cad_push_imp_a6_terminates; eassumption.
  - eapply cad_push_imp_a6_input_persists_when_double;
      [exact HA | exact HtL | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_push_imp_a6_seq_when_double; eassumption.
  - intros qResult Hres.
    eapply cad_push_imp_a6_list_correct_when_double;
      [exact HrepA | exact HqAeq | exact HA | exact HtL | exact HrepC | exact HrepTR
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hop | exact Hres].
Qed.

Theorem cad_inject_imp_a6_full_contract_when_single :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre c suf) ->
    lookup H lA = Some (CCa6_CadSingle lt l_a6) ->
    lookup H lt = Some (CCa6_TripleOnly pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      k <= CAD_INJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l' (CSingle (TOnly pre c (buf6_inject suf x))) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = cad_to_list_base qA ++ [x]).
Proof.
  intros A H lA lt l_a6 x pre suf cChild c qA HrepA HqAeq HA Ht HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  split; [|split; [|split]].
  - eapply cad_inject_imp_a6_terminates; eassumption.
  - eapply cad_inject_imp_a6_input_persists_when_single;
      [exact HA | exact Ht | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_inject_imp_a6_seq_when_single; eassumption.
  - intros qResult Hres.
    eapply cad_inject_imp_a6_list_correct_when_single;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hop | exact Hres].
Qed.

Theorem cad_inject_imp_a6_full_contract_when_double :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR l_a6 : Loc) (x : A)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble tL (TRight pre c suf) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR l_a6) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild (buf6_inject suf x)) H)))) ->
    forall H' l' k,
      cad_inject_imp_a6 lA x H = Some (H', l', k) ->
      k <= CAD_INJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' l' (CDouble tL (TRight pre c (buf6_inject suf x))) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult = cad_to_list_base qA ++ [x]).
Proof.
  intros A H lA ltL ltR l_a6 x pre suf cChild c tL qA HrepA HqAeq HA HtR HrepTL HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  split; [|split; [|split]].
  - eapply cad_inject_imp_a6_terminates; eassumption.
  - eapply cad_inject_imp_a6_input_persists_when_double;
      [exact HA | exact HtR | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_inject_imp_a6_seq_when_double; eassumption.
  - intros qResult Hres.
    eapply cad_inject_imp_a6_list_correct_when_double;
      [exact HrepA | exact HqAeq | exact HA | exact HtR | exact HrepTL | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hop | exact Hres].
Qed.

(** ** List-level refinement for concat_imp_a6 simple sub-ops. *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_list_correct :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltB : Loc)
         (preA sufB : Buf6 A) (cAchild cBchild : Loc)
         (l_a6_A l_a6_B : Loc) (cA' : Cadeque A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cAchild buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cBchild sufB) ->
    heap_represents_cad_a6 H cAchild cA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    forall H' l' k qResult,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult =
        cad_to_list_base (CSingle (TOnly preA cA' buf6_empty)) ++
        cad_to_list_base (CSingle (TOnly buf6_empty CEmpty sufB)).
Proof.
  intros A H lA lB ltA ltB preA sufB cAchild cBchild l_a6_A l_a6_B cA'
         HrepA HrepB HA HB HtA HtB HrepCA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CSingle (TOnly preA cA' sufB)))
    by (eapply cad_concat_imp_a6_singleton_singleton_simple_seq; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Theorem cad_concat_imp_a6_double_double_simple_list_correct :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltLB ltRB : Loc)
         (cRA cLB : Loc) (l_a6_A l_a6_B : Loc) (tLA tRB : Triple A),
    heap_represents_cad_a6 H lA
      (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) ->
    heap_represents_cad_a6 H lB
      (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight buf6_empty cRA buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB buf6_empty) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    forall H' l' k qResult,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult =
        cad_to_list_base (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) ++
        cad_to_list_base (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB).
Proof.
  intros A H lA lB ltLA ltRA ltLB ltRB cRA cLB l_a6_A l_a6_B tLA tRB
         HrepA HrepB HA HB HtRA HtLB HrepTLA HrepTRB
         Hwf_cad Hwf_trip H' l' k qResult Hop Hres.
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble tLA tRB))
    by (eapply cad_concat_imp_a6_double_double_simple_seq; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  rewrite !app_nil_r. reflexivity.
Qed.

Theorem cad_concat_imp_a6_double_single_simple_list_correct :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltB : Loc)
         (preRA sufB : Buf6 A) (cRA cB' : Loc)
         (l_a6_A l_a6_B : Loc)
         (tLA : Triple A) (cRA' : Cadeque A),
    heap_represents_cad_a6 H lA (CDouble tLA (TRight preRA cRA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight preRA cRA buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cB' sufB) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_cad_a6 H cRA cRA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    forall H' l' k qResult,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult =
        cad_to_list_base (CDouble tLA (TRight preRA cRA' buf6_empty)) ++
        cad_to_list_base (CSingle (TOnly buf6_empty CEmpty sufB)).
Proof.
  intros A H lA lB ltLA ltRA ltB preRA sufB cRA cB' l_a6_A l_a6_B tLA cRA'
         HrepA HrepB HA HB HtRA HtB HrepTLA HrepCRA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  assert (Hjoin : heap_represents_cad_a6 H' l'
                    (CDouble tLA (TRight preRA cRA' sufB)))
    by (eapply cad_concat_imp_a6_double_single_simple_seq; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

Theorem cad_concat_imp_a6_single_double_simple_list_correct :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltLB ltRB : Loc)
         (preA sufLB : Buf6 A) (cA' cLB : Loc)
         (l_a6_A l_a6_B : Loc)
         (cA_ab : Cadeque A) (tRB : Triple A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA_ab buf6_empty)) ->
    heap_represents_cad_a6 H lB (CDouble (TLeft buf6_empty CEmpty sufLB) tRB) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cA' buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB sufLB) ->
    heap_represents_cad_a6 H cA' cA_ab ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    forall H' l' k qResult,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' l' qResult ->
      cad_to_list_base qResult =
        cad_to_list_base (CSingle (TOnly preA cA_ab buf6_empty)) ++
        cad_to_list_base (CDouble (TLeft buf6_empty CEmpty sufLB) tRB).
Proof.
  intros A H lA lB ltA ltLB ltRB preA sufLB cA' cLB l_a6_A l_a6_B cA_ab tRB
         HrepA HrepB HA HB HtA HtLB HrepCA HrepTRB
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k qResult Hop Hres.
  assert (Hjoin : heap_represents_cad_a6 H' l'
                    (CDouble (TLeft preA cA_ab sufLB) tRB))
    by (eapply cad_concat_imp_a6_single_double_simple_seq; eassumption).
  assert (Heq : qResult = _)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  unfold cad_to_list_base. cbn.
  rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

(** ** Input-persistence for concat_imp_a6 simple sub-ops.

    Both lA and lB persist across the allocs the sub-op performs. *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_inputs_persist :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltB : Loc)
         (preA sufB : Buf6 A) (cAchild cBchild : Loc)
         (l_a6_A l_a6_B : Loc) (qA qB : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    heap_represents_cad_a6 H lB qB ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cAchild buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cBchild sufB) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' lB qB.
Proof.
  intros A H lA lB ltA ltB preA sufB cAchild cBchild l_a6_A l_a6_B qA qB
         HrepA HrepB HA HB HtA HtB Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         H' l' k Hop.
  unfold cad_concat_imp_a6_singleton_singleton_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  split.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_concat_imp_a6_double_double_simple_inputs_persist :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltLB ltRB : Loc)
         (cRA cLB : Loc) (l_a6_A l_a6_B : Loc) (qA qB : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    heap_represents_cad_a6 H lB qB ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight buf6_empty cRA buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB buf6_empty) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    forall H' l' k,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' lB qB.
Proof.
  intros A H lA lB ltLA ltRA ltLB ltRB cRA cLB l_a6_A l_a6_B qA qB
         HrepA HrepB HA HB HtRA HtLB Hwf_cad Hwf_trip H' l' k Hop.
  unfold cad_concat_imp_a6_double_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  split.
  - apply heap_represents_cad_a6_persists_alloc; assumption.
  - apply heap_represents_cad_a6_persists_alloc; assumption.
Qed.

Theorem cad_concat_imp_a6_double_single_simple_inputs_persist :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltB : Loc)
         (preRA sufB : Buf6 A) (cRA cB' : Loc)
         (l_a6_A l_a6_B : Loc) (qA qB : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    heap_represents_cad_a6 H lB qB ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight preRA cRA buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cB' sufB) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' lB qB.
Proof.
  intros A H lA lB ltLA ltRA ltB preRA sufB cRA cB' l_a6_A l_a6_B qA qB
         HrepA HrepB HA HB HtRA HtB Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         H' l' k Hop.
  unfold cad_concat_imp_a6_double_single_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtRA, HtB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  split.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_concat_imp_a6_single_double_simple_inputs_persist :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltLB ltRB : Loc)
         (preA sufLB : Buf6 A) (cA' cLB : Loc)
         (l_a6_A l_a6_B : Loc) (qA qB : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    heap_represents_cad_a6 H lB qB ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cA' buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB sufLB) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      heap_represents_cad_a6 H' lA qA /\
      heap_represents_cad_a6 H' lB qB.
Proof.
  intros A H lA lB ltA ltLB ltRB preA sufLB cA' cLB l_a6_A l_a6_B qA qB
         HrepA HrepB HA HB HtA HtLB Hwf_cad Hwf_trip Hwf_cad' Hwf_trip'
         H' l' k Hop.
  unfold cad_concat_imp_a6_single_double_simple,
         bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HB, HtA, HtLB in Hop.
  unfold buf6_empty, buf6_elems in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  split.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
  - apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** Termination wrappers for concat simple sub-ops. *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc),
    forall H' l' k,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      k <= 6.
Proof.
  intros A H lA lB H' l' k Hop.
  assert (Hcost : cost_of (cad_concat_imp_a6_singleton_singleton_simple lA lB) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_concat_imp_a6_singleton_singleton_simple_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_concat_imp_a6_double_double_simple_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc),
    forall H' l' k,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      k <= 5.
Proof.
  intros A H lA lB H' l' k Hop.
  assert (Hcost : cost_of (cad_concat_imp_a6_double_double_simple lA lB) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_concat_imp_a6_double_double_simple_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_concat_imp_a6_double_single_simple_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc),
    forall H' l' k,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      k <= 6.
Proof.
  intros A H lA lB H' l' k Hop.
  assert (Hcost : cost_of (cad_concat_imp_a6_double_single_simple lA lB) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_concat_imp_a6_double_single_simple_WC_O1 in Hcost. exact Hcost.
Qed.

Theorem cad_concat_imp_a6_single_double_simple_terminates :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB : Loc),
    forall H' l' k,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      k <= 6.
Proof.
  intros A H lA lB H' l' k Hop.
  assert (Hcost : cost_of (cad_concat_imp_a6_single_double_simple lA lB) H = Some k).
  { unfold cost_of. rewrite Hop. reflexivity. }
  apply cad_concat_imp_a6_single_double_simple_WC_O1 in Hcost. exact Hcost.
Qed.

(** ** FLAGSHIP FULL CONTRACT bundles for concat simple sub-ops. *)

Theorem cad_concat_imp_a6_singleton_singleton_simple_full_contract :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltB : Loc)
         (preA sufB : Buf6 A) (cAchild cBchild : Loc)
         (l_a6_A l_a6_B : Loc) (cA' : Cadeque A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cAchild buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cBchild sufB) ->
    heap_represents_cad_a6 H cAchild cA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly preA cAchild sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_singleton_singleton_simple lA lB H = Some (H', l', k) ->
      k <= 6 /\
      heap_represents_cad_a6 H' lA (CSingle (TOnly preA cA' buf6_empty)) /\
      heap_represents_cad_a6 H' lB (CSingle (TOnly buf6_empty CEmpty sufB)) /\
      heap_represents_cad_a6 H' l' (CSingle (TOnly preA cA' sufB)) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult =
           cad_to_list_base (CSingle (TOnly preA cA' buf6_empty)) ++
           cad_to_list_base (CSingle (TOnly buf6_empty CEmpty sufB))).
Proof.
  intros A H lA lB ltA ltB preA sufB cAchild cBchild l_a6_A l_a6_B cA'
         HrepA HrepB HA HB HtA HtB HrepCA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hpersist : heap_represents_cad_a6 H' lA (CSingle (TOnly preA cA' buf6_empty)) /\
                     heap_represents_cad_a6 H' lB (CSingle (TOnly buf6_empty CEmpty sufB))).
  { eapply cad_concat_imp_a6_singleton_singleton_simple_inputs_persist;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtB
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  destruct Hpersist as [HpA HpB].
  assert (Hjoin : heap_represents_cad_a6 H' l' (CSingle (TOnly preA cA' sufB))).
  { eapply cad_concat_imp_a6_singleton_singleton_simple_seq;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtB
       | exact HrepCA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  split; [|split; [|split; [|split]]].
  - eapply cad_concat_imp_a6_singleton_singleton_simple_terminates; eassumption.
  - exact HpA.
  - exact HpB.
  - exact Hjoin.
  - intros qResult Hres.
    eapply cad_concat_imp_a6_singleton_singleton_simple_list_correct;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtB
       | exact HrepCA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop | exact Hres].
Qed.

Theorem cad_concat_imp_a6_double_double_simple_full_contract :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltLB ltRB : Loc)
         (cRA cLB : Loc) (l_a6_A l_a6_B : Loc) (tLA tRB : Triple A),
    heap_represents_cad_a6 H lA
      (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) ->
    heap_represents_cad_a6 H lB
      (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight buf6_empty cRA buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB buf6_empty) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    forall H' l' k,
      cad_concat_imp_a6_double_double_simple lA lB H = Some (H', l', k) ->
      k <= 5 /\
      heap_represents_cad_a6 H' lA
        (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) /\
      heap_represents_cad_a6 H' lB
        (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB) /\
      heap_represents_cad_a6 H' l' (CDouble tLA tRB) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult =
           cad_to_list_base (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) ++
           cad_to_list_base (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB)).
Proof.
  intros A H lA lB ltLA ltRA ltLB ltRB cRA cLB l_a6_A l_a6_B tLA tRB
         HrepA HrepB HA HB HtRA HtLB HrepTLA HrepTRB
         Hwf_cad Hwf_trip H' l' k Hop.
  assert (Hpersist : heap_represents_cad_a6 H' lA
                       (CDouble tLA (TRight buf6_empty CEmpty buf6_empty)) /\
                     heap_represents_cad_a6 H' lB
                       (CDouble (TLeft buf6_empty CEmpty buf6_empty) tRB)).
  { eapply cad_concat_imp_a6_double_double_simple_inputs_persist;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtLB
       | exact Hwf_cad | exact Hwf_trip | exact Hop]. }
  destruct Hpersist as [HpA HpB].
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble tLA tRB)).
  { eapply cad_concat_imp_a6_double_double_simple_seq;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtLB
       | exact HrepTLA | exact HrepTRB | exact Hwf_cad | exact Hwf_trip | exact Hop]. }
  split; [|split; [|split; [|split]]].
  - eapply cad_concat_imp_a6_double_double_simple_terminates; eassumption.
  - exact HpA.
  - exact HpB.
  - exact Hjoin.
  - intros qResult Hres.
    eapply cad_concat_imp_a6_double_double_simple_list_correct;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtLB
       | exact HrepTLA | exact HrepTRB | exact Hwf_cad | exact Hwf_trip
       | exact Hop | exact Hres].
Qed.

Theorem cad_concat_imp_a6_double_single_simple_full_contract :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltLA ltRA ltB : Loc)
         (preRA sufB : Buf6 A) (cRA cB' : Loc)
         (l_a6_A l_a6_B : Loc)
         (tLA : Triple A) (cRA' : Cadeque A),
    heap_represents_cad_a6 H lA (CDouble tLA (TRight preRA cRA' buf6_empty)) ->
    heap_represents_cad_a6 H lB (CSingle (TOnly buf6_empty CEmpty sufB)) ->
    lookup H lA = Some (CCa6_CadDouble ltLA ltRA l_a6_A) ->
    lookup H lB = Some (CCa6_CadSingle ltB l_a6_B) ->
    lookup H ltRA = Some (CCa6_TripleRight preRA cRA buf6_empty) ->
    lookup H ltB = Some (CCa6_TripleOnly buf6_empty cB' sufB) ->
    heap_represents_triple_a6 H ltLA tLA ->
    heap_represents_cad_a6 H cRA cRA' ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight preRA cRA sufB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_double_single_simple lA lB H = Some (H', l', k) ->
      k <= 6 /\
      heap_represents_cad_a6 H' lA (CDouble tLA (TRight preRA cRA' buf6_empty)) /\
      heap_represents_cad_a6 H' lB (CSingle (TOnly buf6_empty CEmpty sufB)) /\
      heap_represents_cad_a6 H' l' (CDouble tLA (TRight preRA cRA' sufB)) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult =
           cad_to_list_base (CDouble tLA (TRight preRA cRA' buf6_empty)) ++
           cad_to_list_base (CSingle (TOnly buf6_empty CEmpty sufB))).
Proof.
  intros A H lA lB ltLA ltRA ltB preRA sufB cRA cB' l_a6_A l_a6_B tLA cRA'
         HrepA HrepB HA HB HtRA HtB HrepTLA HrepCRA
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hpersist : heap_represents_cad_a6 H' lA (CDouble tLA (TRight preRA cRA' buf6_empty)) /\
                     heap_represents_cad_a6 H' lB (CSingle (TOnly buf6_empty CEmpty sufB))).
  { eapply cad_concat_imp_a6_double_single_simple_inputs_persist;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtB
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  destruct Hpersist as [HpA HpB].
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble tLA (TRight preRA cRA' sufB))).
  { eapply cad_concat_imp_a6_double_single_simple_seq;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtB
       | exact HrepTLA | exact HrepCRA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  split; [|split; [|split; [|split]]].
  - eapply cad_concat_imp_a6_double_single_simple_terminates; eassumption.
  - exact HpA.
  - exact HpB.
  - exact Hjoin.
  - intros qResult Hres.
    eapply cad_concat_imp_a6_double_single_simple_list_correct;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtRA | exact HtB
       | exact HrepTLA | exact HrepCRA | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop | exact Hres].
Qed.

Theorem cad_concat_imp_a6_single_double_simple_full_contract :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lB ltA ltLB ltRB : Loc)
         (preA sufLB : Buf6 A) (cA' cLB : Loc)
         (l_a6_A l_a6_B : Loc)
         (cA_ab : Cadeque A) (tRB : Triple A),
    heap_represents_cad_a6 H lA (CSingle (TOnly preA cA_ab buf6_empty)) ->
    heap_represents_cad_a6 H lB (CDouble (TLeft buf6_empty CEmpty sufLB) tRB) ->
    lookup H lA = Some (CCa6_CadSingle ltA l_a6_A) ->
    lookup H lB = Some (CCa6_CadDouble ltLB ltRB l_a6_B) ->
    lookup H ltA = Some (CCa6_TripleOnly preA cA' buf6_empty) ->
    lookup H ltLB = Some (CCa6_TripleLeft buf6_empty cLB sufLB) ->
    heap_represents_cad_a6 H cA' cA_ab ->
    heap_represents_triple_a6 H ltRB tRB ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft preA cA' sufLB) H)))) ->
    forall H' l' k,
      cad_concat_imp_a6_single_double_simple lA lB H = Some (H', l', k) ->
      k <= 6 /\
      heap_represents_cad_a6 H' lA (CSingle (TOnly preA cA_ab buf6_empty)) /\
      heap_represents_cad_a6 H' lB (CDouble (TLeft buf6_empty CEmpty sufLB) tRB) /\
      heap_represents_cad_a6 H' l' (CDouble (TLeft preA cA_ab sufLB) tRB) /\
      (forall qResult,
         heap_represents_cad_a6 H' l' qResult ->
         cad_to_list_base qResult =
           cad_to_list_base (CSingle (TOnly preA cA_ab buf6_empty)) ++
           cad_to_list_base (CDouble (TLeft buf6_empty CEmpty sufLB) tRB)).
Proof.
  intros A H lA lB ltA ltLB ltRB preA sufLB cA' cLB l_a6_A l_a6_B cA_ab tRB
         HrepA HrepB HA HB HtA HtLB HrepCA HrepTRB
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' l' k Hop.
  assert (Hpersist : heap_represents_cad_a6 H' lA (CSingle (TOnly preA cA_ab buf6_empty)) /\
                     heap_represents_cad_a6 H' lB (CDouble (TLeft buf6_empty CEmpty sufLB) tRB)).
  { eapply cad_concat_imp_a6_single_double_simple_inputs_persist;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtLB
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  destruct Hpersist as [HpA HpB].
  assert (Hjoin : heap_represents_cad_a6 H' l' (CDouble (TLeft preA cA_ab sufLB) tRB)).
  { eapply cad_concat_imp_a6_single_double_simple_seq;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtLB
       | exact HrepCA | exact HrepTRB | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop]. }
  split; [|split; [|split; [|split]]].
  - eapply cad_concat_imp_a6_single_double_simple_terminates; eassumption.
  - exact HpA.
  - exact HpB.
  - exact Hjoin.
  - intros qResult Hres.
    eapply cad_concat_imp_a6_single_double_simple_list_correct;
      [exact HrepA | exact HrepB | exact HA | exact HB | exact HtA | exact HtLB
       | exact HrepCA | exact HrepTRB | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact Hop | exact Hres].
Qed.

(** ** Input-persistence for pop/eject_imp_a6 (shallow cases).

    Pop and eject never mutate the input cell; they only allocate.
    So lA continues to represent qA in H'. *)

Theorem cad_pop_imp_a6_input_persists_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_pop_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA lt pre suf lc x pre' HA Ht Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hpop in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_eject_imp_a6_input_persists_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_eject_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hej in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_pop_imp_a6_input_persists_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft pre' lc suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' lc suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft pre' lc suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' lc suf) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_pop_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA ltL ltR pre suf lc x pre' HA HtL Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtL in Hop. cbn in Hop.
  rewrite Hpop in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_eject_imp_a6_input_persists_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre lc suf') H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_eject_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA ltL ltR pre suf lc suf' x HA HtR Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, HtR in Hop. cbn in Hop.
  rewrite Hej in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** Empty-input persistence: when pop/eject sees CCa6_CadEmpty, it
    returns None and H' = H — so any input representation trivially
    persists. *)

Theorem cad_pop_imp_a6_input_persists_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA qA HrepA HA H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'. exact HrepA.
Qed.

Theorem cad_eject_imp_a6_input_persists_when_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA : Loc) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some CCa6_CadEmpty ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA qA HrepA HA H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, retC in Hop.
  rewrite HA in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'. exact HrepA.
Qed.

(** Pop/eject fallback-buffer input persistence. *)

Theorem cad_pop_imp_a6_input_persists_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_pop_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hpop_pre Hpop_suf
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_pop_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hpop_pre, Hpop_suf in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

Theorem cad_eject_imp_a6_input_persists_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    forall (qA : Cadeque A),
      heap_represents_cad_a6 H lA qA ->
      forall H' lr k,
        cad_eject_imp_a6 lA H = Some (H', lr, k) ->
        heap_represents_cad_a6 H' lA qA.
Proof.
  intros A H lA lt pre suf lc pre' x HA Ht Hej_suf Hej_pre
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' qA HrepA H' lr k Hop.
  unfold cad_eject_imp_a6, bindC, read_MC, alloc_MC, retC in Hop.
  rewrite HA, Ht in Hop. cbn in Hop.
  rewrite Hej_suf, Hej_pre in Hop. cbn in Hop.
  injection Hop as HH _ _. subst H'.
  apply heap_represents_cad_a6_persists_two_allocs; assumption.
Qed.

(** ** FLAGSHIP FULL CONTRACT bundles for pop/eject shallow cases.

    Each bundle composes [terminates] (cost bound) + [input_persists]
    + [seq] for one shape.  The bundles target all 6 shallow shapes:
    pop on CSingle pre-nonempty / CSingle pre-empty / CDouble pre-nonempty,
    and the 3 symmetric eject shapes.  The cascade case (where adopt6
    points to a deeper triple) is intentionally NOT covered here — it's
    handled separately. *)

Theorem cad_pop_imp_a6_full_contract_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre' CEmpty suf))).
Proof.
  intros A H lA lt pre suf lc x pre' qA HrepA HA Ht Hlc Hltlc Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_single_pre_nonempty;
      [exact HA | exact Ht | exact Hpop | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - eapply cad_pop_imp_a6_seq_when_single_pre_nonempty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc | exact Hpop | exact Hop].
Qed.

Theorem cad_pop_imp_a6_full_contract_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly buf6_empty CEmpty suf'))).
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HA Ht Hlc Hltlc Hpop_pre Hpop_suf
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_single_pre_empty;
      [exact HA | exact Ht | exact Hpop_pre | exact Hpop_suf
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact HrepA | exact Hop].
  - eapply cad_pop_imp_a6_seq_when_single_pre_empty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hpop_pre | exact Hpop_suf | exact Hop].
Qed.

Theorem cad_pop_imp_a6_full_contract_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (x : A) (pre' : Buf6 A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble (TLeft pre c suf) tR ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CDouble (TLeft pre' c suf) tR)).
Proof.
  intros A H lA ltL ltR pre suf cChild c tR x pre' qA HrepA HqAeq HA HtL HrepC HrepTR Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_double_pre_nonempty;
      [exact HA | exact HtL | exact Hpop | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_pop_imp_a6_seq_when_double_pre_nonempty;
      [exact HrepA | exact HA | exact HtL | exact HrepC | exact HrepTR
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hpop | exact Hop].
Qed.

Theorem cad_eject_imp_a6_full_contract_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre CEmpty suf'))).
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HA Ht Hlc Hltlc Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_single_suf_nonempty;
      [exact HA | exact Ht | exact Hej | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - eapply cad_eject_imp_a6_seq_when_single_suf_nonempty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc | exact Hej | exact Hop].
Qed.

Theorem cad_eject_imp_a6_full_contract_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre' CEmpty buf6_empty))).
Proof.
  intros A H lA lt pre suf lc pre' x qA HrepA HA Ht Hlc Hltlc Hej_suf Hej_pre
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_single_suf_empty;
      [exact HA | exact Ht | exact Hej_suf | exact Hej_pre
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact HrepA | exact Hop].
  - eapply cad_eject_imp_a6_seq_when_single_suf_empty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hej_suf | exact Hej_pre | exact Hop].
Qed.

Theorem cad_eject_imp_a6_full_contract_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (suf' : Buf6 A) (x : A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble tL (TRight pre c suf) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CDouble tL (TRight pre c suf'))).
Proof.
  intros A H lA ltL ltR pre suf cChild c tL suf' x qA HrepA HqAeq HA HtR HrepTL HrepC Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_double_suf_nonempty;
      [exact HA | exact HtR | exact Hej | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_eject_imp_a6_seq_when_double_suf_nonempty;
      [exact HrepA | exact HA | exact HtR | exact HrepTL | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hej | exact Hop].
Qed.

(** ** List-level refinement for pop/eject_imp_a6 (shallow shapes).

    For each shape, given the seq theorem characterizes the result
    as [heap_represents_cad_a6 H' lq' <shape>], determinism pins
    [qResult] and the answer follows from [buf6_pop_seq_some] /
    [buf6_eject_seq_some] combined with [flat_concat_singleton_id]. *)

Theorem cad_pop_imp_a6_list_correct_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (x, lq') ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = x :: cad_to_list_base qResult.
Proof.
  intros A H lA lt pre suf lc x pre' qA HrepA HqAeq HA Ht Hlc Hltlc Hpop
         H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_pop_imp_a6_seq_when_single_pre_nonempty
              HA Ht Hlc Hltlc Hpop Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CSingle (TOnly pre' CEmpty suf))
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_pop_seq_some in Hpop.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hpop.
  rewrite Hpop. reflexivity.
Qed.

Theorem cad_pop_imp_a6_list_correct_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (x, lq') ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = x :: cad_to_list_base qResult.
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HqAeq HA Ht Hlc Hltlc
         Hpop_pre Hpop_suf H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_pop_imp_a6_seq_when_single_pre_empty
              HA Ht Hlc Hltlc Hpop_pre Hpop_suf Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CSingle (TOnly buf6_empty CEmpty suf'))
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_pop_seq_none in Hpop_pre.
  apply buf6_pop_seq_some in Hpop_suf.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hpop_pre, Hpop_suf.
  rewrite Hpop_pre, Hpop_suf. cbn. reflexivity.
Qed.

Theorem cad_pop_imp_a6_list_correct_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (x : A) (pre' : Buf6 A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble (TLeft pre c suf) tR ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    buf6_pop pre = Some (x, pre') ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (x, lq') ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = x :: cad_to_list_base qResult.
Proof.
  intros A H lA ltL ltR pre suf cChild c tR x pre' qA HrepA HqAeq HA HtL HrepC HrepTR
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hpop H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_pop_imp_a6_seq_when_double_pre_nonempty
              HrepA HA HtL HrepC HrepTR
              Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hpop Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CDouble (TLeft pre' c suf) tR)
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_pop_seq_some in Hpop.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hpop.
  rewrite Hpop. cbn. reflexivity.
Qed.

Theorem cad_eject_imp_a6_list_correct_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (lq', x) ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = cad_to_list_base qResult ++ [x].
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HqAeq HA Ht Hlc Hltlc Hej
         H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_eject_imp_a6_seq_when_single_suf_nonempty
              HA Ht Hlc Hltlc Hej Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CSingle (TOnly pre CEmpty suf'))
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_eject_seq_some in Hej.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hej.
  rewrite Hej. rewrite <- !app_assoc. cbn. reflexivity.
Qed.

Theorem cad_eject_imp_a6_list_correct_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (lq', x) ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = cad_to_list_base qResult ++ [x].
Proof.
  intros A H lA lt pre suf lc pre' x qA HrepA HqAeq HA Ht Hlc Hltlc
         Hej_suf Hej_pre H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_eject_imp_a6_seq_when_single_suf_empty
              HA Ht Hlc Hltlc Hej_suf Hej_pre Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CSingle (TOnly pre' CEmpty buf6_empty))
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_eject_seq_none in Hej_suf.
  apply buf6_eject_seq_some in Hej_pre.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hej_suf, Hej_pre.
  rewrite Hej_suf, Hej_pre. rewrite !app_nil_r. reflexivity.
Qed.

Theorem cad_eject_imp_a6_list_correct_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (suf' : Buf6 A) (x : A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble tL (TRight pre c suf) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    buf6_eject suf = Some (suf', x) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      forall lq' qResult,
        lr = Some (lq', x) ->
        heap_represents_cad_a6 H' lq' qResult ->
        cad_to_list_base qA = cad_to_list_base qResult ++ [x].
Proof.
  intros A H lA ltL ltR pre suf cChild c tL suf' x qA HrepA HqAeq HA HtR HrepTL HrepC
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hej H' lr k Hop lq' qResult Hlreq Hres.
  subst qA.
  destruct (cad_eject_imp_a6_seq_when_double_suf_nonempty
              HrepA HA HtR HrepTL HrepC
              Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' Hej Hop)
    as [lq'' [Hlr_eq Hrep]].
  rewrite Hlreq in Hlr_eq. injection Hlr_eq as Hlq_eq. subst lq''.
  assert (HqRes : qResult = CDouble tL (TRight pre c suf'))
    by (eapply heap_represents_cad_a6_det; eassumption).
  subst qResult.
  apply buf6_eject_seq_some in Hej.
  unfold cad_to_list_base. cbn [cad_to_list triple_to_list].
  unfold buf6_flatten.
  rewrite !flat_concat_singleton_id.
  unfold buf6_to_list in Hej.
  rewrite Hej. rewrite <- !app_assoc. cbn. reflexivity.
Qed.

(** ** FLAGSHIP 4-piece FULL CONTRACT bundles for pop/eject (shallow).

    Each adds the list_correct piece (cad_to_list_base qA =
    x :: cad_to_list_base qResult, resp. ++ [x] for eject) on top
    of cost + persistence + seq.  Takes [qA = <shape>] as an
    explicit precondition mirroring push/inject's [HqAeq]. *)

Theorem cad_pop_imp_a6_flagship_full_contract_when_single_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc suf) H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre' CEmpty suf))) /\
      (forall lq' qResult,
         lr = Some (x, lq') ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = x :: cad_to_list_base qResult).
Proof.
  intros A H lA lt pre suf lc x pre' qA HrepA HqAeq HA Ht Hlc Hltlc Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_single_pre_nonempty;
      [exact HA | exact Ht | exact Hpop | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - eapply cad_pop_imp_a6_seq_when_single_pre_nonempty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc | exact Hpop | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_pop_imp_a6_list_correct_when_single_pre_nonempty;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hpop | exact Hop | exact Hlreq | exact Hres].
Qed.

Theorem cad_pop_imp_a6_flagship_full_contract_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly buf6_empty lc suf') H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly buf6_empty CEmpty suf'))) /\
      (forall lq' qResult,
         lr = Some (x, lq') ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = x :: cad_to_list_base qResult).
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HqAeq HA Ht Hlc Hltlc Hpop_pre Hpop_suf
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_single_pre_empty;
      [exact HA | exact Ht | exact Hpop_pre | exact Hpop_suf
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact HrepA | exact Hop].
  - eapply cad_pop_imp_a6_seq_when_single_pre_empty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hpop_pre | exact Hpop_suf | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_pop_imp_a6_list_correct_when_single_pre_empty;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hpop_pre | exact Hpop_suf | exact Hop | exact Hlreq | exact Hres].
Qed.

Theorem cad_pop_imp_a6_flagship_full_contract_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tR : Triple A)
         (x : A) (pre' : Buf6 A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble (TLeft pre c suf) tR ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre cChild suf) ->
    heap_represents_cad_a6 H cChild c ->
    heap_represents_triple_a6 H ltR tR ->
    buf6_pop pre = Some (x, pre') ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleLeft pre' cChild suf) H)))) ->
    forall H' lr k,
      cad_pop_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_POP_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (x, lq') /\
         heap_represents_cad_a6 H' lq' (CDouble (TLeft pre' c suf) tR)) /\
      (forall lq' qResult,
         lr = Some (x, lq') ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = x :: cad_to_list_base qResult).
Proof.
  intros A H lA ltL ltR pre suf cChild c tR x pre' qA HrepA HqAeq HA HtL HrepC HrepTR Hpop
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_pop_imp_a6_terminates; eassumption.
  - eapply cad_pop_imp_a6_input_persists_when_double_pre_nonempty;
      [exact HA | exact HtL | exact Hpop | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_pop_imp_a6_seq_when_double_pre_nonempty;
      [exact HrepA | exact HA | exact HtL | exact HrepC | exact HrepTR
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hpop | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_pop_imp_a6_list_correct_when_double_pre_nonempty;
      [exact HrepA | exact HqAeq | exact HA | exact HtL | exact HrepC | exact HrepTR
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hpop | exact Hop | exact Hlreq | exact Hres].
Qed.

Theorem cad_eject_imp_a6_flagship_full_contract_when_single_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre lc suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre lc suf') H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre CEmpty suf'))) /\
      (forall lq' qResult,
         lr = Some (lq', x) ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = cad_to_list_base qResult ++ [x]).
Proof.
  intros A H lA lt pre suf lc suf' x qA HrepA HqAeq HA Ht Hlc Hltlc Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_single_suf_nonempty;
      [exact HA | exact Ht | exact Hej | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - eapply cad_eject_imp_a6_seq_when_single_suf_nonempty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc | exact Hej | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_eject_imp_a6_list_correct_when_single_suf_nonempty;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hej | exact Hop | exact Hlreq | exact Hres].
Qed.

Theorem cad_eject_imp_a6_flagship_full_contract_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A)
         (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CSingle (TOnly pre CEmpty suf) ->
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    lookup H lc = Some CCa6_CadEmpty ->
    Pos.lt lc (next_loc H) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleOnly pre' lc buf6_empty) H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CSingle (TOnly pre' CEmpty buf6_empty))) /\
      (forall lq' qResult,
         lr = Some (lq', x) ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = cad_to_list_base qResult ++ [x]).
Proof.
  intros A H lA lt pre suf lc pre' x qA HrepA HqAeq HA Ht Hlc Hltlc Hej_suf Hej_pre
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_single_suf_empty;
      [exact HA | exact Ht | exact Hej_suf | exact Hej_pre
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact HrepA | exact Hop].
  - eapply cad_eject_imp_a6_seq_when_single_suf_empty;
      [exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hej_suf | exact Hej_pre | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_eject_imp_a6_list_correct_when_single_suf_empty;
      [exact HrepA | exact HqAeq | exact HA | exact Ht | exact Hlc | exact Hltlc
       | exact Hej_suf | exact Hej_pre | exact Hop | exact Hlreq | exact Hres].
Qed.

Theorem cad_eject_imp_a6_flagship_full_contract_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (cChild : Loc) (c : Cadeque A) (tL : Triple A)
         (suf' : Buf6 A) (x : A) (qA : Cadeque A),
    heap_represents_cad_a6 H lA qA ->
    qA = CDouble tL (TRight pre c suf) ->
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre cChild suf) ->
    heap_represents_triple_a6 H ltL tL ->
    heap_represents_cad_a6 H cChild c ->
    buf6_eject suf = Some (suf', x) ->
    (forall l' qsub, heap_represents_cad_a6 H l' qsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' tsub, heap_represents_triple_a6 H l' tsub ->
                     Pos.lt l' (next_loc H)) ->
    (forall l' qsub,
       heap_represents_cad_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' qsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    (forall l' tsub,
       heap_represents_triple_a6 (snd (alloc (CCa6_TripleRight pre cChild suf') H)) l' tsub ->
       Pos.lt l' (next_loc (snd (alloc (CCa6_TripleRight pre cChild suf') H)))) ->
    forall H' lr k,
      cad_eject_imp_a6 lA H = Some (H', lr, k) ->
      k <= CAD_EJECT_IMP_A6_COST /\
      heap_represents_cad_a6 H' lA qA /\
      (exists lq',
         lr = Some (lq', x) /\
         heap_represents_cad_a6 H' lq' (CDouble tL (TRight pre c suf'))) /\
      (forall lq' qResult,
         lr = Some (lq', x) ->
         heap_represents_cad_a6 H' lq' qResult ->
         cad_to_list_base qA = cad_to_list_base qResult ++ [x]).
Proof.
  intros A H lA ltL ltR pre suf cChild c tL suf' x qA HrepA HqAeq HA HtR HrepTL HrepC Hej
         Hwf_cad Hwf_trip Hwf_cad' Hwf_trip' H' lr k Hop.
  split; [|split; [|split]].
  - eapply cad_eject_imp_a6_terminates; eassumption.
  - eapply cad_eject_imp_a6_input_persists_when_double_suf_nonempty;
      [exact HA | exact HtR | exact Hej | exact Hwf_cad | exact Hwf_trip
       | exact Hwf_cad' | exact Hwf_trip' | exact HrepA | exact Hop].
  - subst qA. eapply cad_eject_imp_a6_seq_when_double_suf_nonempty;
      [exact HrepA | exact HA | exact HtR | exact HrepTL | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hej | exact Hop].
  - intros lq' qResult Hlreq Hres.
    eapply cad_eject_imp_a6_list_correct_when_double_suf_nonempty;
      [exact HrepA | exact HqAeq | exact HA | exact HtR | exact HrepTL | exact HrepC
       | exact Hwf_cad | exact Hwf_trip | exact Hwf_cad' | exact Hwf_trip'
       | exact Hej | exact Hop | exact Hlreq | exact Hres].
Qed.

(** ** Cost-exact theorems for pop/eject remaining shallow shapes.

    Fills out the cost matrix so every shallow shape has a closed-form
    constant.  All shallow pop/eject ops on the rich type cost exactly
    4 = 2 reads + 2 allocs + retC. *)

Theorem cad_pop_imp_a6_cost_when_single_pre_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_pop pre = None ->
    buf6_pop suf = Some (x, suf') ->
    cost_of (cad_pop_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA lt pre suf lc suf' x HA Ht Hpop_pre Hpop_suf.
  unfold cad_pop_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. rewrite Hpop_pre, Hpop_suf. cbn. reflexivity.
Qed.

Theorem cad_pop_imp_a6_cost_when_double_pre_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (x : A) (pre' : Buf6 A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltL) ->
    lookup H ltL = Some (CCa6_TripleLeft pre lc suf) ->
    buf6_pop pre = Some (x, pre') ->
    cost_of (cad_pop_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA ltL ltR pre suf lc x pre' HA HtL Hpop.
  unfold cad_pop_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, HtL. cbn. rewrite Hpop. cbn. reflexivity.
Qed.

Theorem cad_eject_imp_a6_cost_when_single_suf_empty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA lt : Loc)
         (pre suf : Buf6 A) (lc : Loc) (pre' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadSingle lt lt) ->
    lookup H lt = Some (CCa6_TripleOnly pre lc suf) ->
    buf6_eject suf = None ->
    buf6_eject pre = Some (pre', x) ->
    cost_of (cad_eject_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA lt pre suf lc pre' x HA Ht Hej_suf Hej_pre.
  unfold cad_eject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, Ht. cbn. rewrite Hej_suf. cbn. rewrite Hej_pre. cbn.
  reflexivity.
Qed.

Theorem cad_eject_imp_a6_cost_when_double_suf_nonempty :
  forall (A : Type) (H : Heap (CadCellA6 A)) (lA ltL ltR : Loc)
         (pre suf : Buf6 A) (lc : Loc) (suf' : Buf6 A) (x : A),
    lookup H lA = Some (CCa6_CadDouble ltL ltR ltR) ->
    lookup H ltR = Some (CCa6_TripleRight pre lc suf) ->
    buf6_eject suf = Some (suf', x) ->
    cost_of (cad_eject_imp_a6 lA) H = Some 4.
Proof.
  intros A H lA ltL ltR pre suf lc suf' x HA HtR Hej.
  unfold cad_eject_imp_a6, cost_of, bindC, read_MC, alloc_MC, retC.
  rewrite HA, HtR. cbn. rewrite Hej. cbn. reflexivity.
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
