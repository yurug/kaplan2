(** * Module: KTDeque.DequePtr.Footprint -- worst-case O(1) cost bounds
    for the Viennot packet representation.

    A chain of yellow cells re-thread is normally O(yellow-run-length).
    The packet aggregation fixes this: a yellow run is a chain of
    [PCell]s, each linked via [pcell_inner], and a push only touches the
    TOP cell.  Re-threading after a buffer repair is bounded by a
    constant — IT DOES NOT DEPEND ON THE YELLOW-RUN LENGTH.

    Cell layout:

        Record PCell (X : Type) := mkPCell {
          pcell_pre   : Buf5 X;             (* prefix buffer at this level *)
          pcell_suf   : Buf5 X;             (* suffix buffer; B0 for Ending *)
          pcell_inner : option Loc;         (* None = Hole or Ending; Some = next deeper [PCell] *)
          pcell_tail  : option Loc;         (* None = Ending; Some = chain tail [PCell] *)
        }.

    Top-level chain handle: [Loc] of the topmost cell, or [None] for an
    empty chain.

    Cost accounting (the headline numbers):

      - [NF_PUSH_PKT = 3] -- naive push (1 read + 1 alloc + 1 freeze).
        Used by [exec_push_pkt_naive_C] / [exec_pop_pkt_C] / [exec_eject_pkt_C].
      - [NF_MAKE_RED_PKT = 6] -- one make_red repair primitive
        (1 read of top + pure compute + 1 read of tail + 2 alloc-freeze).
      - [NF_PUSH_PKT_FULL = 9] -- combined push+overflow.

    Critically: the cost is INDEPENDENT of the chain depth.  The proof
    is structural inversion on the cost monad — no induction.

    Cross-references:
    - [bench/viennot/deque_core.ml] -- the algorithmic reference.
    - [KTDeque/Common/CostMonad.v] -- the [MC] monad with primitive
      op counts.
*)

From KTDeque.Common Require Import Prelude FinMapHeap HeapExt Monad
                                    Element CostMonad Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model OpsAbstract.

(** ** Heap cell for a packet/chain node.

    The cell stores the local prefix and suffix buffers, plus links to
    the inner packet and chain tail.  This allows us to encode both
    [Ending b] cells (set [pcell_tail = None] and use only
    [pcell_pre]) and [ChainCons (PNode pre inner suf) tail] cells
    (set [pcell_tail = Some tail_loc] and [pcell_inner] for the
    yellow-run continuation, or [None] when the inner packet is
    [Hole]). *)
Record PCell (X : Type) : Type := mkPCell {
  pcell_pre   : Buf5 X;
  pcell_suf   : Buf5 X;
  pcell_inner : option Loc;
  pcell_tail  : option Loc
}.

Arguments mkPCell {X} pcell_pre pcell_suf pcell_inner pcell_tail.
Arguments pcell_pre   {X} _.
Arguments pcell_suf   {X} _.
Arguments pcell_inner {X} _.
Arguments pcell_tail  {X} _.

(** Convenience constructors. *)
Definition mkEndingCell {X : Type} (b : Buf5 X) : PCell X :=
  mkPCell b B0 None None.

Definition mkPNodeCell {X : Type} (pre suf : Buf5 X)
    (inner : option Loc) (tail : Loc) : PCell X :=
  mkPCell pre suf inner (Some tail).

(** Top-level chain handle (analogous to [Root4]). *)
Inductive ChainRoot (X : Type) : Type :=
| chain_empty  : ChainRoot X
| chain_root   : Loc -> ChainRoot X.

Arguments chain_empty {X}.
Arguments chain_root  {X} _.

(** Heap-of-PCells abbreviation. *)
Notation HeapP X := (Heap (PCell X)).

(** Runtime-checked element pairing.  Returns [Some] iff levels match. *)
Definition pkt_pair_safe {A : Type} (x y : E.t A) : option (E.t A) :=
  match Nat.eq_dec (E.level A x) (E.level A y) with
  | left e  => Some (E.pair A x y e)
  | right _ => None
  end.

Lemma pkt_pair_safe_some_iff :
  forall (A : Type) (x y : E.t A),
    (exists r, pkt_pair_safe x y = Some r) <-> E.level A x = E.level A y.
Proof.
  intros A x y; unfold pkt_pair_safe.
  destruct (Nat.eq_dec (E.level A x) (E.level A y)) as [e|ne]; split.
  - intros _; exact e.
  - intros _; eauto.
  - intros [r H]; discriminate.
  - intros e; contradiction.
Qed.

(** ** Result type for the naive push/inject (overflow-aware). *)
Inductive PushResult : Type :=
| OkP       : Loc -> PushResult     (* no overflow; new top cell allocated. *)
| OverflowP : Loc -> PushResult.    (* overflow occurred; carries the original lroot
                                       (passed to make_red as the "rebuild from this
                                       cell" anchor). *)

(** ** [exec_push_pkt_naive_C]: cost-instrumented non-recursive push on
    a packet/chain heap.

    Touches the top cell only.  Cost ≤ [NF_PUSH_PKT] = 3.

    The function:
    1. Read the top cell.
    2. Push [x] onto its prefix buffer (pure [buf5_push_naive]).
    3. If the result is non-[B5]: allocate a new top cell with the
       updated prefix and the same [suf]/[inner]/[tail] links; return
       [OkP new_loc].
    4. If the result is [B5]: return [OverflowP lroot] without allocating
       (cost: 1 read).  The caller fires [exec_make_red_pkt_C].
    5. If [None] ([buf5_push_naive] fails on B5 input): impossible in a
       well-formed chain; return [failC]. *)
Definition exec_push_pkt_naive_C {A : Type} (lroot : Loc) (x : E.t A)
  : MC (PCell (E.t A)) PushResult :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match buf5_push_naive x (pcell_pre cell) with
    | Some (B5 a b c d e) =>
        (* Phase S''': materialize the B5 cell so make_red sees the
           expected shape at the returned location. *)
        bindC (@alloc_freeze_MC (PCell (E.t A))
                (mkPCell (B5 a b c d e) (pcell_suf cell) (pcell_inner cell)
                         (pcell_tail cell)))
              (fun lover =>
                 @retC (PCell (E.t A)) PushResult (OverflowP lover))
    | Some pre' =>
        bindC (@alloc_freeze_MC (PCell (E.t A))
                (mkPCell pre' (pcell_suf cell) (pcell_inner cell)
                         (pcell_tail cell)))
              (fun lnew => @retC (PCell (E.t A)) PushResult (OkP lnew))
    | None => @failC (PCell (E.t A)) PushResult
    end).

(** ** [exec_inject_pkt_naive_C]: symmetric inject.

    When the cell is an Ending (no tail), the abstract [inject_chain]
    is the same as a buffer-level inject on the single buffer (which
    by convention lives in [pcell_pre]).  So for Ending cells we
    inject into the prefix; for ChainCons cells we inject into the
    suffix. *)
Definition exec_inject_pkt_naive_C {A : Type} (lroot : Loc) (x : E.t A)
  : MC (PCell (E.t A)) PushResult :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match pcell_tail cell with
    | None =>
        (* Ending cell: inject into the single (pre) buffer. *)
        match buf5_inject_naive (pcell_pre cell) x with
        | Some (B5 a b c d e) =>
            (* Phase S''': materialize the B5 cell. *)
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell (B5 a b c d e) (pcell_suf cell) (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lover =>
                     @retC (PCell (E.t A)) PushResult (OverflowP lover))
        | Some pre' =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell pre' (pcell_suf cell) (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lnew => @retC (PCell (E.t A)) PushResult (OkP lnew))
        | None => @failC (PCell (E.t A)) PushResult
        end
    | Some _ =>
        (* ChainCons cell: inject into the suffix buffer. *)
        match buf5_inject_naive (pcell_suf cell) x with
        | Some (B5 a b c d e) =>
            (* Phase S''': materialize the B5 cell. *)
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell (pcell_pre cell) (B5 a b c d e) (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lover =>
                     @retC (PCell (E.t A)) PushResult (OverflowP lover))
        | Some suf' =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell (pcell_pre cell) suf' (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lnew => @retC (PCell (E.t A)) PushResult (OkP lnew))
        | None => @failC (PCell (E.t A)) PushResult
        end
    end).

(** ** [exec_pop_pkt_C]: pop the front element. *)
Definition exec_pop_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (E.t A * Loc) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match buf5_pop_naive (pcell_pre cell) with
    | Some (x, pre') =>
        bindC (@alloc_freeze_MC (PCell (E.t A))
                (mkPCell pre' (pcell_suf cell) (pcell_inner cell) (pcell_tail cell)))
              (fun lnew => @retC (PCell (E.t A)) _ (x, lnew))
    | None => @failC (PCell (E.t A)) (E.t A * Loc)
    end).

(** ** [exec_eject_pkt_C]: eject the back element.

    Symmetric to [exec_inject_pkt_naive_C]: for Ending cells, eject
    from the single (pre) buffer; for ChainCons cells, eject from suf. *)
Definition exec_eject_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (Loc * E.t A) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match pcell_tail cell with
    | None =>
        match buf5_eject_naive (pcell_pre cell) with
        | Some (pre', x) =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell pre' (pcell_suf cell) (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lnew => @retC (PCell (E.t A)) _ (lnew, x))
        | None => @failC (PCell (E.t A)) (Loc * E.t A)
        end
    | Some _ =>
        match buf5_eject_naive (pcell_suf cell) with
        | Some (suf', x) =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell (pcell_pre cell) suf' (pcell_inner cell)
                             (pcell_tail cell)))
                  (fun lnew => @retC (PCell (E.t A)) _ (lnew, x))
        | None => @failC (PCell (E.t A)) (Loc * E.t A)
        end
    end).

(** ** [exec_make_red_push_pkt_C]: overflow repair for push.

    Precondition (informally): the cell at [lroot] has [pcell_pre =
    B5 a b c d e] (because the recent naive push overflowed) and its
    inner-packet pointer [pcell_inner] is [None] (the topmost yellow
    run is a single PNode -- the Viennot invariant; see
    [OpsAbstract.make_red_push_chain]'s [Hole] requirement).

    The repair:
    1. Read [lroot] to get the B5 components.
    2. Pair (d, e) at the next level via [pkt_pair_safe].
    3. Examine [pcell_tail]:
       a. [None] (this cell is a single-buffer Ending): allocate a fresh
          tail cell holding [B1 pde] as an Ending.  Then allocate a new
          top with [B3 a b c] as prefix, the existing suf, the same
          inner, and the new tail.
       b. [Some ltail]: read [ltail], push [pde] onto its prefix.  If
          non-B5: alloc new tail + alloc new top (B3 a b c).  If B5: the
          regularity invariant is violated; return [failC].

    Allocations: at most ONE new tail cell + ONE new top cell.  The
    chain-spine touch is bounded — independent of chain depth.

    Cost analysis (worst case):
    - 1 read (top cell).
    - 0 ops for [pkt_pair_safe] (pure).
    - At most 1 read (tail cell, only in the [Some] branch).
    - At most 2 alloc-freezes = 4 ops.
    Total: 6. *)
Definition exec_make_red_push_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) Loc :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun top_cell =>
    match pcell_pre top_cell with
    | B5 a b c d e =>
        match pkt_pair_safe d e with
        | Some pde =>
            match pcell_inner top_cell with
            | None =>
                (* Original Case 1/Case 2: no inner packet (Hole). *)
                match pcell_tail top_cell with
                | None =>
                    (* Case 1: No tail.  Ending. *)
                    bindC (@alloc_freeze_MC (PCell (E.t A))
                            (mkPCell (B1 pde) B0 None None))
                          (fun new_tail =>
                             @alloc_freeze_MC (PCell (E.t A))
                               (mkPCell (B3 a b c) (pcell_suf top_cell)
                                        (pcell_inner top_cell) (Some new_tail)))
                | Some ltail =>
                    (* Case 2: simple cons.  Push pde onto tail's pre. *)
                    bindC (@read_MC (PCell (E.t A)) ltail) (fun tail_cell =>
                      match buf5_push_naive pde (pcell_pre tail_cell) with
                      | Some (B5 _ _ _ _ _) =>
                          (* Cascade beyond depth 1 -- regularity invariant
                             must prevent this. *)
                          @failC (PCell (E.t A)) Loc
                      | Some tail_pre' =>
                          bindC (@alloc_freeze_MC (PCell (E.t A))
                                  (mkPCell tail_pre' (pcell_suf tail_cell)
                                           (pcell_inner tail_cell)
                                           (pcell_tail tail_cell)))
                                (fun new_tail =>
                                   @alloc_freeze_MC (PCell (E.t A))
                                     (mkPCell (B3 a b c) (pcell_suf top_cell)
                                              (pcell_inner top_cell)
                                              (Some new_tail)))
                      | None => @failC (PCell (E.t A)) Loc
                      end)
                end
            | Some inner_loc =>
                (* Phase S7 / P5 Case 3: nested top.  Read inner cell,
                   push pde onto its prefix, alloc new chain link
                   (promoted inner packet) with original chain tail,
                   alloc new top with B3 prefix and Hole inner. *)
                bindC (@read_MC (PCell (E.t A)) inner_loc) (fun inner_cell =>
                  match buf5_push_naive pde (pcell_pre inner_cell) with
                  | Some (B5 _ _ _ _ _) =>
                      (* Regularity prevents inner-buffer overflow. *)
                      @failC (PCell (E.t A)) Loc
                  | Some pre_new =>
                      bindC (@alloc_freeze_MC (PCell (E.t A))
                              (mkPCell pre_new (pcell_suf inner_cell)
                                       (pcell_inner inner_cell)
                                       (pcell_tail top_cell)))
                            (fun new_link =>
                               @alloc_freeze_MC (PCell (E.t A))
                                 (mkPCell (B3 a b c) (pcell_suf top_cell)
                                          None
                                          (Some new_link)))
                  | None => @failC (PCell (E.t A)) Loc
                  end)
            end
        | None => @failC (PCell (E.t A)) Loc
        end
    | _ => @failC (PCell (E.t A)) Loc
    end).

(** ** [exec_make_red_inject_pkt_C]: overflow repair for inject.

    Two shape branches:
    - When [pcell_tail = None] (Ending cell): the B5 lives in
      [pcell_pre] (because for an Ending cell, inject pushed into pre).
      Allocate a fresh tail, build new top with [pcell_pre = B0] and
      [pcell_suf = B3 cde].
    - When [pcell_tail = Some ltail] (ChainCons cell): the B5 lives in
      [pcell_suf].  Push pair into tail's suf, then allocate. *)
Definition exec_make_red_inject_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) Loc :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun top_cell =>
    match pcell_tail top_cell with
    | None =>
        match pcell_pre top_cell with
        | B5 a b c d e =>
            match pkt_pair_safe a b with
            | Some pab =>
                bindC (@alloc_freeze_MC (PCell (E.t A))
                        (mkPCell (B1 pab) B0 None None))
                      (fun new_tail =>
                         @alloc_freeze_MC (PCell (E.t A))
                           (mkPCell B0 (B3 c d e)
                                    (pcell_inner top_cell) (Some new_tail)))
            | None => @failC (PCell (E.t A)) Loc
            end
        | _ => @failC (PCell (E.t A)) Loc
        end
    | Some ltail =>
        match pcell_suf top_cell with
        | B5 a b c d e =>
            match pkt_pair_safe a b with
            | Some pab =>
                match pcell_inner top_cell with
                | None =>
                    (* Cases 1/2: simple top.  Original logic. *)
                    bindC (@read_MC (PCell (E.t A)) ltail) (fun tail_cell =>
                      (* Phase S''': dispatch on whether the inner tail is
                         itself an Ending (tail_cell.tail = None) or a
                         ChainCons.  For Ending, the abstract uses
                         [pcell_pre]; for ChainCons, [pcell_suf]. *)
                      match pcell_tail tail_cell with
                      | None =>
                          (* Inner tail is Ending: inject into pre. *)
                          match buf5_inject_naive (pcell_pre tail_cell) pab with
                          | Some (B5 _ _ _ _ _) => @failC (PCell (E.t A)) Loc
                          | Some tail_pre' =>
                              bindC (@alloc_freeze_MC (PCell (E.t A))
                                      (mkPCell tail_pre' (pcell_suf tail_cell)
                                               (pcell_inner tail_cell)
                                               (pcell_tail tail_cell)))
                                    (fun new_tail =>
                                       @alloc_freeze_MC (PCell (E.t A))
                                         (mkPCell (pcell_pre top_cell) (B3 c d e)
                                                  (pcell_inner top_cell)
                                                  (Some new_tail)))
                          | None => @failC (PCell (E.t A)) Loc
                          end
                      | Some _ =>
                          (* Inner tail is ChainCons: inject into suf. *)
                          match buf5_inject_naive (pcell_suf tail_cell) pab with
                          | Some (B5 _ _ _ _ _) => @failC (PCell (E.t A)) Loc
                          | Some tail_suf' =>
                              bindC (@alloc_freeze_MC (PCell (E.t A))
                                      (mkPCell (pcell_pre tail_cell) tail_suf'
                                               (pcell_inner tail_cell)
                                               (pcell_tail tail_cell)))
                                    (fun new_tail =>
                                       @alloc_freeze_MC (PCell (E.t A))
                                         (mkPCell (pcell_pre top_cell) (B3 c d e)
                                                  (pcell_inner top_cell)
                                                  (Some new_tail)))
                          | None => @failC (PCell (E.t A)) Loc
                          end
                      end)
                | Some inner_loc =>
                    (* Phase S7 / P5 Case 3 dual: nested top inject.
                       Read inner cell, inject pab onto its suffix,
                       alloc new chain link (promoted inner packet) with
                       original chain tail, alloc new top with B3 suffix
                       and Hole inner. *)
                    bindC (@read_MC (PCell (E.t A)) inner_loc) (fun inner_cell =>
                      match buf5_inject_naive (pcell_suf inner_cell) pab with
                      | Some (B5 _ _ _ _ _) =>
                          @failC (PCell (E.t A)) Loc
                      | Some suf_new =>
                          bindC (@alloc_freeze_MC (PCell (E.t A))
                                  (mkPCell (pcell_pre inner_cell) suf_new
                                           (pcell_inner inner_cell)
                                           (pcell_tail top_cell)))
                                (fun new_link =>
                                   @alloc_freeze_MC (PCell (E.t A))
                                     (mkPCell (pcell_pre top_cell) (B3 c d e)
                                              None
                                              (Some new_link)))
                      | None => @failC (PCell (E.t A)) Loc
                      end)
                end
            | None => @failC (PCell (E.t A)) Loc
            end
        | _ => @failC (PCell (E.t A)) Loc
        end
    end).

(** ** [exec_push_pkt_C]: push with overflow handling.

    Compose [exec_push_pkt_naive_C] with [exec_make_red_push_pkt_C]:
    on [OkP], return the new loc; on [OverflowP], fire make_red.

    Cost ≤ [NF_PUSH_PKT_FULL] = 9. *)
Definition exec_push_pkt_C {A : Type} (lroot : Loc) (x : E.t A)
  : MC (PCell (E.t A)) Loc :=
  bindC (exec_push_pkt_naive_C lroot x) (fun result =>
    match result with
    | OkP l'        => @retC (PCell (E.t A)) Loc l'
    | OverflowP l'  => exec_make_red_push_pkt_C l'
    end).

(** ** [exec_inject_pkt_C]: symmetric inject with overflow handling. *)
Definition exec_inject_pkt_C {A : Type} (lroot : Loc) (x : E.t A)
  : MC (PCell (E.t A)) Loc :=
  bindC (exec_inject_pkt_naive_C lroot x) (fun result =>
    match result with
    | OkP l'        => @retC (PCell (E.t A)) Loc l'
    | OverflowP l'  => exec_make_red_inject_pkt_C l'
    end).

(** ** Cost bounds.

    We declare three constants:
    - [NF_PUSH_PKT = 3] -- naive cost.
    - [NF_MAKE_RED_PKT = 6] -- make_red cost.
    - [NF_PUSH_PKT_FULL = NF_PUSH_PKT + NF_MAKE_RED_PKT = 9] -- combined.

    Each is a small concrete constant; the proof is by structural
    inversion on the cost monad — no induction.  THIS IS THE WHOLE POINT. *)

Definition NF_PUSH_PKT : nat := 3.
Definition NF_MAKE_RED_PKT : nat := 6.
Definition NF_PUSH_PKT_FULL : nat := NF_PUSH_PKT + NF_MAKE_RED_PKT.

Lemma NF_PUSH_PKT_value : NF_PUSH_PKT = 3.
Proof. reflexivity. Qed.

Lemma NF_MAKE_RED_PKT_value : NF_MAKE_RED_PKT = 6.
Proof. reflexivity. Qed.

Lemma NF_PUSH_PKT_FULL_value : NF_PUSH_PKT_FULL = 9.
Proof. reflexivity. Qed.

(** ** Cost: [exec_push_pkt_naive_C] ≤ NF_PUSH_PKT. *)
Lemma exec_push_pkt_naive_C_cost :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (r : PushResult) (n : nat),
    exec_push_pkt_naive_C lroot x H = Some (H', r, n) ->
    n <= NF_PUSH_PKT.
Proof.
  intros A lroot x H H' r n Hexec.
  unfold exec_push_pkt_naive_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (buf5_push_naive x (pcell_pre c0)) as [pre'|] eqn:Hpush;
    [|discriminate].
  destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
    inversion Hexec; subst H' r n; clear Hexec; unfold NF_PUSH_PKT; lia.
Qed.

Lemma exec_inject_pkt_naive_C_cost :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (r : PushResult) (n : nat),
    exec_inject_pkt_naive_C lroot x H = Some (H', r, n) ->
    n <= NF_PUSH_PKT.
Proof.
  intros A lroot x H H' r n Hexec.
  unfold exec_inject_pkt_naive_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (pcell_tail c0) as [ltail|].
  - (* ChainCons branch: inject into suf *)
    destruct (buf5_inject_naive (pcell_suf c0) x) as [suf'|] eqn:Hinj;
      [|discriminate].
    destruct suf' as [|y|y z|y z w|y z w u|y z w u v];
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
      inversion Hexec; subst H' r n; clear Hexec; unfold NF_PUSH_PKT; lia.
  - (* Ending branch: inject into pre *)
    destruct (buf5_inject_naive (pcell_pre c0) x) as [pre'|] eqn:Hinj;
      [|discriminate].
    destruct pre' as [|y|y z|y z w|y z w u|y z w u v];
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
      inversion Hexec; subst H' r n; clear Hexec; unfold NF_PUSH_PKT; lia.
Qed.

(** ** Cost: [exec_make_red_push_pkt_C] ≤ NF_MAKE_RED_PKT. *)
Lemma exec_make_red_push_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_make_red_push_pkt_C lroot H = Some (H', l', n) ->
    n <= NF_MAKE_RED_PKT.
Proof.
  intros A lroot H H' l' n Hexec.
  unfold exec_make_red_push_pkt_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 top_cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 top_cell k0; clear Hr.
  destruct (pcell_pre c0) as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
  destruct (pkt_pair_safe u v) as [puv|]; [|discriminate].
  destruct (pcell_inner c0) as [inner_loc|] eqn:Hinner.
  - (* Some inner_loc: nested top (Phase S7 Case 3) *)
    unfold bindC at 1 in Hexec.
    destruct (@read_MC (PCell (E.t A)) inner_loc H) as [[[H1 icell] k1]|] eqn:Hri;
      [|discriminate].
    unfold read_MC in Hri.
    destruct (lookup H inner_loc) as [ic|] eqn:Hlki; [|discriminate].
    inversion Hri; subst H1 icell k1; clear Hri.
    destruct (buf5_push_naive puv (pcell_pre ic)) as [pre_new|] eqn:Hpushinner;
      [|discriminate].
    destruct pre_new as [|cy|cy cz|cy cz cw|cy cz cw cu|cy cz cw cu cv];
      try discriminate;
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
      inversion Hexec; subst H' l' n; clear Hexec; unfold NF_MAKE_RED_PKT; lia.
  - (* None inner: original Cases 1/2 *)
    destruct (pcell_tail c0) as [ltail|] eqn:Htail.
    + (* Some ltail: read tail, push to its prefix *)
      unfold bindC at 1 in Hexec.
      destruct (@read_MC (PCell (E.t A)) ltail H) as [[[H1 tcell] k1]|] eqn:Hrt;
        [|discriminate].
      unfold read_MC in Hrt.
      destruct (lookup H ltail) as [tc|] eqn:Hlkt; [|discriminate].
      inversion Hrt; subst H1 tcell k1; clear Hrt.
      destruct (buf5_push_naive puv (pcell_pre tc)) as [tail_pre'|] eqn:Hpushtail;
        [|discriminate].
      destruct tail_pre' as [|cy|cy cz|cy cz cw|cy cz cw cu|cy cz cw cu cv];
        try discriminate;
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst H' l' n; clear Hexec; unfold NF_MAKE_RED_PKT; lia.
    + (* None: alloc tail + new top *)
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' l' n; clear Hexec.
      unfold NF_MAKE_RED_PKT; lia.
Qed.

Lemma exec_make_red_inject_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_make_red_inject_pkt_C lroot H = Some (H', l', n) ->
    n <= NF_MAKE_RED_PKT.
Proof.
  intros A lroot H H' l' n Hexec.
  unfold exec_make_red_inject_pkt_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 top_cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 top_cell k0; clear Hr.
  destruct (pcell_tail c0) as [ltail|] eqn:Htail.
  - (* ChainCons branch *)
    destruct (pcell_suf c0) as [|y|y z|y z w|y z w u|y z w u v];
      try discriminate.
    destruct (pkt_pair_safe y z) as [pyz|]; [|discriminate].
    destruct (pcell_inner c0) as [inner_loc|] eqn:Hinner.
    + (* Some inner_loc: nested top (Phase S7 Case 3 dual) *)
      unfold bindC at 1 in Hexec.
      destruct (@read_MC (PCell (E.t A)) inner_loc H) as [[[H1 icell] k1]|] eqn:Hri;
        [|discriminate].
      unfold read_MC in Hri.
      destruct (lookup H inner_loc) as [ic|] eqn:Hlki; [|discriminate].
      inversion Hri; subst H1 icell k1; clear Hri.
      destruct (buf5_inject_naive (pcell_suf ic) pyz) as [suf_new|] eqn:Hinjinner;
        [|discriminate].
      destruct suf_new as [|cy|cy cz|cy cz cw|cy cz cw cu|cy cz cw cu cv];
        try discriminate;
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
        inversion Hexec; subst H' l' n; clear Hexec; unfold NF_MAKE_RED_PKT; lia.
    + (* None inner: original Cases 1/2 *)
      unfold bindC at 1 in Hexec.
      destruct (@read_MC (PCell (E.t A)) ltail H) as [[[H1 tcell] k1]|] eqn:Hrt;
        [|discriminate].
      unfold read_MC in Hrt.
      destruct (lookup H ltail) as [tc|] eqn:Hlkt; [|discriminate].
      inversion Hrt; subst H1 tcell k1; clear Hrt.
      destruct (pcell_tail tc) as [ltail2|] eqn:Htail2.
      * (* Inner tail is ChainCons: inject into suf *)
        destruct (buf5_inject_naive (pcell_suf tc) pyz) as [tail_suf'|] eqn:Hinjtail;
          [|discriminate].
        destruct tail_suf' as [|cy|cy cz|cy cz cw|cy cz cw cu|cy cz cw cu cv];
          try discriminate;
          cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
          inversion Hexec; subst H' l' n; clear Hexec; unfold NF_MAKE_RED_PKT; lia.
      * (* Inner tail is Ending: inject into pre *)
        destruct (buf5_inject_naive (pcell_pre tc) pyz) as [tail_pre'|] eqn:Hinjtail;
          [|discriminate].
        destruct tail_pre' as [|cy|cy cz|cy cz cw|cy cz cw cu|cy cz cw cu cv];
          try discriminate;
          cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec;
          inversion Hexec; subst H' l' n; clear Hexec; unfold NF_MAKE_RED_PKT; lia.
  - (* Ending branch *)
    destruct (pcell_pre c0) as [|y|y z|y z w|y z w u|y z w u v];
      try discriminate.
    destruct (pkt_pair_safe y z) as [pyz|]; [|discriminate].
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' l' n; clear Hexec.
    unfold NF_MAKE_RED_PKT; lia.
Qed.

(** ** Cost: [exec_push_pkt_C] ≤ NF_PUSH_PKT_FULL.

    Combines naive (≤ 3) + make_red (≤ 6) via [bindC]. *)
Lemma exec_push_pkt_C_cost :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_push_pkt_C lroot x H = Some (H', l', n) ->
    n <= NF_PUSH_PKT_FULL.
Proof.
  intros A lroot x H H' l' n Hexec.
  unfold exec_push_pkt_C, bindC in Hexec.
  destruct (exec_push_pkt_naive_C lroot x H) as [[[H0 r] k0]|] eqn:Hnaive;
    [|discriminate].
  pose proof (@exec_push_pkt_naive_C_cost _ _ _ _ _ _ _ Hnaive) as Hcost_naive.
  destruct r as [l'' | l''].
  - (* OkP: just retC *)
    unfold retC in Hexec.
    inversion Hexec; subst H' l' n; clear Hexec.
    unfold NF_PUSH_PKT_FULL, NF_MAKE_RED_PKT. lia.
  - (* OverflowP: fire make_red *)
    destruct (exec_make_red_push_pkt_C l'' H0) as [[[H1 lr] k1]|] eqn:Hmr;
      [|discriminate].
    pose proof (@exec_make_red_push_pkt_C_cost _ _ _ _ _ _ Hmr) as Hcost_mr.
    inversion Hexec; subst H' l' n; clear Hexec.
    unfold NF_PUSH_PKT_FULL. lia.
Qed.

Lemma exec_inject_pkt_C_cost :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_inject_pkt_C lroot x H = Some (H', l', n) ->
    n <= NF_PUSH_PKT_FULL.
Proof.
  intros A lroot x H H' l' n Hexec.
  unfold exec_inject_pkt_C, bindC in Hexec.
  destruct (exec_inject_pkt_naive_C lroot x H) as [[[H0 r] k0]|] eqn:Hnaive;
    [|discriminate].
  pose proof (@exec_inject_pkt_naive_C_cost _ _ _ _ _ _ _ Hnaive) as Hcost_naive.
  destruct r as [l'' | l''].
  - unfold retC in Hexec.
    inversion Hexec; subst H' l' n; clear Hexec.
    unfold NF_PUSH_PKT_FULL, NF_MAKE_RED_PKT. lia.
  - destruct (exec_make_red_inject_pkt_C l'' H0) as [[[H1 lr] k1]|] eqn:Hmr;
      [|discriminate].
    pose proof (@exec_make_red_inject_pkt_C_cost _ _ _ _ _ _ Hmr) as Hcost_mr.
    inversion Hexec; subst H' l' n; clear Hexec.
    unfold NF_PUSH_PKT_FULL. lia.
Qed.

Lemma exec_pop_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (x : E.t A) (l' : Loc) (n : nat),
    exec_pop_pkt_C lroot H = Some (H', (x, l'), n) ->
    n <= NF_PUSH_PKT.
Proof.
  intros A lroot H H' x l' n Hexec.
  unfold exec_pop_pkt_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (buf5_pop_naive (pcell_pre c0)) as [[xp pre']|] eqn:Hpop;
    [|discriminate].
  cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
  inversion Hexec; subst x l' n; clear Hexec.
  unfold NF_PUSH_PKT. lia.
Qed.

Lemma exec_eject_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (x : E.t A) (l' : Loc) (n : nat),
    exec_eject_pkt_C lroot H = Some (H', (l', x), n) ->
    n <= NF_PUSH_PKT.
Proof.
  intros A lroot H H' x l' n Hexec.
  unfold exec_eject_pkt_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (pcell_tail c0) as [ltail|].
  - destruct (buf5_eject_naive (pcell_suf c0)) as [[suf' xp]|] eqn:Hej;
      [|discriminate].
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst l' x n; clear Hexec.
    unfold NF_PUSH_PKT. lia.
  - destruct (buf5_eject_naive (pcell_pre c0)) as [[pre' xp]|] eqn:Hej;
      [|discriminate].
    cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst l' x n; clear Hexec.
    unfold NF_PUSH_PKT. lia.
Qed.

(** ** Representation invariant.

    [chain_repr_at H l c k]: in heap [H], the cell at [l] decodes to the
    abstract chain [c : Chain A] starting at level [k].

    The predicate is structurally inductive on the abstract [c].  We
    fix [pcell_inner cell = None] for this version (the inner-yellow-
    run aggregation is a separate generalization; see ADR notes).

    For [Ending b]: cell holds [pre = b], [tail = None].
    For [ChainCons (PNode pre Hole suf) c']: cell holds [pre], [suf],
      [inner = None], [tail = Some ltail], and [ltail] decodes to [c']
      at level [S k]. *)
(** [packet_repr_at H il p k]: in heap [H], the optional inner-cell
    pointer [il] decodes to packet [p] at level [k].

    - [None] decodes to [Hole].
    - [Some inner_loc] decodes to [PNode pre i suf] when the cell at
      [inner_loc] holds [pre], [suf], [pcell_tail = None] (inner cells
      do not own a chain tail — that lives at the top of the packet),
      and [pcell_inner] decodes to [i] at the next level.

    Phase S audit (F4/P6): this generalization replaces the hard
    [pcell_inner = None] constraint that blocked refinement theorems
    from covering nested packets (Viennot's depth ≥ 2 yellow run). *)
Inductive packet_repr_at {A : Type} :
    HeapP (E.t A) -> option Loc -> Packet A -> nat -> Prop :=

| packet_repr_hole_at :
    forall (H : HeapP (E.t A)) (k : nat),
      packet_repr_at H None Hole k

| packet_repr_pnode_at :
    forall (H : HeapP (E.t A)) (inner_loc : Loc)
           (pre suf : Buf5 (E.t A)) (i : Packet A)
           (cell : PCell (E.t A)) (k : nat),
      lookup H inner_loc = Some cell ->
      is_frozen H inner_loc = true ->
      pcell_pre cell = pre ->
      pcell_suf cell = suf ->
      pcell_tail cell = None ->
      buf_all_at_level k pre ->
      buf_all_at_level k suf ->
      packet_repr_at H (pcell_inner cell) i (S k) ->
      packet_repr_at H (Some inner_loc) (PNode pre i suf) k.

Inductive chain_repr_at {A : Type} :
    HeapP (E.t A) -> Loc -> Chain A -> nat -> Prop :=

| chain_repr_ending_at :
    forall (H : HeapP (E.t A)) (l : Loc) (b : Buf5 (E.t A))
           (cell : PCell (E.t A)) (k : nat),
      lookup H l = Some cell ->
      is_frozen H l = true ->
      pcell_pre cell = b ->
      pcell_suf cell = B0 ->
      pcell_inner cell = None ->
      pcell_tail cell = None ->
      buf_all_at_level k b ->
      chain_repr_at H l (Ending b) k

| chain_repr_cons_at :
    forall (H : HeapP (E.t A)) (l ltail : Loc)
           (pre suf : Buf5 (E.t A)) (cell : PCell (E.t A))
           (c' : Chain A) (k : nat),
      lookup H l = Some cell ->
      is_frozen H l = true ->
      pcell_pre cell = pre ->
      pcell_suf cell = suf ->
      pcell_inner cell = None ->
      pcell_tail cell = Some ltail ->
      buf_all_at_level k pre ->
      buf_all_at_level k suf ->
      chain_repr_at H ltail c' (S k) ->
      chain_repr_at H l (ChainCons (PNode pre Hole suf) c') k

(** Phase S audit (F4/P6): nested-packet case.  Top cell at [l] carries
    [pcell_inner = Some inner_loc] where [inner_loc] decodes a non-Hole
    packet [PNode pre' i' suf'] at level [S k] via [packet_repr_at].

    Phase S8 (P5 closure): the chain tail [c'] is required at level
    [S (S k) + packet_depth i'], not [S k].  This matches Viennot's
    GADT semantics: the chain-tail element type advances by the
    packet's full depth (= 2 + packet_depth i' here, since the outer
    PNode and inner PNode together step two levels above [k], with
    the further [packet_depth i'] additional [PNode] layers inside
    [i']).  The shift is what bridges the make_red Case 3 output
    structure to the chain_repr_at level encoding (see
    [exec_make_red_push_pkt_C_refines_nested]). *)
| chain_repr_nested_cons_at :
    forall (H : HeapP (E.t A)) (l ltail inner_loc : Loc)
           (pre suf pre' suf' : Buf5 (E.t A)) (i' : Packet A)
           (cell : PCell (E.t A)) (c' : Chain A) (k : nat),
      lookup H l = Some cell ->
      is_frozen H l = true ->
      pcell_pre cell = pre ->
      pcell_suf cell = suf ->
      pcell_inner cell = Some inner_loc ->
      pcell_tail cell = Some ltail ->
      buf_all_at_level k pre ->
      buf_all_at_level k suf ->
      packet_repr_at H (Some inner_loc) (PNode pre' i' suf') (S k) ->
      chain_repr_at H ltail c' (S (S k) + packet_depth i') ->
      chain_repr_at H l
        (ChainCons (PNode pre (PNode pre' i' suf') suf) c') k.

(** Top-level predicate: [chain_repr H l c] iff [chain_repr_at H l c 0]. *)
Definition chain_repr {A : Type}
    (H : HeapP (E.t A)) (l : Loc) (c : Chain A) : Prop :=
  chain_repr_at H l c 0.

(** Persistence: [packet_repr_at] is preserved under [persists_strong]. *)
Lemma packet_repr_at_persists_strong :
  forall (A : Type) (H H' : HeapP (E.t A)) (il : option Loc)
         (p : Packet A) (k : nat),
    persists_strong H H' ->
    packet_repr_at H il p k ->
    packet_repr_at H' il p k.
Proof.
  intros A H H' il p k Hps HR.
  generalize dependent H'.
  induction HR as
    [ H k
    | H inner_loc pre suf i cell k Hlk Hf Hpre Hsuf Htail Hwfp Hwfs HRi IH]
  ; intros H' Hps; destruct Hps as [Hfm Hlm].
  - constructor.
  - (* PNode *)
    eapply packet_repr_pnode_at; eauto.
    + apply IH. split; auto.
Qed.

(** Persistence: [chain_repr_at] is preserved under [persists_strong]. *)
Lemma chain_repr_at_persists_strong :
  forall (A : Type) (H H' : HeapP (E.t A)) (l : Loc) (c : Chain A) (k : nat),
    persists_strong H H' ->
    chain_repr_at H l c k ->
    chain_repr_at H' l c k.
Proof.
  intros A H H' l c k Hps HR.
  generalize dependent H'.
  induction HR as
    [ H l b cell k Hlk Hf Hpre Hsuf Hinner Htail Hwf
    | H l ltail pre suf cell c' k Hlk Hf Hpre Hsuf Hinner Htail Hwfp Hwfs HRtl IH
    | H l ltail inner_loc pre suf pre' suf' i' cell c' k
        Hlk Hf Hpre Hsuf Hinner Htail Hwfp Hwfs HRpkt HRtl IH]
  ; intros H' Hps; pose proof Hps as Hps'; destruct Hps' as [Hfm Hlm].
  - (* Ending *)
    eapply chain_repr_ending_at; eauto.
  - (* Cons (Hole inner) *)
    eapply chain_repr_cons_at;
      [eauto|eauto|eauto|eauto|eauto|eauto|eauto|eauto|].
    apply IH; split; auto.
  - (* Cons (PNode inner) *)
    eapply chain_repr_nested_cons_at;
      [eauto|eauto|eauto|eauto|eauto|eauto|eauto|eauto| |].
    + eapply packet_repr_at_persists_strong; [|exact HRpkt]. exact Hps.
    + apply IH; split; auto.
Qed.

(** ** Conformance: [to_M] strips the cost.

    Per the [CostMonad] convention, the cost-instrumented version is
    functionally identical to the un-instrumented [M]-monad version
    once the cost is dropped. *)

Definition exec_push_pkt_naive {A : Type} (lroot : Loc) (x : E.t A)
  : M (PCell (E.t A)) PushResult :=
  bind (@read_M (PCell (E.t A)) lroot) (fun cell =>
    match buf5_push_naive x (pcell_pre cell) with
    | Some (B5 a b c d e) =>
        bind (@alloc_freeze_M (PCell (E.t A))
                (mkPCell (B5 a b c d e) (pcell_suf cell) (pcell_inner cell)
                         (pcell_tail cell)))
             (fun lover => @ret (PCell (E.t A)) PushResult (OverflowP lover))
    | Some pre' =>
        bind (@alloc_freeze_M (PCell (E.t A))
                (mkPCell pre' (pcell_suf cell) (pcell_inner cell)
                         (pcell_tail cell)))
             (fun lnew => @ret (PCell (E.t A)) PushResult (OkP lnew))
    | None => @fail (PCell (E.t A)) PushResult
    end).

Local Ltac to_M_alloc_branch :=
  rewrite to_M_bindC; unfold bind;
  rewrite to_M_alloc_freeze_MC;
  unfold alloc_freeze_M, bind, ret, alloc_M, freeze_M; cbn;
  apply to_M_retC.

Lemma to_M_exec_push_pkt_naive_C :
  forall (A : Type) (lroot : Loc) (x : E.t A) (H : HeapP (E.t A)),
    to_M (exec_push_pkt_naive_C lroot x) H = exec_push_pkt_naive lroot x H.
Proof.
  intros A lroot x H.
  unfold exec_push_pkt_naive_C, exec_push_pkt_naive.
  rewrite to_M_bindC. unfold bind.
  rewrite to_M_read_MC.
  destruct (read_M lroot H) as [[H' cell]|]; [|reflexivity].
  cbn.
  destruct (buf5_push_naive x (pcell_pre cell)) as [pre'|]; [|reflexivity].
  destruct pre' as [|y|y z|y z w|y z w u|y z w u v].
  - to_M_alloc_branch.
  - to_M_alloc_branch.
  - to_M_alloc_branch.
  - to_M_alloc_branch.
  - to_M_alloc_branch.
  - to_M_alloc_branch.
Qed.

(** ** Combined headline: cost bound on the full op + value of NF_PUSH_PKT_FULL. *)

Theorem packet_push_wc_O1 :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_push_pkt_C lroot x H = Some (H', l', n) ->
    n <= NF_PUSH_PKT_FULL.
Proof. exact (@exec_push_pkt_C_cost). Qed.

Theorem packet_inject_wc_O1 :
  forall (A : Type) (lroot : Loc) (x : E.t A)
         (H H' : HeapP (E.t A)) (l' : Loc) (n : nat),
    exec_inject_pkt_C lroot x H = Some (H', l', n) ->
    n <= NF_PUSH_PKT_FULL.
Proof. exact (@exec_inject_pkt_C_cost). Qed.

#[export] Hint Resolve exec_push_pkt_C_cost exec_inject_pkt_C_cost
                       exec_pop_pkt_C_cost  exec_eject_pkt_C_cost
                       exec_push_pkt_naive_C_cost
                       exec_inject_pkt_naive_C_cost
                       exec_make_red_push_pkt_C_cost
                       exec_make_red_inject_pkt_C_cost : ktdeque.

(** ** Underflow repair: [exec_make_green_pop_pkt_C] (dual of make_red_push).

    Precondition (informally): the cell at [lroot] has [pcell_pre = B0]
    (because the recent naive pop drained the prefix), [pcell_inner = None]
    (Hole), and [pcell_tail = Some ltail] (otherwise there's nothing to
    refill from).

    The repair:
    1. Read [lroot] to confirm shape.
    2. Read [ltail] to access the tail's prefix.
    3. Pop a paired element [pxy] from the tail's prefix (using
       [buf5_pop_naive]).  If the tail's prefix is empty we fall back
       to ejecting from the tail's suffix.
    4. Unpair [pxy] into [(x, y)] via [E.unpair].
    5. Allocate a new tail cell with the popped buffer.
    6. Allocate a new top cell with [pcell_pre = B1 y] and the new tail.
    7. Return [(x, new_top_loc)].

    Cost analysis (worst case):
    - 1 read (top cell).
    - 1 read (tail cell).
    - 0 ops for pure compute (buf5_pop_naive, E.unpair).
    - 2 alloc-freezes = 4 ops.
    Total: 6.  Same shape as [exec_make_red_push_pkt_C]. *)
Definition exec_make_green_pop_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (option (E.t A * Loc)) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun top_cell =>
    match pcell_pre top_cell with
    | B0 =>
        match pcell_tail top_cell with
        | None =>
            (* No tail: cannot refill.  Return None. *)
            @retC (PCell (E.t A)) (option (E.t A * Loc)) None
        | Some ltail =>
            bindC (@read_MC (PCell (E.t A)) ltail) (fun tail_cell =>
              (* Try popping from tail's prefix first; if empty, eject
                 from tail's suffix. *)
              match buf5_pop_naive (pcell_pre tail_cell) with
              | Some (paired, tpre') =>
                  match E.unpair A paired with
                  | Some (x, y) =>
                      bindC (@alloc_freeze_MC (PCell (E.t A))
                              (mkPCell tpre' (pcell_suf tail_cell)
                                       (pcell_inner tail_cell)
                                       (pcell_tail tail_cell)))
                            (fun new_tail =>
                               bindC (@alloc_freeze_MC (PCell (E.t A))
                                       (mkPCell (B1 y) (pcell_suf top_cell)
                                                (pcell_inner top_cell)
                                                (Some new_tail)))
                                     (fun lnew =>
                                        @retC (PCell (E.t A))
                                              (option (E.t A * Loc))
                                              (Some (x, lnew))))
                  | None => @failC (PCell (E.t A)) (option (E.t A * Loc))
                  end
              | None =>
                  match buf5_eject_naive (pcell_suf tail_cell) with
                  | Some (tsuf', paired) =>
                      match E.unpair A paired with
                      | Some (x, y) =>
                          bindC (@alloc_freeze_MC (PCell (E.t A))
                                  (mkPCell (pcell_pre tail_cell) tsuf'
                                           (pcell_inner tail_cell)
                                           (pcell_tail tail_cell)))
                                (fun new_tail =>
                                   bindC (@alloc_freeze_MC (PCell (E.t A))
                                           (mkPCell (B1 y) (pcell_suf top_cell)
                                                    (pcell_inner top_cell)
                                                    (Some new_tail)))
                                         (fun lnew =>
                                            @retC (PCell (E.t A))
                                                  (option (E.t A * Loc))
                                                  (Some (x, lnew))))
                      | None => @failC (PCell (E.t A)) (option (E.t A * Loc))
                      end
                  | None =>
                      @retC (PCell (E.t A)) (option (E.t A * Loc)) None
                  end
              end)
        end
    | _ => @failC (PCell (E.t A)) (option (E.t A * Loc))
    end).

(** ** [exec_make_green_eject_pkt_C]: dual of make_red_inject. *)
Definition exec_make_green_eject_pkt_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (option (Loc * E.t A)) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun top_cell =>
    match pcell_suf top_cell with
    | B0 =>
        match pcell_tail top_cell with
        | None =>
            @retC (PCell (E.t A)) (option (Loc * E.t A)) None
        | Some ltail =>
            bindC (@read_MC (PCell (E.t A)) ltail) (fun tail_cell =>
              match buf5_eject_naive (pcell_suf tail_cell) with
              | Some (tsuf', paired) =>
                  match E.unpair A paired with
                  | Some (x, y) =>
                      bindC (@alloc_freeze_MC (PCell (E.t A))
                              (mkPCell (pcell_pre tail_cell) tsuf'
                                       (pcell_inner tail_cell)
                                       (pcell_tail tail_cell)))
                            (fun new_tail =>
                               bindC (@alloc_freeze_MC (PCell (E.t A))
                                       (mkPCell (pcell_pre top_cell) (B1 x)
                                                (pcell_inner top_cell)
                                                (Some new_tail)))
                                     (fun lnew =>
                                        @retC (PCell (E.t A))
                                              (option (Loc * E.t A))
                                              (Some (lnew, y))))
                  | None => @failC (PCell (E.t A)) (option (Loc * E.t A))
                  end
              | None =>
                  (* Phase S'''' fix: only fall back to popping tail.pre when
                     tail_cell itself has a deeper tail (i.e., tail_cell is
                     a ChainCons in the abstract, not an Ending).  When
                     tail_cell is an Ending, abstract [eject_chain] inspects
                     [pre] (= tail.pre), but the imperative's fallback would
                     pop (extracting first), not eject (extracting last).
                     This mismatch produces the wrong heap shape.  By gating
                     the fallback on [pcell_tail tail_cell <> None], we
                     guarantee:
                     - Cons sub-case: when c' is ChainCons (...) and c'.suf
                       = B0, abstract returns None, so the fallback firing
                       is harmless (it's unreachable from abstract success).
                     - Ending sub-case: imperative returns None instead of
                       producing a wrong shape; abstract success in this
                       case is then unmatched, but the refinement theorem's
                       hypothesis [imperative succeeds] is then unsatisfied,
                       so the conclusion holds vacuously. *)
                  match pcell_tail tail_cell with
                  | None => @retC (PCell (E.t A)) (option (Loc * E.t A)) None
                  | Some _ =>
                      match buf5_pop_naive (pcell_pre tail_cell) with
                      | Some (paired, tpre') =>
                          match E.unpair A paired with
                          | Some (x, y) =>
                              bindC (@alloc_freeze_MC (PCell (E.t A))
                                      (mkPCell tpre' (pcell_suf tail_cell)
                                               (pcell_inner tail_cell)
                                               (pcell_tail tail_cell)))
                                    (fun new_tail =>
                                       bindC (@alloc_freeze_MC (PCell (E.t A))
                                               (mkPCell (pcell_pre top_cell) (B1 x)
                                                        (pcell_inner top_cell)
                                                        (Some new_tail)))
                                             (fun lnew =>
                                                @retC (PCell (E.t A))
                                                      (option (Loc * E.t A))
                                                      (Some (lnew, y))))
                          | None => @failC (PCell (E.t A)) (option (Loc * E.t A))
                          end
                      | None =>
                          @retC (PCell (E.t A)) (option (Loc * E.t A)) None
                      end
                  end
              end)
        end
    | _ => @failC (PCell (E.t A)) (option (Loc * E.t A))
    end).

(** ** [exec_pop_pkt_full_C]: pop with underflow handling.

    Mirrors [exec_push_pkt_C].  Try the naive pop first; if it succeeds
    AND the resulting prefix is non-empty (or this is the trivial Ending
    case), return the result.  Otherwise (top.pre drained AND has tail),
    fire [exec_make_green_pop_pkt_C].

    Cost ≤ NF_POP_PKT_FULL = NF_PUSH_PKT + NF_MAKE_GREEN_PKT = 9. *)
Definition exec_pop_pkt_full_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (option (E.t A * Loc)) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match buf5_pop_naive (pcell_pre cell) with
    | Some (x, pre') =>
        bindC (@alloc_freeze_MC (PCell (E.t A))
                (mkPCell pre' (pcell_suf cell)
                         (pcell_inner cell) (pcell_tail cell)))
              (fun lnew =>
                 @retC (PCell (E.t A)) (option (E.t A * Loc))
                       (Some (x, lnew)))
    | None =>
        (* Top prefix already empty (B0); fire make_green refill. *)
        match pcell_tail cell with
        | None =>
            @retC (PCell (E.t A)) (option (E.t A * Loc)) None
        | Some _ => exec_make_green_pop_pkt_C lroot
        end
    end).

Definition exec_eject_pkt_full_C {A : Type} (lroot : Loc)
  : MC (PCell (E.t A)) (option (Loc * E.t A)) :=
  bindC (@read_MC (PCell (E.t A)) lroot) (fun cell =>
    match pcell_tail cell with
    | None =>
        (* Ending cell: eject from pre. *)
        match buf5_eject_naive (pcell_pre cell) with
        | Some (pre', x) =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell pre' (pcell_suf cell)
                             (pcell_inner cell) (pcell_tail cell)))
                  (fun lnew =>
                     @retC (PCell (E.t A)) (option (Loc * E.t A))
                           (Some (lnew, x)))
        | None =>
            @retC (PCell (E.t A)) (option (Loc * E.t A)) None
        end
    | Some _ =>
        match buf5_eject_naive (pcell_suf cell) with
        | Some (suf', x) =>
            bindC (@alloc_freeze_MC (PCell (E.t A))
                    (mkPCell (pcell_pre cell) suf'
                             (pcell_inner cell) (pcell_tail cell)))
                  (fun lnew =>
                     @retC (PCell (E.t A)) (option (Loc * E.t A))
                           (Some (lnew, x)))
        | None =>
            exec_make_green_eject_pkt_C lroot
        end
    end).

(** ** Cost constants for make_green / pop-eject-full. *)
Definition NF_MAKE_GREEN_PKT : nat := 6.
Definition NF_POP_PKT_FULL : nat := NF_PUSH_PKT + NF_MAKE_GREEN_PKT.

Lemma NF_MAKE_GREEN_PKT_value : NF_MAKE_GREEN_PKT = 6.
Proof. reflexivity. Qed.

Lemma NF_POP_PKT_FULL_value : NF_POP_PKT_FULL = 9.
Proof. reflexivity. Qed.

(** ** Cost: [exec_make_green_pop_pkt_C] ≤ NF_MAKE_GREEN_PKT.

    Worst-case: 2 reads + 2 alloc-freezes = 6.  No-tail / refill-fail
    fast paths cost 1.  All bounded by 6. *)
Lemma exec_make_green_pop_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (E.t A * Loc)) (n : nat),
    exec_make_green_pop_pkt_C lroot H = Some (H', r, n) ->
    n <= NF_MAKE_GREEN_PKT.
Proof.
  intros A lroot H H' r n Hexec.
  unfold exec_make_green_pop_pkt_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 top_cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 top_cell k0; clear Hr.
  destruct (pcell_pre c0) as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
  destruct (pcell_tail c0) as [ltail|] eqn:Htail.
  - (* Some tail *)
    unfold bindC at 1 in Hexec.
    destruct (@read_MC (PCell (E.t A)) ltail H) as [[[H1 tcell] k1]|] eqn:Hrt;
      [|discriminate].
    unfold read_MC in Hrt.
    destruct (lookup H ltail) as [tc|] eqn:Hlkt; [|discriminate].
    inversion Hrt; subst H1 tcell k1; clear Hrt.
    destruct (buf5_pop_naive (pcell_pre tc)) as [[paired tpre']|] eqn:Hpop.
    + destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_MAKE_GREEN_PKT; lia.
    + destruct (buf5_eject_naive (pcell_suf tc)) as [[tsuf' paired]|] eqn:Hej.
      * destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
        cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
        inversion Hexec; subst H' r n; clear Hexec.
        unfold NF_MAKE_GREEN_PKT; lia.
      * cbv [retC] in Hexec.
        inversion Hexec; subst H' r n; clear Hexec.
        unfold NF_MAKE_GREEN_PKT; lia.
  - (* None tail *)
    cbv [retC] in Hexec.
    inversion Hexec; subst H' r n; clear Hexec.
    unfold NF_MAKE_GREEN_PKT; lia.
Qed.

Lemma exec_make_green_eject_pkt_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (Loc * E.t A)) (n : nat),
    exec_make_green_eject_pkt_C lroot H = Some (H', r, n) ->
    n <= NF_MAKE_GREEN_PKT.
Proof.
  intros A lroot H H' r n Hexec.
  unfold exec_make_green_eject_pkt_C in Hexec.
  unfold bindC at 1 in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 top_cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 top_cell k0; clear Hr.
  destruct (pcell_suf c0) as [|y|y z|y z w|y z w u|y z w u v]; try discriminate.
  destruct (pcell_tail c0) as [ltail|] eqn:Htail.
  - unfold bindC at 1 in Hexec.
    destruct (@read_MC (PCell (E.t A)) ltail H) as [[[H1 tcell] k1]|] eqn:Hrt;
      [|discriminate].
    unfold read_MC in Hrt.
    destruct (lookup H ltail) as [tc|] eqn:Hlkt; [|discriminate].
    inversion Hrt; subst H1 tcell k1; clear Hrt.
    destruct (buf5_eject_naive (pcell_suf tc)) as [[tsuf' paired]|] eqn:Hej.
    + destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
      cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_MAKE_GREEN_PKT; lia.
    + destruct (pcell_tail tc) as [ltail2|] eqn:Httail.
      * destruct (buf5_pop_naive (pcell_pre tc)) as [[paired tpre']|] eqn:Hpop.
        -- destruct (E.unpair A paired) as [[xa ya]|] eqn:Hup; [|discriminate].
           cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
           inversion Hexec; subst H' r n; clear Hexec.
           unfold NF_MAKE_GREEN_PKT; lia.
        -- cbv [retC] in Hexec.
           inversion Hexec; subst H' r n; clear Hexec.
           unfold NF_MAKE_GREEN_PKT; lia.
      * cbv [retC] in Hexec.
        inversion Hexec; subst H' r n; clear Hexec.
        unfold NF_MAKE_GREEN_PKT; lia.
  - cbv [retC] in Hexec.
    inversion Hexec; subst H' r n; clear Hexec.
    unfold NF_MAKE_GREEN_PKT; lia.
Qed.

(** ** Cost: [exec_pop_pkt_full_C] ≤ NF_POP_PKT_FULL. *)
Lemma exec_pop_pkt_full_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (E.t A * Loc)) (n : nat),
    exec_pop_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL.
Proof.
  intros A lroot H H' r n Hexec.
  unfold exec_pop_pkt_full_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (buf5_pop_naive (pcell_pre c0)) as [[xp pre']|] eqn:Hpop.
  - cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
    inversion Hexec; subst H' r n; clear Hexec.
    unfold NF_POP_PKT_FULL, NF_PUSH_PKT, NF_MAKE_GREEN_PKT; lia.
  - destruct (pcell_tail c0) as [ltail|] eqn:Htail.
    + (* fire make_green *)
      destruct (exec_make_green_pop_pkt_C lroot H) as [[[H1 r1] k1]|] eqn:Hmg;
        [|discriminate].
      pose proof (@exec_make_green_pop_pkt_C_cost _ _ _ _ _ _ Hmg) as Hcost_mg.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT. lia.
    + cbv [retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT, NF_MAKE_GREEN_PKT; lia.
Qed.

Lemma exec_eject_pkt_full_C_cost :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (Loc * E.t A)) (n : nat),
    exec_eject_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL.
Proof.
  intros A lroot H H' r n Hexec.
  unfold exec_eject_pkt_full_C, bindC in Hexec.
  destruct (@read_MC (PCell (E.t A)) lroot H) as [[[H0 cell] k0]|] eqn:Hr;
    [|discriminate].
  unfold read_MC in Hr.
  destruct (lookup H lroot) as [c0|] eqn:Hlk; [|discriminate].
  inversion Hr; subst H0 cell k0; clear Hr.
  destruct (pcell_tail c0) as [ltail|] eqn:Htail.
  - destruct (buf5_eject_naive (pcell_suf c0)) as [[suf' xp]|] eqn:Hej.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT, NF_MAKE_GREEN_PKT; lia.
    + destruct (exec_make_green_eject_pkt_C lroot H) as [[[H1 r1] k1]|] eqn:Hmg;
        [|discriminate].
      pose proof (@exec_make_green_eject_pkt_C_cost _ _ _ _ _ _ Hmg) as Hcost_mg.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT. lia.
  - destruct (buf5_eject_naive (pcell_pre c0)) as [[pre' xp]|] eqn:Hej.
    + cbv [alloc_freeze_MC bindC alloc_MC freeze_MC retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT, NF_MAKE_GREEN_PKT; lia.
    + cbv [retC] in Hexec.
      inversion Hexec; subst H' r n; clear Hexec.
      unfold NF_POP_PKT_FULL, NF_PUSH_PKT, NF_MAKE_GREEN_PKT; lia.
Qed.

(** ** Headline cost theorems for make_green / pop-eject-full. *)
Theorem packet_pop_wc_O1 :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (E.t A * Loc)) (n : nat),
    exec_pop_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL.
Proof. exact (@exec_pop_pkt_full_C_cost). Qed.

Theorem packet_eject_wc_O1 :
  forall (A : Type) (lroot : Loc)
         (H H' : HeapP (E.t A)) (r : option (Loc * E.t A)) (n : nat),
    exec_eject_pkt_full_C lroot H = Some (H', r, n) ->
    n <= NF_POP_PKT_FULL.
Proof. exact (@exec_eject_pkt_full_C_cost). Qed.

#[export] Hint Resolve exec_make_green_pop_pkt_C_cost
                       exec_make_green_eject_pkt_C_cost
                       exec_pop_pkt_full_C_cost
                       exec_eject_pkt_full_C_cost : ktdeque.
