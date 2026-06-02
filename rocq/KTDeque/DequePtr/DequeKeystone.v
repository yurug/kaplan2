(** * KTDeque.DequePtr.DequeKeystone — Gate-B deque keystone (Phase 4a).

    The unconditional worst-case-O(1) statement for the non-catenable deque,
    built TOP-DOWN per kb/spec/deque-reachable-invariant.md and the rebuild
    plan's methodology rule 6.

    The invariant is
      [I_kt c := regular_kt_top c /\ colors_consistent c /\ well_leveled c].

    The per-operation obligation lemmas ([*_total], [*_preserves_I_kt]) are
    [Admitted] SCAFFOLDING on the [rebuild] branch.  The headline theorems
    [deque_wc_o1_*] are proven FROM those obligations + the already-closed cost
    lemmas ([*_green_calls_le_1]), which validates the architecture end to end.

    The remaining admits ARE the to-do list — see [Print Assumptions] at the
    bottom.  CLOSURE of Phase 4a = zero admits + clean Print Assumptions
    (rebuild plan rules 5b/5c).  Admits never reach [main].

    Discharge order (hardest last):
      [ ] empty_I_kt                  -- proven below (not admitted)
      [ ] push_kt4_total / preserves_I_kt
      [ ] inject_kt4_total / preserves_I_kt
      [ ] pop_kt4_total / preserves_I_kt
      [ ] eject_kt4_total / preserves_I_kt
    Each [*_total]/[*_preserves_I_kt] decomposes via the crux lemma
    (green_of_red_k total + I_kt-preserving on regular, colour-consistent,
    well-levelled red chains) into the buffer-op lemmas. *)

From KTDeque.Common Require Import Prelude Color Buf5 Element.
From KTDeque.DequePtr Require Import Model OpsKT OpsKTRegular PublicTheorems.

Module E := OpsKT.E.

(* ========================================================================== *)
(* The invariant I_kt.                                                         *)
(* ========================================================================== *)

(** Colour-consistency inside a packet's yellow run: every nested level is
    not-red (the yellow run sits above the green/red boundary). *)
Fixpoint cc_yellow_run {A : Type} (p : Packet A) : Prop :=
  match p with
  | Hole => True
  | PNode pre i suf =>
      buf5_is_not_red_shape pre /\ buf5_is_not_red_shape suf /\ cc_yellow_run i
  end.

(** Colour-tag consistency at every chain link: a Green link has green-shaped
    (B2/B3) buffers, a Yellow link has not-red (B1..B4) buffers; the inner
    yellow run is not-red throughout.  (The Red-link buffer condition is left
    permissive here and will be tightened while discharging the obligations.) *)
Fixpoint colors_consistent {A : Type} (c : KChain A) : Prop :=
  match c with
  | KEnding _ => True
  | KCons Green (PNode pre i suf) tail =>
      buf5_is_green_shape pre /\ buf5_is_green_shape suf
      /\ cc_yellow_run i /\ colors_consistent tail
  | KCons Yellow (PNode pre i suf) tail =>
      buf5_is_not_red_shape pre /\ buf5_is_not_red_shape suf
      /\ cc_yellow_run i /\ colors_consistent tail
  | KCons Red (PNode _ i suf) tail =>
      cc_yellow_run i /\ colors_consistent tail
  | KCons _ Hole _ => False
  end.

(** Level-consistency: buffers at chain-depth [k] hold level-[k] elements.
    Lifts Model.v's [buf_all_at_level]/[packet_levels] to [KChain].  Over the
    production instance [E = ElementTree], positive-level elements are
    unpairable (a theorem, not an axiom), which is what the repair's underflow
    arms need. *)
Fixpoint well_leveled_at {A : Type} (k : nat) (c : KChain A) : Prop :=
  match c with
  | KEnding b => buf_all_at_level k b
  | KCons _ p tail => packet_levels k p /\ well_leveled_at (S k) tail
  end.

Definition well_leveled {A : Type} (c : KChain A) : Prop := well_leveled_at 0 c.

Definition I_kt {A : Type} (c : KChain A) : Prop :=
  regular_kt_top c /\ colors_consistent c /\ well_leveled c.

(** The empty deque satisfies the invariant. *)
Lemma empty_I_kt : forall A, I_kt (@empty_kchain A).
Proof.
  intros A. unfold I_kt, regular_kt_top, well_leveled, empty_kchain.
  split.
  - split.
    + cbn. discriminate.
    + apply reg_kt_ending.
  - split.
    + cbn. exact I.
    + cbn. exact I.
Qed.

(* ========================================================================== *)
(* Per-operation obligations (Admitted scaffolding — the to-do list).          *)
(* ========================================================================== *)

Lemma push_kt4_total :
  forall A (x : E.t A) (c : KChain A),
    I_kt c -> exists c', push_kt4 x c = PushOk c'.
Proof. Admitted.

Lemma push_kt4_preserves_I_kt :
  forall A (x : E.t A) (c c' : KChain A),
    I_kt c -> push_kt4 x c = PushOk c' -> I_kt c'.
Proof. Admitted.

Lemma inject_kt4_total :
  forall A (c : KChain A) (x : E.t A),
    I_kt c -> exists c', inject_kt4 c x = PushOk c'.
Proof. Admitted.

Lemma inject_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> inject_kt4 c x = PushOk c' -> I_kt c'.
Proof. Admitted.

Lemma pop_kt4_total :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c -> exists x c', pop_kt4 c = PopOk x c'.
Proof. Admitted.

Lemma pop_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> pop_kt4 c = PopOk x c' -> I_kt c'.
Proof. Admitted.

Lemma eject_kt4_total :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c -> exists x c', eject_kt4 c = PopOk x c'.
Proof. Admitted.

Lemma eject_kt4_preserves_I_kt :
  forall A (c c' : KChain A) (x : E.t A),
    I_kt c -> eject_kt4 c = PopOk x c' -> I_kt c'.
Proof. Admitted.

(* ========================================================================== *)
(* The keystone: unconditional WC O(1) per operation on I_kt states.           *)
(* Cost clause reuses the already-closed [*_green_calls_le_1].                  *)
(* ========================================================================== *)

Theorem deque_wc_o1_push :
  forall A (x : E.t A) (c : KChain A),
    I_kt c ->
    exists c',
      push_kt4 x c = PushOk c' /\ I_kt c' /\ push_kt4_green_calls x c <= 1.
Proof.
  intros A x c HI.
  destruct (@push_kt4_total A x c HI) as [c' Hc'].
  exists c'. split; [exact Hc'|]. split.
  - exact (@push_kt4_preserves_I_kt A x c c' HI Hc').
  - apply push_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_inject :
  forall A (c : KChain A) (x : E.t A),
    I_kt c ->
    exists c',
      inject_kt4 c x = PushOk c' /\ I_kt c' /\ inject_kt4_green_calls c x <= 1.
Proof.
  intros A c x HI.
  destruct (@inject_kt4_total A c x HI) as [c' Hc'].
  exists c'. split; [exact Hc'|]. split.
  - exact (@inject_kt4_preserves_I_kt A c c' x HI Hc').
  - apply inject_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_pop :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c ->
    exists x c',
      pop_kt4 c = PopOk x c' /\ I_kt c' /\ pop_kt4_green_calls c <= 1.
Proof.
  intros A c HI Hne.
  destruct (@pop_kt4_total A c HI Hne) as [x [c' Hc']].
  exists x, c'. split; [exact Hc'|]. split.
  - exact (@pop_kt4_preserves_I_kt A c c' x HI Hc').
  - apply pop_kt4_green_calls_le_1.
Qed.

Theorem deque_wc_o1_eject :
  forall A (c : KChain A),
    I_kt c -> kt4_nonempty_state c ->
    exists x c',
      eject_kt4 c = PopOk x c' /\ I_kt c' /\ eject_kt4_green_calls c <= 1.
Proof.
  intros A c HI Hne.
  destruct (@eject_kt4_total A c HI Hne) as [x [c' Hc']].
  exists x, c'. split; [exact Hc'|]. split.
  - exact (@eject_kt4_preserves_I_kt A c c' x HI Hc').
  - apply eject_kt4_green_calls_le_1.
Qed.

(* The admit list IS the to-do list.  Closure = these report "Closed under the
   global context". *)
Print Assumptions deque_wc_o1_push.
Print Assumptions deque_wc_o1_inject.
Print Assumptions deque_wc_o1_pop.
Print Assumptions deque_wc_o1_eject.
