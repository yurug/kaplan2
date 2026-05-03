(** * Module: KTDeque.Common.CostMonad -- the cost-instrumented heap monad.

    A parallel monad to [M] that tracks the number of primitive heap
    operations (read, alloc, freeze, write) performed by a computation.
    Used to prove worst-case O(1) bounds on the imperative ops.

    The monad: [MC Cell X := Heap Cell -> option (Heap Cell * X * nat)].
    The third component is the *primitive op count*: each [read_MC],
    [alloc_MC], [freeze_MC], [write_MC] adds 1; [retC]/[failC] add 0;
    [bindC] adds the costs of its components.

    This is purely an instrumentation layer.  [to_M] strips the count and
    recovers the standard [M Cell X] computation; the conformance lemma
    [to_M_*] shows each instrumented op is functionally identical to its
    [M] counterpart.

    Cross-references:
    - kb/properties/footprint.md (NF1, NF2 — worst-case bounds).
    - kb/architecture/decisions/adr-0010-imperative-dsl.md.
*)

From KTDeque.Common Require Import Prelude FinMapHeap HeapExt Monad.

(** ** The cost-instrumented monad. *)
Definition MC (Cell : Type) (X : Type) : Type :=
  Heap Cell -> option (Heap Cell * X * nat).

Definition retC {Cell X} (x : X) : MC Cell X :=
  fun H => Some (H, x, 0).

Definition failC {Cell X} : MC Cell X :=
  fun _ => None.

Definition bindC {Cell X Y} (m : MC Cell X) (f : X -> MC Cell Y) : MC Cell Y :=
  fun H =>
    match m H with
    | None => None
    | Some (H', x, k1) =>
        match f x H' with
        | None => None
        | Some (H'', y, k2) => Some (H'', y, k1 + k2)
        end
    end.

(** ** Primitive ops, each costing 1 step. *)

Definition read_MC {Cell : Type} (l : Loc) : MC Cell Cell :=
  fun H =>
    match lookup H l with
    | None => None
    | Some c => Some (H, c, 1)
    end.

Definition alloc_MC {Cell : Type} (c : Cell) : MC Cell Loc :=
  fun H => Some (snd (alloc c H), fst (alloc c H), 1).

Definition freeze_MC {Cell : Type} (l : Loc) : MC Cell unit :=
  fun H => Some (freeze l H, tt, 1).

Definition write_MC {Cell : Type} (l : Loc) (c : Cell) : MC Cell unit :=
  fun H =>
    match write l c H with
    | None => None
    | Some H' => Some (H', tt, 1)
    end.

(** [alloc_freeze_MC]: allocate then freeze.  Cost: 2 (one alloc + one
    freeze).  By [bindC], the cost is automatically 1+1+0 = 2. *)
Definition alloc_freeze_MC {Cell : Type} (c : Cell) : MC Cell Loc :=
  bindC (@alloc_MC Cell c) (fun l =>
    bindC (@freeze_MC Cell l) (fun _ =>
      @retC Cell Loc l)).

(** ** Conformance to [M]: strip the cost. *)

Definition to_M {Cell X} (m : MC Cell X) : M Cell X :=
  fun H =>
    match m H with
    | None => None
    | Some (H', x, _) => Some (H', x)
    end.

(** Conformance lemmas: each [_MC] op corresponds to its [_M] counterpart
    after stripping the cost. *)

Lemma to_M_retC :
  forall (Cell X : Type) (x : X) (H : Heap Cell),
    to_M (retC x) H = ret x H.
Proof. intros. unfold to_M, retC, ret. reflexivity. Qed.

Lemma to_M_bindC :
  forall (Cell X Y : Type) (m : MC Cell X) (f : X -> MC Cell Y) (H : Heap Cell),
    to_M (bindC m f) H = bind (to_M m) (fun x => to_M (f x)) H.
Proof.
  intros Cell X Y m f H. unfold to_M, bindC, bind.
  destruct (m H) as [[[H' x] k1]|]; [|reflexivity].
  destruct (f x H') as [[[H'' y] k2]|]; reflexivity.
Qed.

Lemma to_M_read_MC :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    to_M (read_MC l) H = read_M l H.
Proof.
  intros. unfold to_M, read_MC, read_M.
  destruct (lookup H l); reflexivity.
Qed.

Lemma to_M_alloc_MC :
  forall (Cell : Type) (c : Cell) (H : Heap Cell),
    to_M (alloc_MC c) H = alloc_M c H.
Proof. intros. unfold to_M, alloc_MC, alloc_M. reflexivity. Qed.

Lemma to_M_freeze_MC :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    to_M (freeze_MC l) H = freeze_M l H.
Proof. intros. unfold to_M, freeze_MC, freeze_M. reflexivity. Qed.

Lemma to_M_alloc_freeze_MC :
  forall (Cell : Type) (c : Cell) (H : Heap Cell),
    to_M (alloc_freeze_MC c) H = alloc_freeze_M c H.
Proof.
  intros Cell c H.
  unfold alloc_freeze_MC, alloc_freeze_M.
  rewrite to_M_bindC. unfold bind.
  rewrite to_M_alloc_MC. destruct (alloc_M c H) as [[H' l]|]; [|reflexivity].
  rewrite to_M_bindC. unfold bind.
  rewrite to_M_freeze_MC. destruct (freeze_M l H') as [[H'' u]|]; [|reflexivity].
  rewrite to_M_retC. reflexivity.
Qed.

(** ** Cost extraction.

    [cost_of m H = Some k] means [m] succeeds on [H] with primitive count [k]. *)
Definition cost_of {Cell X} (m : MC Cell X) (H : Heap Cell) : option nat :=
  match m H with
  | None => None
  | Some (_, _, k) => Some k
  end.

(** Cost of primitives. *)
Lemma cost_retC :
  forall Cell X (x : X) (H : Heap Cell),
    @cost_of Cell X (retC x) H = Some 0.
Proof. reflexivity. Qed.

Lemma cost_alloc_MC :
  forall Cell (c : Cell) (H : Heap Cell),
    @cost_of Cell Loc (alloc_MC c) H = Some 1.
Proof. reflexivity. Qed.

Lemma cost_freeze_MC :
  forall Cell (l : Loc) (H : Heap Cell),
    @cost_of Cell unit (freeze_MC l) H = Some 1.
Proof. reflexivity. Qed.

Lemma cost_alloc_freeze_MC :
  forall Cell (c : Cell) (H : Heap Cell),
    @cost_of Cell Loc (alloc_freeze_MC c) H = Some 2.
Proof. reflexivity. Qed.

(** Cost composition for [bindC]: if both sides succeed with costs [k1]
    and [k2], the composed cost is [k1 + k2]. *)
Lemma cost_bindC :
  forall Cell X Y (m : MC Cell X) (f : X -> MC Cell Y) (H H' : Heap Cell)
         (x : X) (k1 k2 : nat),
    m H = Some (H', x, k1) ->
    cost_of (f x) H' = Some k2 ->
    cost_of (bindC m f) H = Some (k1 + k2).
Proof.
  intros Cell X Y m f H H' x k1 k2 Hm Hf.
  unfold cost_of, bindC.
  rewrite Hm.
  unfold cost_of in Hf.
  destruct (f x H') as [[[H'' y] kk2]|] eqn:Hfeq;
    [|discriminate].
  inversion Hf; subst kk2.
  reflexivity.
Qed.
