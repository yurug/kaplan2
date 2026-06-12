(** * KTDeque.DequePtr.SizedChain — size-fused kt4 chains.

    Verified DATA-CONSTRUCTOR FUSION for the production buffer seam:
    the §6 catenable layer needs an O(1) element count next to each
    kt4 chain ([bsize] drives the colour tests).  Carrying it as a
    record {chain; size} costs one extra allocation per operation and
    one extra indirection per size read.  [SChain] fuses the count
    into the top chain constructor instead:

        SEnding n b   ~   {KEnding b;   size = n}
        SCons n col p t ~ {KCons col p t; size = n}

    and the four ops are mirrored natively against it, threading n±1
    — so a buffer push allocates the (sized) top cell it would have
    allocated anyway, and nothing else.  The push/inject mirrors also
    drop the [PushOk] result wrapper (failure returns the input chain,
    a sentinel the §6 keystone proves unreachable on regular inputs;
    pop/eject keep the flat [SPopOk] because the element must come
    back too).

    Each mirror carries a [_spec] lemma reducing it to the proven kt4
    op through the erasure [s_erase] / re-tagging [s_of], so the
    deque keystone (sequence semantics + WC O(1) totality on regular
    chains) describes these ops verbatim. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color.
From KTDeque.DequePtr Require Import Model OpsKT.

Set Implicit Arguments.

Module E := Model.E.

Inductive SChain (A : Type) : Type :=
| SEnding : nat -> Buf5 (E.t A) -> SChain A
| SCons   : nat -> color -> Packet A -> KChain A -> SChain A.

Arguments SEnding {A} _ _.
Arguments SCons   {A} _ _ _ _.

Definition s_empty {A : Type} : SChain A := SEnding 0 B0.

Definition s_size {A : Type} (c : SChain A) : nat :=
  match c with
  | SEnding n _ => n
  | SCons n _ _ _ => n
  end.

Definition s_erase {A : Type} (c : SChain A) : KChain A :=
  match c with
  | SEnding _ b => KEnding b
  | SCons _ col p t => KCons col p t
  end.

Definition s_of {A : Type} (n : nat) (c : KChain A) : SChain A :=
  match c with
  | KEnding b => SEnding n b
  | KCons col p t => SCons n col p t
  end.

Definition s_to_list {A : Type} (c : SChain A) : list A :=
  kchain_to_list (s_erase c).

Lemma s_of_erase : forall A n (c : KChain A),
    s_erase (s_of n c) = c.
Proof. intros A n [b | col p t]; reflexivity. Qed.

(* ========================================================================== *)
(* push / inject.                                                              *)
(* ========================================================================== *)

(** [yellow_wrap_pr] with the result wrapper fused away; [fb] is the
    fail sentinel (the op's input). *)
Definition yellow_wrap_s {A : Type} (fb : SChain A) (n' : nat)
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (t : KChain A) : SChain A :=
  match t with
  | KCons Red _ _ =>
      match green_of_red_k t with
      | Some t' => SCons n' Yellow (PNode pre i suf) t'
      | None    => fb
      end
  | _ => SCons n' Yellow (PNode pre i suf) t
  end.

Definition push_s {A : Type} (x : E.t A) (c : SChain A) : SChain A :=
  match c with
  | SEnding n b =>
      match b with
      | B0           => SEnding (S n) (B1 x)
      | B1 a         => SEnding (S n) (B2 x a)
      | B2 a b1      => SEnding (S n) (B3 x a b1)
      | B3 a b1 c1   => SEnding (S n) (B4 x a b1 c1)
      | B4 a b1 c1 d => SEnding (S n) (B5 x a b1 c1 d)
      | B5 a b1 c1 d e =>
          SCons (S n) Green (PNode (B3 x a b1) Hole (B3 c1 d e)) (KEnding B0)
      end
  | SCons n col p t =>
      match col, p with
      | Green, PNode pre i suf =>
          match pre with
          | B2 a b1    => yellow_wrap_s c (S n) (B3 x a b1) i suf t
          | B3 a b1 c1 => yellow_wrap_s c (S n) (B4 x a b1 c1) i suf t
          | _          => c
          end
      | Yellow, PNode pre i suf =>
          match pre with
          | B1 a         => SCons (S n) Yellow (PNode (B2 x a) i suf) t
          | B2 a b1      => SCons (S n) Yellow (PNode (B3 x a b1) i suf) t
          | B3 a b1 c1   => SCons (S n) Yellow (PNode (B4 x a b1 c1) i suf) t
          | B4 a b1 c1 d =>
              match green_of_red_k
                      (KCons Red (PNode (B5 x a b1 c1 d) i suf) t) with
              | Some d' => s_of (S n) d'
              | None    => c
              end
          | _ => c
          end
      | _, _ => c
      end
  end.

Lemma push_s_spec : forall A (x : E.t A) (c : SChain A),
    push_s x c = match push_kt4 x (s_erase c) with
                 | PushOk d => s_of (S (s_size c)) d
                 | PushFail => c
                 end.
Proof.
  intros A x c.
  destruct c as [n b | n col p t].
  - destruct b; reflexivity.
  - destruct col.
    + (* Green *)
      destruct p as [| pre i suf]; [reflexivity|].
      destruct pre; try reflexivity;
        cbn [push_s push_kt4 s_erase];
        unfold yellow_wrap_s, yellow_wrap_pr;
        (destruct t as [b' | col' p' t']; [reflexivity|];
         destruct col'; try reflexivity;
         destruct (green_of_red_k (KCons Red p' t')); reflexivity).
    + (* Yellow *)
      destruct p as [| pre i suf]; [reflexivity|].
      destruct pre; try reflexivity.
      cbn [push_s push_kt4 s_erase].
      destruct (green_of_red_k (KCons Red (PNode (B5 x _ _ _ _) i suf) t));
        reflexivity.
    + (* Red *)
      destruct p; reflexivity.
Qed.

Definition inject_s {A : Type} (c : SChain A) (x : E.t A) : SChain A :=
  match c with
  | SEnding n b =>
      match b with
      | B0           => SEnding (S n) (B1 x)
      | B1 a         => SEnding (S n) (B2 a x)
      | B2 a b1      => SEnding (S n) (B3 a b1 x)
      | B3 a b1 c1   => SEnding (S n) (B4 a b1 c1 x)
      | B4 a b1 c1 d => SEnding (S n) (B5 a b1 c1 d x)
      | B5 a b1 c1 d e =>
          SCons (S n) Green (PNode (B3 a b1 c1) Hole (B3 d e x)) (KEnding B0)
      end
  | SCons n col p t =>
      match col, p with
      | Green, PNode pre i suf =>
          match suf with
          | B2 a b1    => yellow_wrap_s c (S n) pre i (B3 a b1 x) t
          | B3 a b1 c1 => yellow_wrap_s c (S n) pre i (B4 a b1 c1 x) t
          | _          => c
          end
      | Yellow, PNode pre i suf =>
          match suf with
          | B1 a         => SCons (S n) Yellow (PNode pre i (B2 a x)) t
          | B2 a b1      => SCons (S n) Yellow (PNode pre i (B3 a b1 x)) t
          | B3 a b1 c1   => SCons (S n) Yellow (PNode pre i (B4 a b1 c1 x)) t
          | B4 a b1 c1 d =>
              match green_of_red_k
                      (KCons Red (PNode pre i (B5 a b1 c1 d x)) t) with
              | Some d' => s_of (S n) d'
              | None    => c
              end
          | _ => c
          end
      | _, _ => c
      end
  end.

Lemma inject_s_spec : forall A (c : SChain A) (x : E.t A),
    inject_s c x = match inject_kt4 (s_erase c) x with
                   | PushOk d => s_of (S (s_size c)) d
                   | PushFail => c
                   end.
Proof.
  intros A c x.
  destruct c as [n b | n col p t].
  - destruct b; reflexivity.
  - destruct col.
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct suf; try reflexivity;
        cbn [inject_s inject_kt4 s_erase];
        unfold yellow_wrap_s, yellow_wrap_pr;
        (destruct t as [b' | col' p' t']; [reflexivity|];
         destruct col'; try reflexivity;
         destruct (green_of_red_k (KCons Red p' t')); reflexivity).
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct suf; try reflexivity.
      cbn [inject_s inject_kt4 s_erase].
      destruct (green_of_red_k (KCons Red (PNode pre i (B5 _ _ _ _ x)) t));
        reflexivity.
    + destruct p; reflexivity.
Qed.

(* ========================================================================== *)
(* pop / eject.                                                                *)
(* ========================================================================== *)

Inductive spop_result (A : Type) : Type :=
| SPopFail : spop_result A
| SPopOk   : E.t A -> SChain A -> spop_result A.
Arguments SPopFail {A}.
Arguments SPopOk   {A} _ _.

Definition pop_s {A : Type} (c : SChain A) : spop_result A :=
  match c with
  | SEnding n b =>
      match b with
      | B0           => SPopFail
      | B1 a         => SPopOk a (SEnding (Nat.pred n) B0)
      | B2 a b1      => SPopOk a (SEnding (Nat.pred n) (B1 b1))
      | B3 a b1 c1   => SPopOk a (SEnding (Nat.pred n) (B2 b1 c1))
      | B4 a b1 c1 d => SPopOk a (SEnding (Nat.pred n) (B3 b1 c1 d))
      | B5 a b1 c1 d e => SPopOk a (SEnding (Nat.pred n) (B4 b1 c1 d e))
      end
  | SCons n col p t =>
      match col, p with
      | Green, PNode pre i suf =>
          match pre with
          | B2 a b1 =>
              match t with
              | KCons Red _ _ =>
                  match green_of_red_k t with
                  | Some t' =>
                      SPopOk a
                        (SCons (Nat.pred n) Yellow (PNode (B1 b1) i suf) t')
                  | None => SPopFail
                  end
              | _ =>
                  SPopOk a
                    (SCons (Nat.pred n) Yellow (PNode (B1 b1) i suf) t)
              end
          | B3 a b1 c1 =>
              match t with
              | KCons Red _ _ =>
                  match green_of_red_k t with
                  | Some t' =>
                      SPopOk a
                        (SCons (Nat.pred n) Yellow (PNode (B2 b1 c1) i suf) t')
                  | None => SPopFail
                  end
              | _ =>
                  SPopOk a
                    (SCons (Nat.pred n) Yellow (PNode (B2 b1 c1) i suf) t)
              end
          | _ => SPopFail
          end
      | Yellow, PNode pre i suf =>
          match pre with
          | B1 a =>
              match green_of_red_k (KCons Red (PNode B0 i suf) t) with
              | Some d' => SPopOk a (s_of (Nat.pred n) d')
              | None    => SPopFail
              end
          | B2 a b1 =>
              SPopOk a (SCons (Nat.pred n) Yellow (PNode (B1 b1) i suf) t)
          | B3 a b1 c1 =>
              SPopOk a (SCons (Nat.pred n) Yellow (PNode (B2 b1 c1) i suf) t)
          | B4 a b1 c1 d =>
              SPopOk a (SCons (Nat.pred n) Yellow (PNode (B3 b1 c1 d) i suf) t)
          | _ => SPopFail
          end
      | _, _ => SPopFail
      end
  end.

Lemma pop_s_spec : forall A (c : SChain A),
    pop_s c = match pop_kt4 (s_erase c) with
              | PopOk x d => SPopOk x (s_of (Nat.pred (s_size c)) d)
              | PopFail => SPopFail
              end.
Proof.
  intros A c.
  destruct c as [n b | n col p t].
  - destruct b; reflexivity.
  - destruct col.
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct pre; try reflexivity;
        cbn [pop_s pop_kt4 s_erase];
        unfold yellow_wrap_pr;
        (destruct t as [b' | col' p' t']; [reflexivity|];
         destruct col'; try reflexivity;
         destruct (green_of_red_k (KCons Red p' t')); reflexivity).
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct pre; try reflexivity.
      cbn [pop_s pop_kt4 s_erase].
      destruct (green_of_red_k (KCons Red (PNode B0 i suf) t)); reflexivity.
    + destruct p; reflexivity.
Qed.

Definition eject_s {A : Type} (c : SChain A) : spop_result A :=
  match c with
  | SEnding n b =>
      match b with
      | B0           => SPopFail
      | B1 a         => SPopOk a (SEnding (Nat.pred n) B0)
      | B2 a b1      => SPopOk b1 (SEnding (Nat.pred n) (B1 a))
      | B3 a b1 c1   => SPopOk c1 (SEnding (Nat.pred n) (B2 a b1))
      | B4 a b1 c1 d => SPopOk d (SEnding (Nat.pred n) (B3 a b1 c1))
      | B5 a b1 c1 d e => SPopOk e (SEnding (Nat.pred n) (B4 a b1 c1 d))
      end
  | SCons n col p t =>
      match col, p with
      | Green, PNode pre i suf =>
          match suf with
          | B2 a b1 =>
              match t with
              | KCons Red _ _ =>
                  match green_of_red_k t with
                  | Some t' =>
                      SPopOk b1
                        (SCons (Nat.pred n) Yellow (PNode pre i (B1 a)) t')
                  | None => SPopFail
                  end
              | _ =>
                  SPopOk b1
                    (SCons (Nat.pred n) Yellow (PNode pre i (B1 a)) t)
              end
          | B3 a b1 c1 =>
              match t with
              | KCons Red _ _ =>
                  match green_of_red_k t with
                  | Some t' =>
                      SPopOk c1
                        (SCons (Nat.pred n) Yellow (PNode pre i (B2 a b1)) t')
                  | None => SPopFail
                  end
              | _ =>
                  SPopOk c1
                    (SCons (Nat.pred n) Yellow (PNode pre i (B2 a b1)) t)
              end
          | _ => SPopFail
          end
      | Yellow, PNode pre i suf =>
          match suf with
          | B1 a =>
              match green_of_red_k (KCons Red (PNode pre i B0) t) with
              | Some d' => SPopOk a (s_of (Nat.pred n) d')
              | None    => SPopFail
              end
          | B2 a b1 =>
              SPopOk b1 (SCons (Nat.pred n) Yellow (PNode pre i (B1 a)) t)
          | B3 a b1 c1 =>
              SPopOk c1 (SCons (Nat.pred n) Yellow (PNode pre i (B2 a b1)) t)
          | B4 a b1 c1 d =>
              SPopOk d (SCons (Nat.pred n) Yellow (PNode pre i (B3 a b1 c1)) t)
          | _ => SPopFail
          end
      | _, _ => SPopFail
      end
  end.

Lemma eject_s_spec : forall A (c : SChain A),
    eject_s c = match eject_kt4 (s_erase c) with
                | PopOk x d => SPopOk x (s_of (Nat.pred (s_size c)) d)
                | PopFail => SPopFail
                end.
Proof.
  intros A c.
  destruct c as [n b | n col p t].
  - destruct b; reflexivity.
  - destruct col.
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct suf; try reflexivity;
        cbn [eject_s eject_kt4 s_erase];
        unfold yellow_wrap_pr;
        (destruct t as [b' | col' p' t']; [reflexivity|];
         destruct col'; try reflexivity;
         destruct (green_of_red_k (KCons Red p' t')); reflexivity).
    + destruct p as [| pre i suf]; [reflexivity|].
      destruct suf; try reflexivity.
      cbn [eject_s eject_kt4 s_erase].
      destruct (green_of_red_k (KCons Red (PNode pre i B0) t)); reflexivity.
    + destruct p; reflexivity.
Qed.
