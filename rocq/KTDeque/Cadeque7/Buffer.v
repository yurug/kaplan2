(** * Module: KTDeque.Cadeque7.Buffer — two-list deque-backed buffer.

    Phase 5b foundation: replace [Buf6] (= [list X]) with a buffer
    that supports O(1) inject and eject as well as O(1) push and pop.

    ## Design

    [KBuf X] = (front : list X, back : list X) where:
      - [front] holds the first elements in order
      - [back] holds the LAST elements in REVERSE order

    Sequence: [to_list (f, b) = f ++ rev b].

    Operations:
      - push   : O(1)  — cons onto front
      - inject : O(1)  — cons onto back (in reverse)
      - pop    : O(1) amortized — head of front; rebalance if empty
      - eject  : O(1) amortized — head of back; rebalance if empty

    For WC O(1) we'd use Okasaki real-time deques (rotation streams);
    for now amortized is sufficient for the bench.
*)

From Stdlib Require Import List Lia.
Import ListNotations.

(** ** The type. *)

Record KBuf (X : Type) : Type := mkKBuf {
  kbuf_front : list X;
  kbuf_back  : list X    (* reversed *)
}.

Arguments mkKBuf {X} _ _.
Arguments kbuf_front {X} _.
Arguments kbuf_back  {X} _.

(** ** Sequence semantics. *)

Definition kbuf_to_list {X : Type} (b : KBuf X) : list X :=
  kbuf_front b ++ rev (kbuf_back b).

Definition kbuf_size {X : Type} (b : KBuf X) : nat :=
  length (kbuf_front b) + length (kbuf_back b).

(** ** Distinguished values. *)

Definition kbuf_empty {X : Type} : KBuf X := mkKBuf [] [].

Definition kbuf_singleton {X : Type} (x : X) : KBuf X := mkKBuf [x] [].

(** ** Push and inject (O(1)). *)

Definition kbuf_push {X : Type} (x : X) (b : KBuf X) : KBuf X :=
  mkKBuf (x :: kbuf_front b) (kbuf_back b).

Definition kbuf_inject {X : Type} (b : KBuf X) (x : X) : KBuf X :=
  mkKBuf (kbuf_front b) (x :: kbuf_back b).

(** ** Pop (O(1) amortized).

    If [front] is non-empty, pop from it.  Otherwise [back] holds all
    the elements (in reverse) — reverse it into front and pop. *)

Definition kbuf_pop {X : Type} (b : KBuf X) : option (X * KBuf X) :=
  match kbuf_front b with
  | x :: f' => Some (x, mkKBuf f' (kbuf_back b))
  | []      =>
      match rev (kbuf_back b) with
      | x :: f' => Some (x, mkKBuf f' [])
      | []      => None
      end
  end.

(** ** Eject (O(1) amortized). *)

Definition kbuf_eject {X : Type} (b : KBuf X) : option (KBuf X * X) :=
  match kbuf_back b with
  | x :: b' => Some (mkKBuf (kbuf_front b) b', x)
  | []      =>
      match rev (kbuf_front b) with
      | x :: b' => Some (mkKBuf [] b', x)
      | []      => None
      end
  end.

(** ** Concat (O(|b1|) — appending the back of b1 to the front of b2). *)

Definition kbuf_concat {X : Type} (b1 b2 : KBuf X) : KBuf X :=
  mkKBuf (kbuf_to_list b1 ++ kbuf_front b2) (kbuf_back b2).

(** ** Sequence laws. *)

Lemma kbuf_to_list_empty :
  forall X : Type, kbuf_to_list (@kbuf_empty X) = [].
Proof. intros. reflexivity. Qed.

Lemma kbuf_to_list_singleton :
  forall (X : Type) (x : X), kbuf_to_list (kbuf_singleton x) = [x].
Proof. intros. reflexivity. Qed.

Lemma kbuf_to_list_push :
  forall (X : Type) (x : X) (b : KBuf X),
    kbuf_to_list (kbuf_push x b) = x :: kbuf_to_list b.
Proof. intros X x [f bk]. unfold kbuf_push, kbuf_to_list. cbn. reflexivity. Qed.

Lemma kbuf_to_list_inject :
  forall (X : Type) (b : KBuf X) (x : X),
    kbuf_to_list (kbuf_inject b x) = kbuf_to_list b ++ [x].
Proof.
  intros X [f bk] x. unfold kbuf_inject, kbuf_to_list. cbn.
  rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma kbuf_to_list_pop_some :
  forall (X : Type) (b b' : KBuf X) (x : X),
    kbuf_pop b = Some (x, b') ->
    kbuf_to_list b = x :: kbuf_to_list b'.
Proof.
  intros X [f bk] b' x H. unfold kbuf_pop in H. cbn in H.
  destruct f as [|y f'].
  - destruct (rev bk) as [|z f''] eqn:Hr; [discriminate|].
    injection H as Hx Hb. subst z. subst b'.
    unfold kbuf_to_list. cbn.
    assert (Hbk : bk = rev f'' ++ [x]).
    { rewrite <- (rev_involutive bk), Hr. cbn. reflexivity. }
    rewrite Hbk. rewrite rev_unit. rewrite rev_involutive.
    rewrite app_nil_r. reflexivity.
  - injection H as Hx Hb. subst y b'.
    unfold kbuf_to_list. cbn. reflexivity.
Qed.

Lemma kbuf_to_list_eject_some :
  forall (X : Type) (b b' : KBuf X) (x : X),
    kbuf_eject b = Some (b', x) ->
    kbuf_to_list b = kbuf_to_list b' ++ [x].
Proof.
  intros X [f bk] b' x H. unfold kbuf_eject in H. cbn in H.
  destruct bk as [|y bk'].
  - destruct (rev f) as [|z bk''] eqn:Hr; [discriminate|].
    injection H as Hb Hx. subst z b'.
    unfold kbuf_to_list. cbn.
    assert (Hf : f = rev bk'' ++ [x]).
    { rewrite <- (rev_involutive f), Hr. cbn. reflexivity. }
    rewrite Hf, app_nil_r. reflexivity.
  - injection H as Hb Hx. subst y b'.
    unfold kbuf_to_list. cbn.
    rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma kbuf_to_list_pop_none :
  forall (X : Type) (b : KBuf X),
    kbuf_pop b = None -> kbuf_to_list b = [].
Proof.
  intros X [f bk] H. unfold kbuf_pop in H. cbn in H.
  destruct f as [|y f']; [|discriminate].
  destruct (rev bk) as [|z f''] eqn:Hr; [|discriminate].
  unfold kbuf_to_list. cbn.
  apply (f_equal (@rev X)) in Hr. rewrite rev_involutive in Hr. rewrite Hr.
  reflexivity.
Qed.

Lemma kbuf_to_list_concat :
  forall (X : Type) (b1 b2 : KBuf X),
    kbuf_to_list (kbuf_concat b1 b2) = kbuf_to_list b1 ++ kbuf_to_list b2.
Proof.
  intros X b1 b2. unfold kbuf_concat, kbuf_to_list. cbn.
  rewrite <- app_assoc. reflexivity.
Qed.

(** ** [is_empty]: O(1) emptiness check (doesn't require rebalancing). *)

Definition kbuf_is_empty {X : Type} (b : KBuf X) : bool :=
  match kbuf_front b, kbuf_back b with
  | [], [] => true
  | _, _   => false
  end.

Lemma kbuf_is_empty_iff :
  forall (X : Type) (b : KBuf X),
    kbuf_is_empty b = true <-> kbuf_to_list b = [].
Proof.
  intros X [f bk]. unfold kbuf_is_empty, kbuf_to_list. cbn.
  split.
  - destruct f, bk; cbn; intros; try discriminate. reflexivity.
  - destruct f, bk; cbn; intros H.
    + reflexivity.
    + assert (Hr : rev bk ++ [x] = []) by exact H.
      apply (f_equal (@length X)) in Hr. rewrite app_length in Hr. cbn in Hr.
      lia.
    + discriminate.
    + discriminate.
Qed.
