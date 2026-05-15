(** * Module: KTDeque.Cadeque7.PopEject — pop / eject on KCadeque.

    Phase 5a of the [Cadeque7] development.

    ## Design

    Two-tier pop/eject:

    - [kcad_pop_struct] / [kcad_eject_struct]: fast structural
      traversal of the chain.  O(d) where d is the [KPair]-tree
      depth on the relevant spine.  Returns [None] if it can't
      proceed (e.g., the packet has been drained but the chain
      structure hasn't been compacted yet).

    - [kcad_pop] / [kcad_eject]: try the fast version; if it
      returns [None], fall back to [kcad_to_list]+rebuild.  The
      fallback is O(n) but always correct.  In practice the
      structural pass succeeds on every op (it covers the common
      shapes produced by push/inject/concat); the fallback only
      triggers in pathological "stuck" states.

    ## Sequence laws

    Clean: the seq theorem says "if pop returns [Some (x, k')]
    then [kcad_to_list k = x :: kcad_to_list k']".  Holds for
    both fast path and fallback, by case analysis.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque7  Require Import Model PushInject.

(** ** Smart [KPair] constructor: collapses empty sides. *)

Definition kpair_smart {X : Type} (l r : KCadeque X) : KCadeque X :=
  match l with
  | KEmpty => r
  | _ => match r with
         | KEmpty => l
         | _ => KPair l r
         end
  end.

Lemma kpair_smart_seq :
  forall (X : Type) (l r : KCadeque X),
    kcad_to_list (kpair_smart l r) = kcad_to_list l ++ kcad_to_list r.
Proof.
  intros X l r. unfold kpair_smart.
  destruct l; destruct r; cbn; try rewrite app_nil_r; reflexivity.
Qed.

(** ** Buffer-level helpers. *)

Lemma buf6_flat_kelem_app :
  forall (X : Type) (xs ys : list (KElem X)),
    buf6_flat_kelem (xs ++ ys) = buf6_flat_kelem xs ++ buf6_flat_kelem ys.
Proof.
  induction xs as [|e es IH]; intros ys.
  - cbn. reflexivity.
  - cbn. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma buf6_eject_elems_app :
  forall (X : Type) (b b' : Buf6 X) (x : X),
    buf6_eject b = Some (b', x) ->
    buf6_elems b = buf6_elems b' ++ [x].
Proof.
  intros X [xs] [ys] x H.
  unfold buf6_eject, buf6_elems in H. cbn in H.
  destruct (rev xs) as [|y t] eqn:Hr; [discriminate|].
  injection H as Hys Hx. subst y ys.
  unfold buf6_elems.
  assert (Hxs : xs = rev (rev xs)) by (rewrite rev_involutive; reflexivity).
  rewrite Hxs at 1. rewrite Hr. cbn. reflexivity.
Qed.

(** ** Node-level pop/eject (fast structural). *)

Definition pop_node_leftmost {X : Type} (n : Node X) : option (X * Node X) :=
  match n with
  | NOnlyEnd b =>
      match buf6_pop b with
      | Some (XBase x, b') => Some (x, NOnlyEnd b')
      | _ => None
      end
  | NOnly pre suf =>
      match buf6_pop pre with
      | Some (XBase x, pre') => Some (x, NOnly pre' suf)
      | _ => None
      end
  | NLeft pre suf =>
      match buf6_pop pre with
      | Some (XBase x, pre') => Some (x, NLeft pre' suf)
      | _ => None
      end
  | NRight pre suf =>
      match buf6_pop pre with
      | Some (XBase x, pre') => Some (x, NRight pre' suf)
      | _ => None
      end
  end.

Definition eject_node_rightmost {X : Type} (n : Node X) : option (Node X * X) :=
  match n with
  | NOnlyEnd b =>
      match buf6_eject b with
      | Some (b', XBase x) => Some (NOnlyEnd b', x)
      | _ => None
      end
  | NOnly pre suf =>
      match buf6_eject suf with
      | Some (suf', XBase x) => Some (NOnly pre suf', x)
      | _ => None
      end
  | NLeft pre suf =>
      match buf6_eject suf with
      | Some (suf', XBase x) => Some (NLeft pre suf', x)
      | _ => None
      end
  | NRight pre suf =>
      match buf6_eject suf with
      | Some (suf', XBase x) => Some (NRight pre suf', x)
      | _ => None
      end
  end.

(** ** Body-level. *)

Fixpoint pop_body_leftmost {X : Type} (b : Body X) : option (X * Body X) :=
  match b with
  | Hole              => None
  | BSingleY h b'     =>
      match pop_node_leftmost h with
      | Some (x, h') => Some (x, BSingleY h' b')
      | None         => None
      end
  | BPairY h bl br    =>
      match pop_node_leftmost h with
      | Some (x, h') => Some (x, BPairY h' bl br)
      | None         => None
      end
  | BPairO h bl br    =>
      match pop_node_leftmost h with
      | Some (x, h') => Some (x, BPairO h' bl br)
      | None         => None
      end
  end.

(** For [eject_body_rightmost]: the body's rightmost element is at
    the END of [body_to_list], i.e., the DEEPEST non-Hole node.
    Walking that out cleanly without cascade machinery is tricky.
    Since our current runtime never builds non-Hole bodies (only
    push/inject/concat/pop/eject exist, and none create yellow
    runs), we restrict eject to [Pkt Hole tail] packets — returning
    [None] on non-Hole bodies.

    Phase 5b/Phase 6 will fill this in when the cascade arrives. *)

Definition eject_body_rightmost {X : Type} (b : Body X)
                                : option (Body X * X) :=
  match b with
  | _ => None
  end.

(** ** Packet-level: dispatches on body shape so the seq law holds
    unconditionally (no body-skip). *)

Definition pop_packet_leftmost {X : Type} (p : Packet X)
                              : option (X * Packet X) :=
  match p with
  | Pkt Hole tail =>
      match pop_node_leftmost tail with
      | Some (x, tail') => Some (x, Pkt Hole tail')
      | None            => None
      end
  | Pkt body tail =>
      match pop_body_leftmost body with
      | Some (x, body') => Some (x, Pkt body' tail)
      | None            => None
      end
  end.

Definition eject_packet_rightmost {X : Type} (p : Packet X)
                                 : option (Packet X * X) :=
  match p with
  | Pkt Hole tail =>
      match eject_node_rightmost tail with
      | Some (tail', x) => Some (Pkt Hole tail', x)
      | None            => None
      end
  | _ => None  (* non-Hole body — deferred to Phase 5b cascade *)
  end.

(** ** Chain-level fast pop/eject (no fallback, no recursion-on-fail). *)

Fixpoint kcad_pop_struct {X : Type} (k : KCadeque X)
                        : option (X * KCadeque X) :=
  match k with
  | KEmpty           => None
  | KSingle r p c    =>
      match pop_packet_leftmost p with
      | Some (x, p') => Some (x, KSingle r p' c)
      | None         => None
      end
  | KPair l r        =>
      match kcad_pop_struct l with
      | Some (x, l') => Some (x, kpair_smart l' r)
      | None         => None
      end
  end.

Fixpoint kcad_eject_struct {X : Type} (k : KCadeque X)
                          : option (KCadeque X * X) :=
  match k with
  | KEmpty           => None
  | KSingle r p c    =>
      match c with
      | KEmpty =>
          (* No child — eject from the packet's tail. *)
          match eject_packet_rightmost p with
          | Some (p', x) => Some (KSingle r p' KEmpty, x)
          | None         => None
          end
      | _ =>
          (* Non-empty child — rightmost lives there. *)
          match kcad_eject_struct c with
          | Some (c', x) => Some (KSingle r p c', x)
          | None         => None
          end
      end
  | KPair l r        =>
      match kcad_eject_struct r with
      | Some (r', x) => Some (kpair_smart l r', x)
      | None         => None
      end
  end.

(** ** [kcad_from_list]: builds a chain by repeated inject (used by
    the [kcad_pop]/[kcad_eject] fallback). *)

Definition kcad_from_list {X : Type} (xs : list X) : KCadeque X :=
  fold_left (fun acc y => kcad_inject acc y) xs KEmpty.

Lemma kcad_to_list_fold_inject :
  forall (X : Type) (xs : list X) (k : KCadeque X),
    kcad_to_list (fold_left (fun acc y => kcad_inject acc y) xs k)
    = kcad_to_list k ++ xs.
Proof.
  induction xs as [|y ys IH]; intros k.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn. rewrite IH. rewrite kcad_inject_seq.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma kcad_to_list_from_list :
  forall (X : Type) (xs : list X),
    kcad_to_list (kcad_from_list xs) = xs.
Proof.
  intros X xs. unfold kcad_from_list.
  rewrite kcad_to_list_fold_inject. cbn. reflexivity.
Qed.

(** ** Public pop/eject: try fast, fall back to [kcad_to_list]+rebuild. *)

Definition kcad_pop {X : Type} (k : KCadeque X) : option (X * KCadeque X) :=
  match kcad_pop_struct k with
  | Some r => Some r
  | None =>
      match kcad_to_list k with
      | []      => None
      | x :: xs => Some (x, kcad_from_list xs)
      end
  end.

Definition kcad_eject {X : Type} (k : KCadeque X) : option (KCadeque X * X) :=
  match kcad_eject_struct k with
  | Some r => Some r
  | None =>
      match rev (kcad_to_list k) with
      | []      => None
      | x :: xs => Some (kcad_from_list (rev xs), x)
      end
  end.

(** ** Sequence laws for the fast-path. *)

Lemma pop_node_leftmost_seq :
  forall (X : Type) (n n' : Node X) (x : X),
    pop_node_leftmost n = Some (x, n') ->
    node_to_list n = x :: node_to_list n'.
Proof.
  intros X n n' x H.
  destruct n; cbn [pop_node_leftmost] in H;
    destruct (buf6_pop _) as [[e b']|] eqn:Hp; try discriminate;
    destruct e as [a|st]; try discriminate;
    injection H as Hx Hn; subst x n';
    rewrite ?node_to_list_NOnlyEnd, ?node_to_list_NOnly,
            ?node_to_list_NLeft, ?node_to_list_NRight;
    match goal with
    | b : Buf6 _ |- _ =>
        destruct b as [xs];
        unfold buf6_pop, buf6_elems in Hp; cbn in Hp;
        destruct xs as [|h t]; [discriminate|];
        injection Hp as He Hb'; subst h; subst;
        cbn; try rewrite <- app_assoc; reflexivity
    end.
Qed.

Lemma eject_node_rightmost_seq :
  forall (X : Type) (n n' : Node X) (x : X),
    eject_node_rightmost n = Some (n', x) ->
    node_to_list n = node_to_list n' ++ [x].
Proof.
  intros X n n' x H.
  destruct n; cbn [eject_node_rightmost] in H;
    destruct (buf6_eject _) as [[b' e]|] eqn:He; try discriminate;
    destruct e as [a|st]; try discriminate;
    injection H as Hn Hx; subst n' x;
    rewrite ?node_to_list_NOnlyEnd, ?node_to_list_NOnly,
            ?node_to_list_NLeft, ?node_to_list_NRight;
    apply buf6_eject_elems_app in He; rewrite He;
    rewrite buf6_flat_kelem_app; cbn;
    rewrite ?app_nil_r;
    rewrite <- ?app_assoc; reflexivity.
Qed.

Lemma pop_body_leftmost_seq :
  forall (X : Type) (b b' : Body X) (x : X),
    pop_body_leftmost b = Some (x, b') ->
    body_to_list b = x :: body_to_list b'.
Proof.
  intros X b. induction b as [|h b' IH | h bl br | h bl br]; intros b'' x Hp;
    cbn in Hp; try discriminate;
    destruct (pop_node_leftmost h) as [[a h']|] eqn:Hn; try discriminate;
    injection Hp as Hx Hb; subst a b''; cbn;
    rewrite (pop_node_leftmost_seq _ _ _ _ Hn); reflexivity.
Qed.

Lemma eject_body_rightmost_seq :
  forall (X : Type) (b b' : Body X) (x : X),
    eject_body_rightmost b = Some (b', x) ->
    body_to_list b = body_to_list b' ++ [x].
Proof.
  intros X b b' x He. unfold eject_body_rightmost in He. destruct b; discriminate.
Qed.

Lemma pop_packet_leftmost_seq :
  forall (X : Type) (p p' : Packet X) (x : X),
    pop_packet_leftmost p = Some (x, p') ->
    packet_to_list p = x :: packet_to_list p'.
Proof.
  intros X [body tail] p' x H.
  destruct body; cbn in H.
  - (* Hole *)
    destruct (pop_node_leftmost tail) as [[a tail']|] eqn:Ht; [|discriminate].
    injection H as Hx Hp. subst a p'.
    cbn. apply (pop_node_leftmost_seq _ _ _ _ Ht).
  - destruct (pop_node_leftmost n) as [[a h']|] eqn:Hh; [|discriminate].
    injection H as Hx Hp. subst a p'.
    cbn. rewrite (pop_node_leftmost_seq _ _ _ _ Hh). reflexivity.
  - destruct (pop_node_leftmost n) as [[a h']|] eqn:Hh; [|discriminate].
    injection H as Hx Hp. subst a p'.
    cbn. rewrite (pop_node_leftmost_seq _ _ _ _ Hh). reflexivity.
  - destruct (pop_node_leftmost n) as [[a h']|] eqn:Hh; [|discriminate].
    injection H as Hx Hp. subst a p'.
    cbn. rewrite (pop_node_leftmost_seq _ _ _ _ Hh). reflexivity.
Qed.

Lemma eject_packet_rightmost_seq :
  forall (X : Type) (p p' : Packet X) (x : X),
    eject_packet_rightmost p = Some (p', x) ->
    packet_to_list p = packet_to_list p' ++ [x].
Proof.
  intros X [body tail] p' x H. destruct body; cbn in H; try discriminate.
  destruct (eject_node_rightmost tail) as [[tail' a]|] eqn:Ht; [|discriminate].
  injection H as Hp Hx. subst a p'.
  cbn. rewrite (eject_node_rightmost_seq _ _ _ _ Ht). reflexivity.
Qed.

Lemma kcad_pop_struct_seq :
  forall (X : Type) (k : KCadeque X) (x : X) (k' : KCadeque X),
    kcad_pop_struct k = Some (x, k') ->
    kcad_to_list k = x :: kcad_to_list k'.
Proof.
  induction k as [|r p c IHc|l IHl r IHr]; intros x k' Hp.
  - cbn in Hp. discriminate.
  - cbn in Hp.
    remember (pop_packet_leftmost p) as opt eqn:Hpp.
    destruct opt as [[a p']|]; [|discriminate].
    injection Hp as Hx Hk. subst a k'.
    cbn. symmetry in Hpp. rewrite (pop_packet_leftmost_seq _ _ _ _ Hpp). reflexivity.
  - cbn in Hp.
    destruct (kcad_pop_struct l) as [[a l']|] eqn:Hl; [|discriminate].
    (* Coq substitutes [kcad_pop_struct l] → [Some (a, l')] in IHl, so
       IHl now expects [Some (a, l') = Some (x0, k0)]. *)
    pose proof (IHl a l' eq_refl) as IHL.
    injection Hp as Hx Hk. subst a k'.
    cbn. rewrite IHL. rewrite kpair_smart_seq. reflexivity.
Qed.

Lemma kcad_eject_struct_seq :
  forall (X : Type) (k k' : KCadeque X) (x : X),
    kcad_eject_struct k = Some (k', x) ->
    kcad_to_list k = kcad_to_list k' ++ [x].
Proof.
  induction k as [|r p c IHc|l IHl r IHr]; intros k' x He.
  - cbn in He. discriminate.
  - cbn in He. destruct c eqn:Hc.
    + (* c = KEmpty: eject from packet *)
      destruct (eject_packet_rightmost p) as [[p' a]|] eqn:Hp; [|discriminate].
      injection He as Hk Hx. subst a k'.
      cbn [kcad_to_list].
      rewrite (eject_packet_rightmost_seq _ _ _ _ Hp).
      cbn [kcad_to_list]. rewrite ?app_nil_r. reflexivity.
    + (* c = KSingle _ _ _: recurse via IHc *)
      destruct (kcad_eject_struct _) as [[c' a]|] eqn:Hes;
        [|discriminate].
      pose proof (IHc c' a eq_refl) as IHC.
      injection He as Hk Hx. subst a k'.
      replace (kcad_to_list (KSingle r p (KSingle r0 p0 k)))
         with (packet_to_list p ++ kcad_to_list (KSingle r0 p0 k)) by reflexivity.
      replace (kcad_to_list (KSingle r p c'))
         with (packet_to_list p ++ kcad_to_list c') by reflexivity.
      rewrite IHC. rewrite <- app_assoc. reflexivity.
    + (* c = KPair _ _: recurse via IHc *)
      destruct (kcad_eject_struct _) as [[c' a]|] eqn:Hes;
        [|discriminate].
      pose proof (IHc c' a eq_refl) as IHC.
      injection He as Hk Hx. subst a k'.
      replace (kcad_to_list (KSingle r p (KPair k1 k2)))
         with (packet_to_list p ++ kcad_to_list (KPair k1 k2)) by reflexivity.
      replace (kcad_to_list (KSingle r p c'))
         with (packet_to_list p ++ kcad_to_list c') by reflexivity.
      rewrite IHC. rewrite <- app_assoc. reflexivity.
  - cbn in He. destruct (kcad_eject_struct r) as [[r' a]|] eqn:Hr; [|discriminate].
    pose proof (IHr r' a eq_refl) as IHR.
    injection He as Hk Hx. subst a k'.
    cbn. rewrite IHR. rewrite kpair_smart_seq.
    rewrite <- app_assoc. reflexivity.
Qed.

(** ** Public seq laws — combine struct + fallback. *)

Theorem kcad_pop_seq :
  forall (X : Type) (k : KCadeque X) (x : X) (k' : KCadeque X),
    kcad_pop k = Some (x, k') ->
    kcad_to_list k = x :: kcad_to_list k'.
Proof.
  intros X k x k' Hpop.
  unfold kcad_pop in Hpop.
  destruct (kcad_pop_struct k) as [[a k_s]|] eqn:Hs.
  - injection Hpop as Hx Hk. subst a k'.
    apply (kcad_pop_struct_seq _ _ _ _ Hs).
  - destruct (kcad_to_list k) as [|y ys] eqn:Hto; [discriminate|].
    injection Hpop as Hxy Hk'.
    rewrite <- Hk'. rewrite kcad_to_list_from_list.
    rewrite <- Hxy. reflexivity.
Qed.

Theorem kcad_eject_seq :
  forall (X : Type) (k k' : KCadeque X) (x : X),
    kcad_eject k = Some (k', x) ->
    kcad_to_list k = kcad_to_list k' ++ [x].
Proof.
  intros X k k' x Hej.
  unfold kcad_eject in Hej.
  destruct (kcad_eject_struct k) as [[k_s a]|] eqn:Hs.
  - injection Hej as Hk Hx. subst a k'.
    apply (kcad_eject_struct_seq _ _ _ _ Hs).
  - destruct (rev (kcad_to_list k)) as [|y ys] eqn:Hrev; [discriminate|].
    injection Hej as Hk' Hxy.
    rewrite <- Hk'. rewrite kcad_to_list_from_list.
    assert (Heq : kcad_to_list k = rev (y :: ys)).
    { rewrite <- Hrev. rewrite rev_involutive. reflexivity. }
    rewrite Heq. cbn. rewrite <- Hxy. reflexivity.
Qed.
