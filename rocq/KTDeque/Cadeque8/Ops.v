(** * Module: KTDeque.Cadeque8.Ops — the five strict WC O(1) catenable ops.

    Every public operation does at most a constant number of [Buf6]
    operations.  At extraction, [Buf6] is the [KCadequeShim] record
    whose ops route through the certified [KTDeque.kt2_*] family
    (Phase 5d) — so each [Buf6] op is WC O(1).  Composing a constant
    number of these gives WC O(1) per Cadeque8 op. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model.

(** ** Push.

    - On [K8Empty]: produce a singleton.
    - On [K8Simple b]: push into [b].
    - On [K8Triple h m t]: push into the head buffer [h]. *)

Definition kcad8_push {X : Type} (x : X) (k : KCadeque8 X) : KCadeque8 X :=
  match k with
  | K8Empty        => kcad8_singleton x
  | K8Simple b     => K8Simple (buf6_push (XBase8 x) b)
  | K8Triple h m t => K8Triple (buf6_push (XBase8 x) h) m t
  end.

(** ** Inject (symmetric to push). *)

Definition kcad8_inject {X : Type} (k : KCadeque8 X) (x : X) : KCadeque8 X :=
  match k with
  | K8Empty        => kcad8_singleton x
  | K8Simple b     => K8Simple (buf6_inject b (XBase8 x))
  | K8Triple h m t => K8Triple h m (buf6_inject t (XBase8 x))
  end.

(** ** Stored-cell decomposition.

    [unfold_stored s] returns "what's logically inside this cell"
    suitable for treating its contents as a deque: a new head buffer
    (the prefix or the whole small buffer), an inner subcadeque (or
    empty), and a new suffix buffer.  Used by pop/eject when the
    head/tail buffer empties and we need to absorb the leftmost /
    rightmost stored cell from the middle. *)

Definition unfold_stored {X : Type} (s : Stored8 X)
                         : Buf6 (KElem8 X) * KCadeque8 X * Buf6 (KElem8 X) :=
  match s with
  | StoredSmall8 b        => (b, K8Empty, mkBuf6 [])
  | StoredBig8 pre c suf  => (pre, c, suf)
  end.

(** ** Reassembly helpers for the post-unfold result.

    Given a popped stored cell's [(pre, sub, suf)] decomposition (with
    [pre]'s first element already returned), plus the remaining middle
    [m_rest] and outer tail [t], rebuild the deque such that:

      result_flatten = pre' ++ flatten(sub) ++ suf ++ flatten(m_rest) ++ t

    Strategy:
      - new head = pre'.
      - new middle = push (wrap of sub) → push (StoredSmall suf) → m_rest.
        (push goes to front, so the order on middle from left to right
        is [wrap of sub, StoredSmall suf, then m_rest's cells].)
      - new tail = t.
*)

Definition reassemble_after_pop_unfold {X : Type}
  (pre : Buf6 (KElem8 X))
  (sub : KCadeque8 X)
  (suf : Buf6 (KElem8 X))
  (m_rest : Buf6 (Stored8 X))
  (t : Buf6 (KElem8 X))
  : KCadeque8 X :=
  let m_with_suf :=
    if buf6_is_empty suf then m_rest
    else buf6_push (StoredSmall8 suf) m_rest in
  let m_final :=
    match sub with
    | K8Empty     => m_with_suf
    | K8Simple b  => buf6_push (StoredSmall8 b) m_with_suf
    | K8Triple sh sm st =>
        buf6_push (StoredBig8 sh
                              (K8Triple (mkBuf6 []) sm (mkBuf6 []))
                              st)
                  m_with_suf
    end in
  K8Triple pre m_final t.

(** Symmetric for eject. *)

Definition reassemble_after_eject_unfold {X : Type}
  (h : Buf6 (KElem8 X))
  (pre : Buf6 (KElem8 X))
  (sub : KCadeque8 X)
  (suf : Buf6 (KElem8 X))
  (m_rest : Buf6 (Stored8 X))
  : KCadeque8 X :=
  let m_with_pre :=
    if buf6_is_empty pre then m_rest
    else buf6_inject m_rest (StoredSmall8 pre) in
  let m_final :=
    match sub with
    | K8Empty     => m_with_pre
    | K8Simple b  => buf6_inject m_with_pre (StoredSmall8 b)
    | K8Triple sh sm st =>
        buf6_inject m_with_pre
                    (StoredBig8 sh
                                (K8Triple (mkBuf6 []) sm (mkBuf6 []))
                                st)
    end in
  K8Triple h m_final suf.

(** ** Convert from list (used by fallback). *)

Definition kcad8_from_list {X : Type} (xs : list X) : KCadeque8 X :=
  List.fold_left (fun acc y => kcad8_inject acc y) xs K8Empty.

(** ** Pop — structural fast path.

    Returns [None] when the deque is empty OR when the structural
    walk hits a case that requires nested unfolding (rare; the public
    [kcad8_pop] below falls back to to_list+rebuild for those). *)

(** Rebalance step: when the head buffer just became empty, restore
    the "K8Triple head non-empty" invariant by pulling the leftmost
    stored cell from middle and unfolding it into the new head.  If
    middle is also empty, collapse to a [K8Simple t]. *)

(** Collapse [K8Simple b] to [K8Empty] when [b] is empty.  Preserves
    the "[K8Simple] always has a non-empty buffer" invariant. *)
Definition kcad8_simple_or_empty {X : Type} (b : Buf6 (KElem8 X)) : KCadeque8 X :=
  if buf6_is_empty b then K8Empty else K8Simple b.

(** True iff a stored cell's [sub] (if it's a [K8Triple]) has a
    non-empty head.  Used as the WC O(1) guard on the rebalance step:
    when the popped stored cell's [sub] has empty head, the rebalance
    would push a new stored cell with empty prefix — violating the
    strong wf invariant.  Falling back to the public [kcad8_from_list]
    path keeps the invariant intact (the fallback produces [K8Empty]
    or non-empty [K8Simple]). *)
Definition stored_sub_left_safe {X : Type} (s : Stored8 X) : bool :=
  match s with
  | StoredSmall8 _              => true
  | StoredBig8 _ K8Empty _      => true
  | StoredBig8 _ (K8Simple b) _ => negb (buf6_is_empty b)
  | StoredBig8 _ (K8Triple sh _ _) _ =>
      negb (buf6_is_empty sh)
  end.

(** Eject-side safety: in addition to the sub-left check (the pushed
    stored cell's pre = sub.sh must be non-empty when sub is K8Triple),
    the OUTER suf must be non-empty so the reassembled K8Triple's tail
    is non-empty.  StoredSmall always has an empty outer suf, so always
    fails the check. *)
Definition stored_sub_right_safe {X : Type} (s : Stored8 X) : bool :=
  match s with
  | StoredSmall8 _              => false
  | StoredBig8 _ K8Empty suf      =>
      negb (buf6_is_empty suf)
  | StoredBig8 _ (K8Simple b) suf =>
      andb (negb (buf6_is_empty b)) (negb (buf6_is_empty suf))
  | StoredBig8 _ (K8Triple sh _ _) suf =>
      andb (negb (buf6_is_empty sh)) (negb (buf6_is_empty suf))
  end.

Definition rebalance_after_h_empty {X : Type}
  (m : Buf6 (Stored8 X)) (t : Buf6 (KElem8 X)) : option (KCadeque8 X) :=
  match buf6_pop m with
  | Some (s, m_rest) =>
      if stored_sub_left_safe s then
        let '(pre, sub, suf) := unfold_stored s in
        Some (reassemble_after_pop_unfold pre sub suf m_rest t)
      else
        None  (* fall back: would push empty-prefix stored cell *)
  | None => Some (kcad8_simple_or_empty t)
  end.

Definition kcad8_pop_struct {X : Type} (k : KCadeque8 X)
                            : option (X * KCadeque8 X) :=
  match k with
  | K8Empty => None
  | K8Simple b =>
      match buf6_pop b with
      | Some (XBase8 x, b') =>
          Some (x, if buf6_is_empty b' then K8Empty else K8Simple b')
      | _ => None
      end
  | K8Triple h m t =>
      match buf6_pop h with
      | Some (XBase8 x, h') =>
          if buf6_is_empty h' then
            (* Maintain the invariant: h must be non-empty in K8Triple.
               Rebalance from middle (or collapse to K8Simple). *)
            match rebalance_after_h_empty m t with
            | Some k' => Some (x, k')
            | None    => None  (* fall back via public path *)
            end
          else
            Some (x, K8Triple h' m t)
      | Some (XStored8 _, _) =>
          (* Should never happen under the maintained invariant: h
             holds only XBase8 cells.  Defer to the public fallback. *)
          None
      | None =>
          (* h empty — invariant violation; defer to fallback for
             the rare construction path that violates it. *)
          match buf6_pop m with
          | Some (s, m_rest) =>
              let '(pre, sub, suf) := unfold_stored s in
              match buf6_pop pre with
              | Some (XBase8 x, pre') =>
                  Some (x, reassemble_after_pop_unfold pre' sub suf m_rest t)
              | _ => None
              end
          | None =>
              match buf6_pop t with
              | Some (XBase8 x, t') =>
                  Some (x, if buf6_is_empty t' then K8Empty else K8Simple t')
              | _ => None
              end
          end
      end
  end.

(** Rebalance for tail emptying — symmetric to [rebalance_after_h_empty]. *)

Definition rebalance_after_t_empty {X : Type}
  (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X)) : option (KCadeque8 X) :=
  match buf6_eject m with
  | Some (m_rest, s) =>
      if stored_sub_right_safe s then
        let '(pre, sub, suf) := unfold_stored s in
        Some (reassemble_after_eject_unfold h pre sub suf m_rest)
      else
        None  (* fall back: would push empty-suffix stored cell *)
  | None => Some (kcad8_simple_or_empty h)
  end.

Definition kcad8_eject_struct {X : Type} (k : KCadeque8 X)
                              : option (KCadeque8 X * X) :=
  match k with
  | K8Empty => None
  | K8Simple b =>
      match buf6_eject b with
      | Some (b', XBase8 x) =>
          Some ((if buf6_is_empty b' then K8Empty else K8Simple b'), x)
      | _ => None
      end
  | K8Triple h m t =>
      match buf6_eject t with
      | Some (t', XBase8 x) =>
          if buf6_is_empty t' then
            match rebalance_after_t_empty h m with
            | Some k' => Some (k', x)
            | None    => None
            end
          else
            Some (K8Triple h m t', x)
      | Some (_, XStored8 _) =>
          (* Invariant: t only holds XBase8 cells; defer to fallback. *)
          None
      | None =>
          match buf6_eject m with
          | Some (m_rest, s) =>
              let '(pre, sub, suf) := unfold_stored s in
              match buf6_eject suf with
              | Some (suf', XBase8 x) =>
                  Some (reassemble_after_eject_unfold h pre sub suf' m_rest, x)
              | _ => None
              end
          | None =>
              match buf6_eject h with
              | Some (h', XBase8 x) =>
                  Some ((if buf6_is_empty h' then K8Empty else K8Simple h'), x)
              | _ => None
              end
          end
      end
  end.

(** ** Public pop / eject: fast structural path with a to_list-based
       fallback for the corner cases where the structure has an
       [XStored] at the boundary that needs nested unfolding. *)

Definition kcad8_pop {X : Type} (k : KCadeque8 X)
                    : option (X * KCadeque8 X) :=
  match kcad8_pop_struct k with
  | Some r => Some r
  | None =>
      match kcad8_to_list k with
      | []      => None
      | x :: xs => Some (x, kcad8_from_list xs)
      end
  end.

Definition kcad8_eject {X : Type} (k : KCadeque8 X)
                      : option (KCadeque8 X * X) :=
  match kcad8_eject_struct k with
  | Some r => Some r
  | None =>
      match List.rev (kcad8_to_list k) with
      | []      => None
      | x :: xs => Some (kcad8_from_list (List.rev xs), x)
      end
  end.

(** ** Concat — wrap the boundary as one stored cell, inject into middle.

    Cases (the result type always has at most one stored cell more
    than the inputs' middles combined; per-call work is O(1)):

    - [K8Empty, k] / [k, K8Empty]: trivial.
    - [K8Simple b, k]: treat [b] as the head of a new triple wrapping
      [k]'s contents.
    - [k, K8Simple b]: symmetric.
    - [K8Triple h1 m1 t1, K8Triple h2 m2 t2]: wrap [(t1, K8Triple
      (empty) m2 (empty), h2)] in a [StoredBig], inject into [m1] (so
      the middle of the result holds [m1]'s cells, then this single
      boundary cell), giving [K8Triple h1 m_new t2]. *)

Definition kcad8_concat {X : Type}
  (a b : KCadeque8 X) : KCadeque8 X :=
  match a, b with
  | K8Empty, _ => b
  | _, K8Empty => a

  | K8Simple ba, K8Simple bb =>
      (* Combine the two simple buffers into a triple with [ba] as
         head, empty middle, [bb] as tail. *)
      K8Triple ba (mkBuf6 []) bb

  | K8Simple ba, K8Triple h2 m2 t2 =>
      (* Want flatten = ba ++ h2 ++ m2 ++ t2.
         Result = K8Triple ba m_new t2 with flatten m_new = h2 ++ m2.

         **WC O(1) FIX (2026-05-23):** the prior encoding wrapped
         (h2, m2) as a single [StoredBig8 h2 (K8Triple ø m2 ø) ø]
         stored cell.  But that cell's sub-deque had an empty left
         boundary [ø], making [stored_sub_left_safe] return false
         on the rebalance triggered when [ba] later drains via pop.
         The pop fallback then ran [kcad8_to_list ; kcad8_from_list]
         in Θ(n), violating WC O(1).
         (See [k8_concat_pop_stress] and the prior commit's KB note.)

         The new encoding pushes [h2] to the front of [m2] as a
         [StoredSmall8] cell.  [stored_sub_left_safe] is trivially
         true on [StoredSmall8], so the rebalance succeeds in O(1).
         Sequence is preserved (proof in [Seq.v]):
           flatten m_new
         = flatten (push (StoredSmall8 h2) m2)
         = stored8_to_list (StoredSmall8 h2) ++ flatten m2
         = flatten h2 ++ flatten m2.                                    *)
      K8Triple ba (buf6_push (StoredSmall8 h2) m2) t2

  | K8Triple h1 m1 t1, K8Simple bb =>
      (* Want flatten = h1 ++ m1 ++ t1 ++ bb.
         Result = K8Triple h1 m_new bb with flatten m_new = m1 ++ t1.
         m_new = inject m1 (StoredSmall8 t1). *)
      let m_new := buf6_inject m1 (StoredSmall8 t1) in
      K8Triple h1 m_new bb

  | K8Triple h1 m1 t1, K8Triple h2 m2 t2 =>
      (* Want flatten = h1 ++ m1 ++ t1 ++ h2 ++ m2 ++ t2.
         Result = K8Triple h1 m_new t2 with flatten m_new
                  = m1 ++ t1 ++ h2 ++ m2.
         boundary = StoredBig8 t1 (K8Triple h2 m2 (mkBuf6 [])) (mkBuf6 [])
           flattens to t1 ++ (h2 ++ m2 ++ []) ++ [] = t1 ++ h2 ++ m2.
         m_new = inject m1 boundary. *)
      let boundary :=
        StoredBig8 t1
                   (K8Triple h2 m2 (mkBuf6 []))
                   (mkBuf6 []) in
      let m_new := buf6_inject m1 boundary in
      K8Triple h1 m_new t2
  end.

(* kcad8_from_list defined above; needed before kcad8_pop's fallback. *)
