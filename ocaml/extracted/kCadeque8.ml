
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val buf6_elems : 'a1 KCadequeShim.buf6 -> 'a1 list **)

let buf6_elems = KCadequeShim.buf6_elems

(** val buf6_to_list : 'a1 KCadequeShim.buf6 -> 'a1 list **)

let buf6_to_list = KCadequeShim.buf6_to_list

(** val buf6_size : 'a1 KCadequeShim.buf6 -> int **)

let buf6_size = KCadequeShim.buf6_size

(** val buf6_empty : 'a1 KCadequeShim.buf6 **)

let buf6_empty = KCadequeShim.buf6_empty

(** val buf6_singleton : 'a1 -> 'a1 KCadequeShim.buf6 **)

let buf6_singleton = KCadequeShim.buf6_singleton

(** val buf6_is_empty : 'a1 KCadequeShim.buf6 -> bool **)

let buf6_is_empty = KCadequeShim.buf6_is_empty

(** val buf6_push : 'a1 -> 'a1 KCadequeShim.buf6 -> 'a1 KCadequeShim.buf6 **)

let buf6_push = KCadequeShim.buf6_push

(** val buf6_inject :
    'a1 KCadequeShim.buf6 -> 'a1 -> 'a1 KCadequeShim.buf6 **)

let buf6_inject = KCadequeShim.buf6_inject

(** val buf6_pop :
    'a1 KCadequeShim.buf6 -> ('a1 * 'a1 KCadequeShim.buf6) option **)

let buf6_pop = KCadequeShim.buf6_pop

(** val buf6_eject :
    'a1 KCadequeShim.buf6 -> ('a1 KCadequeShim.buf6 * 'a1) option **)

let buf6_eject = KCadequeShim.buf6_eject

type 'x kElem8 =
| XBase8 of 'x
| XStored8 of 'x stored8
and 'x stored8 =
| StoredSmall8 of 'x kElem8 KCadequeShim.buf6
| StoredBig8 of 'x kElem8 KCadequeShim.buf6 * 'x kCadeque8
   * 'x kElem8 KCadequeShim.buf6
and 'x kCadeque8 =
| K8Empty
| K8Simple of 'x kElem8 KCadequeShim.buf6
| K8Triple of 'x kElem8 KCadequeShim.buf6 * 'x stored8 KCadequeShim.buf6
   * 'x kElem8 KCadequeShim.buf6

(** val kcad8_empty : 'a1 kCadeque8 **)

let kcad8_empty =
  K8Empty

(** val kcad8_singleton : 'a1 -> 'a1 kCadeque8 **)

let kcad8_singleton x =
  K8Simple (KCadequeShim.mkBuf6 ((XBase8 x) :: []))

(** val kcad8_to_list : 'a1 kCadeque8 -> 'a1 list **)

let kcad8_to_list =
  let rec kelem8_to_list = function
  | XBase8 x -> x :: []
  | XStored8 s -> stored8_to_list s
  and stored8_to_list = function
  | StoredSmall8 b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem8_to_list e) (go es)
    in go (buf6_elems b)
  | StoredBig8 (pre, c, suf) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem8_to_list e) (go es)
       in go (buf6_elems pre))
      (app (kcad8_to_list0 c)
        (let rec go = function
         | [] -> []
         | e :: es -> app (kelem8_to_list e) (go es)
         in go (buf6_elems suf)))
  and kcad8_to_list0 = function
  | K8Empty -> []
  | K8Simple b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem8_to_list e) (go es)
    in go (buf6_elems b)
  | K8Triple (h, m, t) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem8_to_list e) (go es)
       in go (buf6_elems h))
      (app
        (let rec go_m = function
         | [] -> []
         | s :: ss -> app (stored8_to_list s) (go_m ss)
         in go_m (buf6_elems m))
        (let rec go = function
         | [] -> []
         | e :: es -> app (kelem8_to_list e) (go es)
         in go (buf6_elems t)))
  in kcad8_to_list0

(** val kcad8_push : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_push x = function
| K8Empty -> kcad8_singleton x
| K8Simple b -> K8Simple (buf6_push (XBase8 x) b)
| K8Triple (h, m, t) -> K8Triple ((buf6_push (XBase8 x) h), m, t)

(** val kcad8_inject : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8 **)

let kcad8_inject k x =
  match k with
  | K8Empty -> kcad8_singleton x
  | K8Simple b -> K8Simple (buf6_inject b (XBase8 x))
  | K8Triple (h, m, t) -> K8Triple (h, m, (buf6_inject t (XBase8 x)))

(** val unfold_stored :
    'a1 stored8 -> ('a1 kElem8 KCadequeShim.buf6 * 'a1 kCadeque8) * 'a1
    kElem8 KCadequeShim.buf6 **)

let unfold_stored = function
| StoredSmall8 b -> ((b, K8Empty), (KCadequeShim.mkBuf6 []))
| StoredBig8 (pre, c, suf) -> ((pre, c), suf)

(** val reassemble_after_pop_unfold :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 kCadeque8 -> 'a1 kElem8
    KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8
    KCadequeShim.buf6 -> 'a1 kCadeque8 **)

let reassemble_after_pop_unfold pre sub suf m_rest t =
  let m_with_suf =
    if buf6_is_empty suf then m_rest else buf6_push (StoredSmall8 suf) m_rest
  in
  let m_final =
    match sub with
    | K8Empty -> m_with_suf
    | K8Simple b -> buf6_push (StoredSmall8 b) m_with_suf
    | K8Triple (sh, sm, st) ->
      buf6_push (StoredBig8 (sh, (K8Triple ((KCadequeShim.mkBuf6 []), sm,
        (KCadequeShim.mkBuf6 []))), st)) m_with_suf
  in
  K8Triple (pre, m_final, t)

(** val reassemble_after_eject_unfold :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
    kCadeque8 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1 stored8
    KCadequeShim.buf6 -> 'a1 kCadeque8 **)

let reassemble_after_eject_unfold h pre sub suf m_rest =
  let m_with_pre =
    if buf6_is_empty pre
    then m_rest
    else buf6_inject m_rest (StoredSmall8 pre)
  in
  let m_final =
    match sub with
    | K8Empty -> m_with_pre
    | K8Simple b -> buf6_inject m_with_pre (StoredSmall8 b)
    | K8Triple (sh, sm, st) ->
      buf6_inject m_with_pre (StoredBig8 (sh, (K8Triple ((KCadequeShim.mkBuf6
        []), sm, (KCadequeShim.mkBuf6 []))), st))
  in
  K8Triple (h, m_final, suf)

(** val kcad8_from_list : 'a1 list -> 'a1 kCadeque8 **)

let kcad8_from_list xs =
  fold_left kcad8_inject xs K8Empty

(** val rebalance_after_h_empty :
    'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
    kCadeque8 **)

let rebalance_after_h_empty m t =
  match buf6_pop m with
  | Some p ->
    let (s, m_rest) = p in
    let (p0, suf) = unfold_stored s in
    let (pre, sub) = p0 in reassemble_after_pop_unfold pre sub suf m_rest t
  | None -> K8Simple t

(** val kcad8_pop_struct : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option **)

let kcad8_pop_struct = function
| K8Empty -> None
| K8Simple b ->
  (match buf6_pop b with
   | Some p ->
     let (k0, b') = p in
     (match k0 with
      | XBase8 x ->
        Some (x, (if buf6_is_empty b' then K8Empty else K8Simple b'))
      | XStored8 _ -> None)
   | None -> None)
| K8Triple (h, m, t) ->
  (match buf6_pop h with
   | Some p ->
     let (k0, h') = p in
     (match k0 with
      | XBase8 x ->
        if buf6_is_empty h'
        then Some (x, (rebalance_after_h_empty m t))
        else Some (x, (K8Triple (h', m, t)))
      | XStored8 _ ->
        (match buf6_pop m with
         | Some p0 ->
           let (s, m_rest) = p0 in
           let (p1, suf) = unfold_stored s in
           let (pre, sub) = p1 in
           (match buf6_pop pre with
            | Some p2 ->
              let (k1, pre') = p2 in
              (match k1 with
               | XBase8 x ->
                 Some (x, (reassemble_after_pop_unfold pre' sub suf m_rest t))
               | XStored8 _ -> None)
            | None -> None)
         | None ->
           (match buf6_pop t with
            | Some p0 ->
              let (k1, t') = p0 in
              (match k1 with
               | XBase8 x ->
                 Some (x, (if buf6_is_empty t' then K8Empty else K8Simple t'))
               | XStored8 _ -> None)
            | None -> None)))
   | None ->
     (match buf6_pop m with
      | Some p ->
        let (s, m_rest) = p in
        let (p0, suf) = unfold_stored s in
        let (pre, sub) = p0 in
        (match buf6_pop pre with
         | Some p1 ->
           let (k0, pre') = p1 in
           (match k0 with
            | XBase8 x ->
              Some (x, (reassemble_after_pop_unfold pre' sub suf m_rest t))
            | XStored8 _ -> None)
         | None -> None)
      | None ->
        (match buf6_pop t with
         | Some p ->
           let (k0, t') = p in
           (match k0 with
            | XBase8 x ->
              Some (x, (if buf6_is_empty t' then K8Empty else K8Simple t'))
            | XStored8 _ -> None)
         | None -> None)))

(** val kcad8_eject_struct : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option **)

let kcad8_eject_struct = function
| K8Empty -> None
| K8Simple b ->
  (match buf6_eject b with
   | Some p ->
     let (b', k0) = p in
     (match k0 with
      | XBase8 x ->
        Some ((if buf6_is_empty b' then K8Empty else K8Simple b'), x)
      | XStored8 _ -> None)
   | None -> None)
| K8Triple (h, m, t) ->
  (match buf6_eject t with
   | Some p ->
     let (t', k0) = p in
     (match k0 with
      | XBase8 x -> Some ((K8Triple (h, m, t')), x)
      | XStored8 _ ->
        (match buf6_eject m with
         | Some p0 ->
           let (m_rest, s) = p0 in
           let (p1, suf) = unfold_stored s in
           let (pre, sub) = p1 in
           (match buf6_eject suf with
            | Some p2 ->
              let (suf', k1) = p2 in
              (match k1 with
               | XBase8 x ->
                 Some ((reassemble_after_eject_unfold h pre sub suf' m_rest),
                   x)
               | XStored8 _ -> None)
            | None -> None)
         | None ->
           (match buf6_eject h with
            | Some p0 ->
              let (h', k1) = p0 in
              (match k1 with
               | XBase8 x ->
                 Some ((if buf6_is_empty h' then K8Empty else K8Simple h'), x)
               | XStored8 _ -> None)
            | None -> None)))
   | None ->
     (match buf6_eject m with
      | Some p ->
        let (m_rest, s) = p in
        let (p0, suf) = unfold_stored s in
        let (pre, sub) = p0 in
        (match buf6_eject suf with
         | Some p1 ->
           let (suf', k0) = p1 in
           (match k0 with
            | XBase8 x ->
              Some ((reassemble_after_eject_unfold h pre sub suf' m_rest), x)
            | XStored8 _ -> None)
         | None -> None)
      | None ->
        (match buf6_eject h with
         | Some p ->
           let (h', k0) = p in
           (match k0 with
            | XBase8 x ->
              Some ((if buf6_is_empty h' then K8Empty else K8Simple h'), x)
            | XStored8 _ -> None)
         | None -> None)))

(** val kcad8_pop : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option **)

let kcad8_pop k =
  match kcad8_pop_struct k with
  | Some r -> Some r
  | None ->
    (match kcad8_to_list k with
     | [] -> None
     | x :: xs -> Some (x, (kcad8_from_list xs)))

(** val kcad8_eject : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option **)

let kcad8_eject k =
  match kcad8_eject_struct k with
  | Some r -> Some r
  | None ->
    (match rev (kcad8_to_list k) with
     | [] -> None
     | x :: xs -> Some ((kcad8_from_list (rev xs)), x))

(** val kcad8_concat : 'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_concat a b =
  match a with
  | K8Empty -> b
  | K8Simple ba ->
    (match b with
     | K8Empty -> a
     | K8Simple bb -> K8Triple (ba, (KCadequeShim.mkBuf6 []), bb)
     | K8Triple (h2, m2, t2) ->
       let boundary = StoredBig8 (h2, (K8Triple ((KCadequeShim.mkBuf6 []),
         m2, (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6 []))
       in
       K8Triple (ba, (KCadequeShim.mkBuf6 (boundary :: [])), t2))
  | K8Triple (h1, m1, t1) ->
    (match b with
     | K8Empty -> a
     | K8Simple bb ->
       let m_new = buf6_inject m1 (StoredSmall8 t1) in
       K8Triple (h1, m_new, bb)
     | K8Triple (h2, m2, t2) ->
       let boundary = StoredBig8 (t1, (K8Triple (h2, m2, (KCadequeShim.mkBuf6
         []))), (KCadequeShim.mkBuf6 []))
       in
       let m_new = buf6_inject m1 boundary in K8Triple (h1, m_new, t2))
