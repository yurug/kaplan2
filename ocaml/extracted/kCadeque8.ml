
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

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
| StoredMiddle8 of 'x stored8 KCadequeShim.buf6
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
  | StoredMiddle8 sm ->
    let rec go_sm = function
    | [] -> []
    | s' :: ss -> app (stored8_to_list s') (go_sm ss)
    in go_sm (buf6_elems sm)
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
| StoredMiddle8 _ ->
  (((KCadequeShim.mkBuf6 []), K8Empty), (KCadequeShim.mkBuf6 []))

let k8_small_push b rest =
  if buf6_is_empty b then rest else buf6_push (StoredSmall8 b) rest

let k8_small_inject rest b =
  if buf6_is_empty b then rest else buf6_inject rest (StoredSmall8 b)

let k8_middle_push sm rest =
  if buf6_is_empty sm then rest else buf6_push (StoredMiddle8 sm) rest

let k8_middle_inject rest sm =
  if buf6_is_empty sm then rest else buf6_inject rest (StoredMiddle8 sm)

let rec k8_push_sub sub rest =
  match sub with
  | K8Empty -> rest
  | K8Simple b -> k8_small_push b rest
  | K8Triple (sh, sm, st) ->
    k8_small_push sh (k8_middle_push sm (k8_small_push st rest))

and k8_inject_sub rest sub =
  match sub with
  | K8Empty -> rest
  | K8Simple b -> k8_small_inject rest b
  | K8Triple (sh, sm, st) ->
    k8_small_inject (k8_middle_inject (k8_small_inject rest sh) sm) st

and k8_with_front h m t =
  if not (buf6_is_empty h)
  then
    if buf6_is_empty t
    then k8_with_back h m t
    else K8Triple (h, m, t)
  else
    match buf6_pop m with
    | Some p ->
      let (cell, m_rest) = p in
      (match cell with
       | StoredSmall8 b -> k8_with_front b m_rest t
       | StoredBig8 (pre, sub, suf) ->
         let new_m = k8_push_sub sub (k8_small_push suf m_rest) in
         k8_with_front pre new_m t
       | StoredMiddle8 sm ->
         (match buf6_pop sm with
          | Some p_sm ->
            let (front_cell, sm_rest) = p_sm in
            let new_m = buf6_push front_cell (k8_middle_push sm_rest m_rest) in
            k8_with_front (KCadequeShim.mkBuf6 []) new_m t
          | None -> k8_with_front (KCadequeShim.mkBuf6 []) m_rest t))
    | None ->
      if buf6_is_empty t then K8Empty else K8Simple t

and k8_with_back h m t =
  if not (buf6_is_empty t)
  then
    if buf6_is_empty h
    then k8_with_front h m t
    else K8Triple (h, m, t)
  else
    match buf6_eject m with
    | Some p ->
      let (m_rest, cell) = p in
      (match cell with
       | StoredSmall8 b -> k8_with_back h m_rest b
       | StoredBig8 (pre, sub, suf) ->
         let new_m = k8_inject_sub (k8_small_inject m_rest pre) sub in
         k8_with_back h new_m suf
       | StoredMiddle8 sm ->
         (match buf6_eject sm with
          | Some p_sm ->
            let (sm_rest, back_cell) = p_sm in
            let new_m = buf6_inject (k8_middle_inject m_rest sm_rest) back_cell in
            k8_with_back h new_m (KCadequeShim.mkBuf6 [])
          | None -> k8_with_back h m_rest (KCadequeShim.mkBuf6 [])))
    | None ->
      if buf6_is_empty h then K8Empty else K8Simple h

(** val reassemble_after_pop_unfold :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 kCadeque8 -> 'a1 kElem8
    KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8
    KCadequeShim.buf6 -> 'a1 kCadeque8 **)

let reassemble_after_pop_unfold pre sub suf m_rest t =
  k8_with_front pre (k8_push_sub sub (k8_small_push suf m_rest)) t

(** val reassemble_after_eject_unfold :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
    kCadeque8 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1 stored8
    KCadequeShim.buf6 -> 'a1 kCadeque8 **)

let reassemble_after_eject_unfold h pre sub suf m_rest =
  k8_with_back h (k8_inject_sub (k8_small_inject m_rest pre) sub) suf

(** val kcad8_from_list : 'a1 list -> 'a1 kCadeque8 **)

let kcad8_from_list xs =
  fold_left kcad8_inject xs K8Empty

(** val kcad8_simple_or_empty :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 kCadeque8 **)

let kcad8_simple_or_empty b =
  if buf6_is_empty b then K8Empty else K8Simple b

(** val stored_sub_left_safe : 'a1 stored8 -> bool **)

let stored_sub_left_safe = function
| StoredSmall8 _ -> true
| StoredBig8 (_, k, _) ->
  (match k with
   | K8Empty -> true
   | K8Simple b -> negb (buf6_is_empty b)
   | K8Triple (sh, _, _) -> negb (buf6_is_empty sh))
| StoredMiddle8 _ -> true

(** val stored_sub_right_safe : 'a1 stored8 -> bool **)

let stored_sub_right_safe = function
| StoredSmall8 _ -> false
| StoredBig8 (_, k, suf) ->
  (match k with
   | K8Empty -> negb (buf6_is_empty suf)
   | K8Simple b -> (&&) (negb (buf6_is_empty b)) (negb (buf6_is_empty suf))
   | K8Triple (sh, _, _) ->
     (&&) (negb (buf6_is_empty sh)) (negb (buf6_is_empty suf)))
| StoredMiddle8 _ -> true

(** val rebalance_after_h_empty :
    'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
    kCadeque8 option **)

let rebalance_after_h_empty m t =
  Some (k8_with_front (KCadequeShim.mkBuf6 []) m t)

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
        then (match rebalance_after_h_empty m t with
              | Some k' -> Some (x, k')
              | None -> None)
        else Some (x, (K8Triple (h', m, t)))
      | XStored8 _ -> None)
   | None ->
     (match k8_with_front (KCadequeShim.mkBuf6 []) m t with
      | K8Empty -> None
      | K8Simple b ->
        (match buf6_pop b with
         | Some p1 ->
           let (k0, b') = p1 in
           (match k0 with
            | XBase8 x ->
              Some (x, (if buf6_is_empty b' then K8Empty else K8Simple b'))
            | XStored8 _ -> None)
         | None -> None)
      | K8Triple (h', m', t') ->
        (match buf6_pop h' with
         | Some p1 ->
           let (k0, h'') = p1 in
           (match k0 with
            | XBase8 x ->
              Some (x, (k8_with_front h'' m' t'))
            | XStored8 _ -> None)
         | None -> None)))

(** val rebalance_after_t_empty :
    'a1 kElem8 KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6 -> 'a1
    kCadeque8 option **)

let rebalance_after_t_empty h m =
  Some (k8_with_back h m (KCadequeShim.mkBuf6 []))

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
      | XBase8 x ->
        if buf6_is_empty t'
        then (match rebalance_after_t_empty h m with
              | Some k' -> Some (k', x)
              | None -> None)
        else Some ((K8Triple (h, m, t')), x)
      | XStored8 _ -> None)
   | None ->
     (match k8_with_back h m (KCadequeShim.mkBuf6 []) with
      | K8Empty -> None
      | K8Simple b ->
        (match buf6_eject b with
         | Some p1 ->
           let (b', k0) = p1 in
           (match k0 with
            | XBase8 x ->
              Some ((if buf6_is_empty b' then K8Empty else K8Simple b'), x)
            | XStored8 _ -> None)
         | None -> None)
      | K8Triple (h', m', t') ->
        (match buf6_eject t' with
         | Some p1 ->
           let (t'', k0) = p1 in
           (match k0 with
            | XBase8 x ->
              Some ((k8_with_back h' m' t''), x)
            | XStored8 _ -> None)
         | None -> None)))

(** val kcad8_pop : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option **)

let kcad8_pop k =
  kcad8_pop_struct k

(** val kcad8_eject : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option **)

let kcad8_eject k =
  kcad8_eject_struct k

(** val kcad8_concat : 'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_concat a b =
  match a with
  | K8Empty -> b
  | K8Simple ba ->
    (match b with
     | K8Empty -> a
     | K8Simple bb -> K8Triple (ba, (KCadequeShim.mkBuf6 []), bb)
     | K8Triple (h2, m2, t2) ->
       K8Triple (ba, (buf6_push (StoredSmall8 h2) m2), t2))
  | K8Triple (h1, m1, t1) ->
    (match b with
     | K8Empty -> a
     | K8Simple bb ->
       let m_new = buf6_inject m1 (StoredSmall8 t1) in
       K8Triple (h1, m_new, bb)
     | K8Triple (h2, m2, t2) ->
       (match buf6_pop t2 with
        | Some p ->
          let (x_first, t2_rest) = p in
          if buf6_is_empty t2_rest
          then let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
                 (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6 []))
               in
               K8Triple (h1, (buf6_inject m1 boundary), t2)
          else let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
                 (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6
                 (x_first :: [])))
               in
               K8Triple (h1, (buf6_inject m1 boundary), t2_rest)
        | None ->
          let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
            (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6 []))
          in
          K8Triple (h1, (buf6_inject m1 boundary), t2)))

type 'x pop_result8 =
| PopFail8
| PopOk8 of 'x * 'x kCadeque8

type 'x eject_result8 =
| EjectFail8
| EjectOk8 of 'x kCadeque8 * 'x

(** val kcad8_push_fast : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_push_fast x = function
| K8Empty -> K8Simple (KCadequeShim.mkBuf6 ((XBase8 x) :: []))
| K8Simple b -> K8Simple (buf6_push (XBase8 x) b)
| K8Triple (h, m, t) -> K8Triple ((buf6_push (XBase8 x) h), m, t)

(** val kcad8_inject_fast : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8 **)

let kcad8_inject_fast k x =
  match k with
  | K8Empty -> K8Simple (KCadequeShim.mkBuf6 ((XBase8 x) :: []))
  | K8Simple b -> K8Simple (buf6_inject b (XBase8 x))
  | K8Triple (h, m, t) -> K8Triple (h, m, (buf6_inject t (XBase8 x)))

(** val kcad8_pop_struct_fast : 'a1 kCadeque8 -> 'a1 pop_result8 **)

let kcad8_pop_struct_fast = function
| K8Empty -> PopFail8
| K8Simple b ->
  (match buf6_pop b with
   | Some p ->
     let (k0, b') = p in
     (match k0 with
      | XBase8 x ->
        PopOk8 (x, (if buf6_is_empty b' then K8Empty else K8Simple b'))
      | XStored8 _ -> PopFail8)
   | None -> PopFail8)
| K8Triple (h, m, t) ->
  (match buf6_pop h with
   | Some p ->
     let (k0, h') = p in
     (match k0 with
      | XBase8 x ->
        if buf6_is_empty h'
        then (match rebalance_after_h_empty m t with
              | Some k' -> PopOk8 (x, k')
              | None -> PopFail8)
        else PopOk8 (x, (K8Triple (h', m, t)))
      | XStored8 _ -> PopFail8)
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
              PopOk8 (x, (reassemble_after_pop_unfold pre' sub suf m_rest t))
            | XStored8 _ -> PopFail8)
         | None -> PopFail8)
      | None ->
        (match buf6_pop t with
         | Some p ->
           let (k0, t') = p in
           (match k0 with
            | XBase8 x ->
              PopOk8 (x, (if buf6_is_empty t' then K8Empty else K8Simple t'))
            | XStored8 _ -> PopFail8)
         | None -> PopFail8)))

(** val kcad8_pop_fast : 'a1 kCadeque8 -> 'a1 pop_result8 **)

let kcad8_pop_fast k =
  match kcad8_pop k with
  | Some (x, k') -> PopOk8 (x, k')
  | None -> PopFail8

(** val kcad8_eject_struct_fast : 'a1 kCadeque8 -> 'a1 eject_result8 **)

let kcad8_eject_struct_fast = function
| K8Empty -> EjectFail8
| K8Simple b ->
  (match buf6_eject b with
   | Some p ->
     let (b', k0) = p in
     (match k0 with
      | XBase8 x ->
        EjectOk8 ((if buf6_is_empty b' then K8Empty else K8Simple b'), x)
      | XStored8 _ -> EjectFail8)
   | None -> EjectFail8)
| K8Triple (h, m, t) ->
  (match buf6_eject t with
   | Some p ->
     let (t', k0) = p in
     (match k0 with
      | XBase8 x ->
        if buf6_is_empty t'
        then (match rebalance_after_t_empty h m with
              | Some k' -> EjectOk8 (k', x)
              | None -> EjectFail8)
        else EjectOk8 ((K8Triple (h, m, t')), x)
      | XStored8 _ -> EjectFail8)
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
              EjectOk8
                ((reassemble_after_eject_unfold h pre sub suf' m_rest), x)
            | XStored8 _ -> EjectFail8)
         | None -> EjectFail8)
      | None ->
        (match buf6_eject h with
         | Some p ->
           let (h', k0) = p in
           (match k0 with
            | XBase8 x ->
              EjectOk8 ((if buf6_is_empty h' then K8Empty else K8Simple h'),
                x)
            | XStored8 _ -> EjectFail8)
         | None -> EjectFail8)))

(** val kcad8_eject_fast : 'a1 kCadeque8 -> 'a1 eject_result8 **)

let kcad8_eject_fast k =
  match kcad8_eject k with
  | Some (k', x) -> EjectOk8 (k', x)
  | None -> EjectFail8

(** val kcad8_concat_fast :
    'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_concat_fast a b =
  match a with
  | K8Empty -> b
  | K8Simple ba ->
    (match b with
     | K8Empty -> a
     | K8Simple bb -> K8Triple (ba, (KCadequeShim.mkBuf6 []), bb)
     | K8Triple (h2, m2, t2) ->
       K8Triple (ba, (buf6_push (StoredSmall8 h2) m2), t2))
  | K8Triple (h1, m1, t1) ->
    (match b with
     | K8Empty -> a
     | K8Simple bb -> K8Triple (h1, (buf6_inject m1 (StoredSmall8 t1)), bb)
     | K8Triple (h2, m2, t2) ->
       (match buf6_pop t2 with
        | Some p ->
          let (x_first, t2_rest) = p in
          if buf6_is_empty t2_rest
          then let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
                 (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6 []))
               in
               K8Triple (h1, (buf6_inject m1 boundary), t2)
          else let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
                 (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6
                 (x_first :: [])))
               in
               K8Triple (h1, (buf6_inject m1 boundary), t2_rest)
        | None ->
          let boundary = StoredBig8 (t1, (K8Triple (h2, m2,
            (KCadequeShim.mkBuf6 []))), (KCadequeShim.mkBuf6 []))
          in
          K8Triple (h1, (buf6_inject m1 boundary), t2)))

(** val kcad8_push_inline : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8 **)

let kcad8_push_inline =
  kcad8_push_fast

(** val kcad8_inject_inline : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8 **)

let kcad8_inject_inline =
  kcad8_inject_fast

(** val kcad8_pop_inline : 'a1 kCadeque8 -> 'a1 pop_result8 **)

let kcad8_pop_inline =
  kcad8_pop_fast

(** val kcad8_eject_inline : 'a1 kCadeque8 -> 'a1 eject_result8 **)

let kcad8_eject_inline =
  kcad8_eject_fast
