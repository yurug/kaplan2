
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val leb : int -> int -> bool **)

let rec leb n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n

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

type 'x kElem9 =
| XBase9 of 'x
| XStored9 of 'x stored9
and 'x stored9 =
| StoredSmall9 of 'x kElem9 KCadequeShim.buf6
| StoredBig9 of 'x kElem9 KCadequeShim.buf6 * 'x stored9 KCadequeShim.buf6
   * 'x kElem9 KCadequeShim.buf6

type 'x kCadeque9 =
| K9Empty
| K9Simple of 'x kElem9 KCadequeShim.buf6
| K9Triple of 'x kElem9 KCadequeShim.buf6 * 'x stored9 KCadequeShim.buf6
   * 'x kElem9 KCadequeShim.buf6

(** val kcad9_empty : 'a1 kCadeque9 **)

let kcad9_empty =
  K9Empty

(** val kcad9_singleton : 'a1 -> 'a1 kCadeque9 **)

let kcad9_singleton x =
  K9Simple (KCadequeShim.mkBuf6 ((XBase9 x) :: []))

(** val kelem9_to_list : 'a1 kElem9 -> 'a1 list **)

let kelem9_to_list =
  let rec kelem9_to_list0 = function
  | XBase9 x -> x :: []
  | XStored9 s -> stored9_to_list0 s
  and stored9_to_list0 = function
  | StoredSmall9 b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem9_to_list0 e) (go es)
    in go (buf6_elems b)
  | StoredBig9 (pre, sm, suf) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem9_to_list0 e) (go es)
       in go (buf6_elems pre))
      (app
        (let rec go_sm = function
         | [] -> []
         | s' :: ss -> app (stored9_to_list0 s') (go_sm ss)
         in go_sm (buf6_elems sm))
        (let rec go = function
         | [] -> []
         | e :: es -> app (kelem9_to_list0 e) (go es)
         in go (buf6_elems suf)))
  in kelem9_to_list0

(** val stored9_to_list : 'a1 stored9 -> 'a1 list **)

let stored9_to_list =
  let rec kelem9_to_list0 = function
  | XBase9 x -> x :: []
  | XStored9 s -> stored9_to_list0 s
  and stored9_to_list0 = function
  | StoredSmall9 b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem9_to_list0 e) (go es)
    in go (buf6_elems b)
  | StoredBig9 (pre, sm, suf) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem9_to_list0 e) (go es)
       in go (buf6_elems pre))
      (app
        (let rec go_sm = function
         | [] -> []
         | s' :: ss -> app (stored9_to_list0 s') (go_sm ss)
         in go_sm (buf6_elems sm))
        (let rec go = function
         | [] -> []
         | e :: es -> app (kelem9_to_list0 e) (go es)
         in go (buf6_elems suf)))
  in stored9_to_list0

(** val kcad9_to_list : 'a1 kCadeque9 -> 'a1 list **)

let kcad9_to_list = function
| K9Empty -> []
| K9Simple b ->
  let rec go = function
  | [] -> []
  | e :: es -> app (kelem9_to_list e) (go es)
  in go (buf6_elems b)
| K9Triple (h, m, t) ->
  app
    (let rec go = function
     | [] -> []
     | e :: es -> app (kelem9_to_list e) (go es)
     in go (buf6_elems h))
    (app
      (let rec go_m = function
       | [] -> []
       | s :: ss -> app (stored9_to_list s) (go_m ss)
       in go_m (buf6_elems m))
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem9_to_list e) (go es)
       in go (buf6_elems t)))

(** val buf6_concat :
    'a1 KCadequeShim.buf6 -> 'a1 KCadequeShim.buf6 -> 'a1 KCadequeShim.buf6 **)

let buf6_concat a b =
  KCadequeShim.mkBuf6 (app (buf6_elems a) (buf6_elems b))

(** val kcad9_push : 'a1 -> 'a1 kCadeque9 -> 'a1 kCadeque9 **)

let kcad9_push x = function
| K9Empty -> K9Simple (KCadequeShim.mkBuf6 ((XBase9 x) :: []))
| K9Simple b -> K9Simple (buf6_push (XBase9 x) b)
| K9Triple (h, m, t) -> K9Triple ((buf6_push (XBase9 x) h), m, t)

(** val kcad9_inject : 'a1 kCadeque9 -> 'a1 -> 'a1 kCadeque9 **)

let kcad9_inject k x =
  match k with
  | K9Empty -> K9Simple (KCadequeShim.mkBuf6 ((XBase9 x) :: []))
  | K9Simple b -> K9Simple (buf6_inject b (XBase9 x))
  | K9Triple (h, m, t) -> K9Triple (h, m, (buf6_inject t (XBase9 x)))

(** val refill_h_K9Triple :
    'a1 kElem9 KCadequeShim.buf6 -> 'a1 stored9 KCadequeShim.buf6 -> 'a1
    kElem9 KCadequeShim.buf6 -> 'a1 kCadeque9 **)

let refill_h_K9Triple h' m t =
  match buf6_pop m with
  | Some p ->
    let (cell, m_rest) = p in
    (match cell with
     | StoredSmall9 b -> K9Triple ((buf6_concat h' b), m_rest, t)
     | StoredBig9 (pre, sm, suf) ->
       let new_h = buf6_concat h' pre in
       let m_carrying_suf = buf6_push (StoredSmall9 suf) m_rest in
       let new_m = buf6_concat sm m_carrying_suf in K9Triple (new_h, new_m, t))
  | None -> K9Simple (buf6_concat h' t)

(** val refill_t_K9Triple :
    'a1 kElem9 KCadequeShim.buf6 -> 'a1 stored9 KCadequeShim.buf6 -> 'a1
    kElem9 KCadequeShim.buf6 -> 'a1 kCadeque9 **)

let refill_t_K9Triple h m t' =
  match buf6_eject m with
  | Some p ->
    let (m_rest, cell) = p in
    (match cell with
     | StoredSmall9 b -> K9Triple (h, m_rest, (buf6_concat b t'))
     | StoredBig9 (pre, sm, suf) ->
       let new_t = buf6_concat suf t' in
       let m_carrying_pre = buf6_inject m_rest (StoredSmall9 pre) in
       let new_m = buf6_concat m_carrying_pre sm in K9Triple (h, new_m, new_t))
  | None -> K9Simple (buf6_concat h t')

(** val kcad9_pop : 'a1 kCadeque9 -> ('a1 * 'a1 kCadeque9) option **)

let kcad9_pop = function
| K9Empty -> None
| K9Simple b ->
  (match buf6_pop b with
   | Some p ->
     let (k0, b') = p in
     (match k0 with
      | XBase9 x ->
        if buf6_is_empty b'
        then Some (x, K9Empty)
        else Some (x, (K9Simple b'))
      | XStored9 _ -> None)
   | None -> None)
| K9Triple (h, m, t) ->
  (match buf6_pop h with
   | Some p ->
     let (k0, h') = p in
     (match k0 with
      | XBase9 x ->
        if leb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0))))) (buf6_size h')
        then Some (x, (K9Triple (h', m, t)))
        else Some (x, (refill_h_K9Triple h' m t))
      | XStored9 _ -> None)
   | None -> None)

(** val kcad9_eject : 'a1 kCadeque9 -> ('a1 kCadeque9 * 'a1) option **)

let kcad9_eject = function
| K9Empty -> None
| K9Simple b ->
  (match buf6_eject b with
   | Some p ->
     let (b', k0) = p in
     (match k0 with
      | XBase9 x ->
        if buf6_is_empty b'
        then Some (K9Empty, x)
        else Some ((K9Simple b'), x)
      | XStored9 _ -> None)
   | None -> None)
| K9Triple (h, m, t) ->
  (match buf6_eject t with
   | Some p ->
     let (t', k0) = p in
     (match k0 with
      | XBase9 x ->
        if leb (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0))))) (buf6_size t')
        then Some ((K9Triple (h, m, t')), x)
        else Some ((refill_t_K9Triple h m t'), x)
      | XStored9 _ -> None)
   | None -> None)

(** val kcad9_concat : 'a1 kCadeque9 -> 'a1 kCadeque9 -> 'a1 kCadeque9 **)

let kcad9_concat a b =
  match a with
  | K9Empty -> b
  | K9Simple ba ->
    (match b with
     | K9Empty -> a
     | K9Simple bb -> K9Simple (buf6_concat ba bb)
     | K9Triple (h2, m2, t2) -> K9Triple ((buf6_concat ba h2), m2, t2))
  | K9Triple (h1, m1, t1) ->
    (match b with
     | K9Empty -> a
     | K9Simple bb -> K9Triple (h1, m1, (buf6_concat t1 bb))
     | K9Triple (h2, m2, t2) ->
       let cell = StoredSmall9 (buf6_concat t1 h2) in
       let m_new = buf6_concat (buf6_inject m1 cell) m2 in
       K9Triple (h1, m_new, t2))

type 'x pop_result9 =
| PopFail9
| PopOk9 of 'x * 'x kCadeque9

type 'x eject_result9 =
| EjectFail9
| EjectOk9 of 'x kCadeque9 * 'x

(** val pop_result9_of_option :
    ('a1 * 'a1 kCadeque9) option -> 'a1 pop_result9 **)

let pop_result9_of_option = function
| Some p -> let (x, k') = p in PopOk9 (x, k')
| None -> PopFail9

(** val eject_result9_of_option :
    ('a1 kCadeque9 * 'a1) option -> 'a1 eject_result9 **)

let eject_result9_of_option = function
| Some p -> let (k', x) = p in EjectOk9 (k', x)
| None -> EjectFail9

(** val kcad9_push_fast : 'a1 -> 'a1 kCadeque9 -> 'a1 kCadeque9 **)

let kcad9_push_fast =
  kcad9_push

(** val kcad9_inject_fast : 'a1 kCadeque9 -> 'a1 -> 'a1 kCadeque9 **)

let kcad9_inject_fast =
  kcad9_inject

(** val kcad9_concat_fast :
    'a1 kCadeque9 -> 'a1 kCadeque9 -> 'a1 kCadeque9 **)

let kcad9_concat_fast =
  kcad9_concat

(** val kcad9_pop_fast : 'a1 kCadeque9 -> 'a1 pop_result9 **)

let kcad9_pop_fast k =
  pop_result9_of_option (kcad9_pop k)

(** val kcad9_eject_fast : 'a1 kCadeque9 -> 'a1 eject_result9 **)

let kcad9_eject_fast k =
  eject_result9_of_option (kcad9_eject k)
