
(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

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

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

type 'x buf6 = 'x list
  (* singleton inductive, whose constructor was mkBuf6 *)

(** val buf6_to_list : 'a1 buf6 -> 'a1 list **)

let buf6_to_list b =
  b

(** val buf6_size : 'a1 buf6 -> int **)

let buf6_size =
  length

(** val buf6_empty : 'a1 buf6 **)

let buf6_empty =
  []

(** val buf6_singleton : 'a1 -> 'a1 buf6 **)

let buf6_singleton x =
  x :: []

(** val buf6_push : 'a1 -> 'a1 buf6 -> 'a1 buf6 **)

let buf6_push x b =
  x :: b

(** val buf6_inject : 'a1 buf6 -> 'a1 -> 'a1 buf6 **)

let buf6_inject b x =
  app b (x :: [])

(** val buf6_pop : 'a1 buf6 -> ('a1 * 'a1 buf6) option **)

let buf6_pop = function
| [] -> None
| x :: xs -> Some (x, xs)

(** val buf6_eject : 'a1 buf6 -> ('a1 buf6 * 'a1) option **)

let buf6_eject b =
  match rev b with
  | [] -> None
  | x :: xs -> Some ((rev xs), x)

(** val buf6_concat : 'a1 buf6 -> 'a1 buf6 -> 'a1 buf6 **)

let buf6_concat =
  app

type tripleKind =
| KOnly
| KLeft
| KRight

type 'x triple =
| TOnly of 'x buf6 * 'x cadeque * 'x buf6
| TLeft of 'x buf6 * 'x cadeque * 'x buf6
| TRight of 'x buf6 * 'x cadeque * 'x buf6
and 'x cadeque =
| CEmpty
| CSingle of 'x triple
| CDouble of 'x triple * 'x triple

(** val triple_kind : 'a1 triple -> tripleKind **)

let triple_kind = function
| TOnly (_, _, _) -> KOnly
| TLeft (_, _, _) -> KLeft
| TRight (_, _, _) -> KRight

type 'x stored =
| StoredSmall of 'x buf6
| StoredBig of 'x buf6 * 'x cadeque * 'x buf6

(** val cad_empty : 'a1 cadeque **)

let cad_empty =
  CEmpty

(** val cad_singleton_only : 'a1 buf6 -> 'a1 cadeque **)

let cad_singleton_only b =
  CSingle (TOnly (b, CEmpty, buf6_empty))

(** val flat_concat : ('a2 -> 'a1 list) -> 'a2 list -> 'a1 list **)

let rec flat_concat flat = function
| [] -> []
| y :: ys -> app (flat y) (flat_concat flat ys)

(** val buf6_flatten : ('a2 -> 'a1 list) -> 'a2 buf6 -> 'a1 list **)

let buf6_flatten =
  flat_concat

(** val triple_to_list : ('a2 -> 'a1 list) -> 'a2 triple -> 'a1 list **)

let rec triple_to_list flat = function
| TOnly (pre, c, suf) ->
  app (buf6_flatten flat pre)
    (app (cad_to_list flat c) (buf6_flatten flat suf))
| TLeft (pre, c, suf) ->
  app (buf6_flatten flat pre)
    (app (cad_to_list flat c) (buf6_flatten flat suf))
| TRight (pre, c, suf) ->
  app (buf6_flatten flat pre)
    (app (cad_to_list flat c) (buf6_flatten flat suf))

(** val cad_to_list : ('a2 -> 'a1 list) -> 'a2 cadeque -> 'a1 list **)

and cad_to_list flat = function
| CEmpty -> []
| CSingle t -> triple_to_list flat t
| CDouble (tL, tR) -> app (triple_to_list flat tL) (triple_to_list flat tR)

(** val cad_to_list_base : 'a1 cadeque -> 'a1 list **)

let cad_to_list_base c =
  cad_to_list (fun x -> x :: []) c

(** val triple_push_prefix : 'a1 -> 'a1 triple -> 'a1 triple **)

let triple_push_prefix x = function
| TOnly (pre, c, suf) -> TOnly ((buf6_push x pre), c, suf)
| TLeft (pre, c, suf) -> TLeft ((buf6_push x pre), c, suf)
| TRight (pre, c, suf) -> TRight ((buf6_push x pre), c, suf)

(** val triple_inject_suffix : 'a1 triple -> 'a1 -> 'a1 triple **)

let triple_inject_suffix t x =
  match t with
  | TOnly (pre, c, suf) -> TOnly (pre, c, (buf6_inject suf x))
  | TLeft (pre, c, suf) -> TLeft (pre, c, (buf6_inject suf x))
  | TRight (pre, c, suf) -> TRight (pre, c, (buf6_inject suf x))

(** val triple_pop_prefix : 'a1 triple -> ('a1 * 'a1 triple) option **)

let triple_pop_prefix = function
| TOnly (pre, c, suf) ->
  (match buf6_pop pre with
   | Some p -> let (x, pre') = p in Some (x, (TOnly (pre', c, suf)))
   | None -> None)
| TLeft (pre, c, suf) ->
  (match buf6_pop pre with
   | Some p -> let (x, pre') = p in Some (x, (TLeft (pre', c, suf)))
   | None -> None)
| TRight (pre, c, suf) ->
  (match buf6_pop pre with
   | Some p -> let (x, pre') = p in Some (x, (TRight (pre', c, suf)))
   | None -> None)

(** val triple_eject_suffix : 'a1 triple -> ('a1 triple * 'a1) option **)

let triple_eject_suffix = function
| TOnly (pre, c, suf) ->
  (match buf6_eject suf with
   | Some p -> let (suf', x) = p in Some ((TOnly (pre, c, suf')), x)
   | None -> None)
| TLeft (pre, c, suf) ->
  (match buf6_eject suf with
   | Some p -> let (suf', x) = p in Some ((TLeft (pre, c, suf')), x)
   | None -> None)
| TRight (pre, c, suf) ->
  (match buf6_eject suf with
   | Some p -> let (suf', x) = p in Some ((TRight (pre, c, suf')), x)
   | None -> None)

(** val cad_push : 'a1 -> 'a1 cadeque -> 'a1 cadeque **)

let cad_push x = function
| CEmpty -> CSingle (TOnly ((buf6_singleton x), CEmpty, buf6_empty))
| CSingle t -> CSingle (triple_push_prefix x t)
| CDouble (tL, tR) -> CDouble ((triple_push_prefix x tL), tR)

(** val cad_inject : 'a1 cadeque -> 'a1 -> 'a1 cadeque **)

let cad_inject q x =
  match q with
  | CEmpty -> CSingle (TOnly (buf6_empty, CEmpty, (buf6_singleton x)))
  | CSingle t -> CSingle (triple_inject_suffix t x)
  | CDouble (tL, tR) -> CDouble (tL, (triple_inject_suffix tR x))

(** val cad_pop : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop = function
| CEmpty -> None
| CSingle t ->
  (match triple_pop_prefix t with
   | Some p -> let (x, t') = p in Some (x, (CSingle t'))
   | None -> None)
| CDouble (tL, tR) ->
  (match triple_pop_prefix tL with
   | Some p -> let (x, tL') = p in Some (x, (CDouble (tL', tR)))
   | None -> None)

(** val cad_eject : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject = function
| CEmpty -> None
| CSingle t ->
  (match triple_eject_suffix t with
   | Some p -> let (t', x) = p in Some ((CSingle t'), x)
   | None -> None)
| CDouble (tL, tR) ->
  (match triple_eject_suffix tR with
   | Some p -> let (tR', x) = p in Some ((CDouble (tL, tR')), x)
   | None -> None)

(** val cad_from_list : 'a1 list -> 'a1 cadeque **)

let rec cad_from_list = function
| [] -> CEmpty
| y :: ys -> cad_push y (cad_from_list ys)

(** val cad_concat : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque **)

let cad_concat a b =
  cad_from_list (app (cad_to_list_base a) (cad_to_list_base b))

(** val cad_size : 'a1 cadeque -> int **)

let cad_size q =
  length (cad_to_list_base q)

(** val cad_singleton : 'a1 -> 'a1 cadeque **)

let cad_singleton x =
  cad_push x CEmpty

(** val cad_is_empty : 'a1 cadeque -> bool **)

let cad_is_empty = function
| CEmpty -> true
| _ -> false

(** val cad_rev : 'a1 cadeque -> 'a1 cadeque **)

let cad_rev q =
  cad_from_list (rev (cad_to_list_base q))

(** val cad_fold_left : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 cadeque -> 'a2 **)

let cad_fold_left f z q =
  fold_left f (cad_to_list_base q) z

(** val cad_fold_right : ('a1 -> 'a2 -> 'a2) -> 'a1 cadeque -> 'a2 -> 'a2 **)

let cad_fold_right f q z =
  fold_right f z (cad_to_list_base q)

(** val normalize_only_empty_child : 'a1 buf6 -> 'a1 buf6 -> 'a1 cadeque **)

let normalize_only_empty_child pre suf =
  match pre with
  | [] ->
    (match suf with
     | [] -> CEmpty
     | _ :: _ -> CSingle (TOnly ((buf6_concat pre suf), CEmpty, buf6_empty)))
  | _ :: _ -> CSingle (TOnly ((buf6_concat pre suf), CEmpty, buf6_empty))

(** val cad_push_op : 'a1 -> 'a1 cadeque -> 'a1 cadeque **)

let cad_push_op x = function
| CEmpty -> CSingle (TOnly ((buf6_singleton x), CEmpty, buf6_empty))
| CSingle t ->
  (match t with
   | TOnly (pre, c, suf) ->
     (match c with
      | CEmpty ->
        (match pre with
         | [] -> normalize_only_empty_child (buf6_push x pre) suf
         | _ :: _ -> CSingle (TOnly ((buf6_push x pre), CEmpty, suf)))
      | _ -> CSingle (TOnly ((buf6_push x pre), c, suf)))
   | _ -> CSingle (triple_push_prefix x t))
| CDouble (tL, tR) -> CDouble ((triple_push_prefix x tL), tR)

(** val cad_inject_op : 'a1 cadeque -> 'a1 -> 'a1 cadeque **)

let cad_inject_op q x =
  match q with
  | CEmpty -> CSingle (TOnly (buf6_empty, CEmpty, (buf6_singleton x)))
  | CSingle t ->
    (match t with
     | TOnly (pre, c, suf) ->
       (match c with
        | CEmpty ->
          (match suf with
           | [] -> normalize_only_empty_child pre (buf6_inject suf x)
           | _ :: _ -> CSingle (TOnly (pre, CEmpty, (buf6_inject suf x))))
        | _ -> CSingle (TOnly (pre, c, (buf6_inject suf x))))
     | _ -> CSingle (triple_inject_suffix t x))
  | CDouble (tL, tR) -> CDouble (tL, (triple_inject_suffix tR x))

(** val cad_pop_op : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop_op q = match q with
| CEmpty -> None
| CSingle t ->
  (match t with
   | TOnly (pre, c, suf) ->
     (match c with
      | CEmpty ->
        (match buf6_pop pre with
         | Some p ->
           let (x, pre') = p in
           Some (x, (normalize_only_empty_child pre' suf))
         | None ->
           (match buf6_pop suf with
            | Some p ->
              let (x, suf') = p in
              Some (x, (normalize_only_empty_child buf6_empty suf'))
            | None -> None))
      | _ -> cad_pop q)
   | _ -> cad_pop q)
| CDouble (_, _) -> cad_pop q

(** val cad_eject_op : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject_op q = match q with
| CEmpty -> None
| CSingle t ->
  (match t with
   | TOnly (pre, c, suf) ->
     (match c with
      | CEmpty ->
        (match buf6_eject suf with
         | Some p ->
           let (suf', x) = p in
           Some ((normalize_only_empty_child pre suf'), x)
         | None ->
           (match buf6_eject pre with
            | Some p ->
              let (pre', x) = p in
              Some ((normalize_only_empty_child pre' buf6_empty), x)
            | None -> None))
      | _ -> cad_eject q)
   | _ -> cad_eject q)
| CDouble (_, _) -> cad_eject q

(** val cad_concat_op : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque **)

let cad_concat_op a b =
  match a with
  | CEmpty -> b
  | _ -> (match b with
          | CEmpty -> a
          | _ -> cad_concat a b)

(** val cad_from_list_op : 'a1 list -> 'a1 cadeque **)

let rec cad_from_list_op = function
| [] -> CEmpty
| y :: ys -> cad_push_op y (cad_from_list_op ys)

(** val cad_normalize : 'a1 cadeque -> 'a1 cadeque **)

let cad_normalize q =
  cad_from_list_op (cad_to_list_base q)

(** val cad_pop_op_full : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop_op_full q =
  match cad_pop_op q with
  | Some p -> let (x, q') = p in Some (x, (cad_normalize q'))
  | None -> None

(** val cad_eject_op_full : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject_op_full q =
  match cad_eject_op q with
  | Some p -> let (q', x) = p in Some ((cad_normalize q'), x)
  | None -> None

(** val cad_concat_op_full : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque **)

let cad_concat_op_full a b =
  match a with
  | CEmpty -> b
  | _ -> (match b with
          | CEmpty -> a
          | _ -> cad_normalize (cad_concat a b))
