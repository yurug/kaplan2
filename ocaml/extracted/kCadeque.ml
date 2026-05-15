
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

type regularityTag =
| RegG
| RegR

type 'x kElem =
| XBase of 'x
| XStored of 'x stored
and 'x stored =
| StoredSmall of 'x kElem buf6
| StoredBig of 'x kElem buf6 * 'x kCadeque * 'x kElem buf6
and 'x kCadeque =
| KEmpty
| KSingle of regularityTag * 'x packet * 'x kCadeque
| KPair of 'x kCadeque * 'x kCadeque
and 'x packet =
| Pkt of 'x body * 'x node
and 'x body =
| Hole
| BSingleY of 'x node * 'x body
| BPairY of 'x node * 'x body * 'x body
| BPairO of 'x node * 'x body * 'x body
and 'x node =
| NOnlyEnd of 'x kElem buf6
| NOnly of 'x kElem buf6 * 'x kElem buf6
| NLeft of 'x kElem buf6 * 'x kElem buf6
| NRight of 'x kElem buf6 * 'x kElem buf6

(** val kcad_empty : 'a1 kCadeque **)

let kcad_empty =
  KEmpty

(** val kcad_singleton : 'a1 -> 'a1 kCadeque **)

let kcad_singleton x =
  KSingle (RegG, (Pkt (Hole, (NOnlyEnd ((XBase x) :: [])))), KEmpty)

(** val kcad_to_list : 'a1 kCadeque -> 'a1 list **)

let kcad_to_list =
  let rec kelem_to_list = function
  | XBase x -> x :: []
  | XStored s -> stored_to_list s
  and stored_to_list = function
  | StoredSmall b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem_to_list e) (go es)
    in go b
  | StoredBig (b, c, b0) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b)
      (app (kcad_to_list0 c)
        (let rec go = function
         | [] -> []
         | e :: es -> app (kelem_to_list e) (go es)
         in go b0))
  and kcad_to_list0 = function
  | KEmpty -> []
  | KSingle (_, p, c) -> app (packet_to_list p) (kcad_to_list0 c)
  | KPair (l, r) -> app (kcad_to_list0 l) (kcad_to_list0 r)
  and packet_to_list = function
  | Pkt (b, n) -> app (body_to_list b) (node_to_list n)
  and body_to_list = function
  | Hole -> []
  | BSingleY (n, inner) -> app (node_to_list n) (body_to_list inner)
  | BPairY (n, bl, br) ->
    app (node_to_list n) (app (body_to_list bl) (body_to_list br))
  | BPairO (n, bl, br) ->
    app (node_to_list n) (app (body_to_list bl) (body_to_list br))
  and node_to_list = function
  | NOnlyEnd b ->
    let rec go = function
    | [] -> []
    | e :: es -> app (kelem_to_list e) (go es)
    in go b
  | NOnly (b, b0) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b)
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b0)
  | NLeft (b, b0) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b)
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b0)
  | NRight (b, b0) ->
    app
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b)
      (let rec go = function
       | [] -> []
       | e :: es -> app (kelem_to_list e) (go es)
       in go b0)
  in kcad_to_list0

(** val push_node : 'a1 -> 'a1 node -> 'a1 node **)

let push_node x = function
| NOnlyEnd b -> NOnlyEnd (buf6_push (XBase x) b)
| NOnly (pre, suf) -> NOnly ((buf6_push (XBase x) pre), suf)
| NLeft (pre, suf) -> NLeft ((buf6_push (XBase x) pre), suf)
| NRight (pre, suf) -> NRight ((buf6_push (XBase x) pre), suf)

(** val inject_node : 'a1 node -> 'a1 -> 'a1 node **)

let inject_node n x =
  match n with
  | NOnlyEnd b -> NOnlyEnd (buf6_inject b (XBase x))
  | NOnly (pre, suf) -> NOnly (pre, (buf6_inject suf (XBase x)))
  | NLeft (pre, suf) -> NLeft (pre, (buf6_inject suf (XBase x)))
  | NRight (pre, suf) -> NRight (pre, (buf6_inject suf (XBase x)))

(** val push_packet : 'a1 -> 'a1 packet -> 'a1 packet **)

let push_packet x = function
| Pkt (b, tail) ->
  (match b with
   | Hole -> Pkt (Hole, (push_node x tail))
   | BSingleY (head, body0) ->
     Pkt ((BSingleY ((push_node x head), body0)), tail)
   | BPairY (head, bl, br) ->
     Pkt ((BPairY ((push_node x head), bl, br)), tail)
   | BPairO (head, bl, br) ->
     Pkt ((BPairO ((push_node x head), bl, br)), tail))

(** val inject_packet : 'a1 packet -> 'a1 -> 'a1 packet **)

let inject_packet p x =
  let Pkt (body0, tail) = p in Pkt (body0, (inject_node tail x))

(** val kcad_push : 'a1 -> 'a1 kCadeque -> 'a1 kCadeque **)

let rec kcad_push x = function
| KEmpty -> kcad_singleton x
| KSingle (r, p, c) -> KSingle (r, (push_packet x p), c)
| KPair (l, r) -> KPair ((kcad_push x l), r)

(** val kcad_inject : 'a1 kCadeque -> 'a1 -> 'a1 kCadeque **)

let rec kcad_inject k x =
  match k with
  | KEmpty -> kcad_singleton x
  | KSingle (r, p, c) ->
    (match c with
     | KEmpty -> KSingle (r, (inject_packet p x), KEmpty)
     | _ -> KSingle (r, p, (kcad_inject c x)))
  | KPair (l, r) -> KPair (l, (kcad_inject r x))

(** val kpair_smart : 'a1 kCadeque -> 'a1 kCadeque -> 'a1 kCadeque **)

let kpair_smart l r =
  match l with
  | KEmpty -> r
  | _ -> (match r with
          | KEmpty -> l
          | _ -> KPair (l, r))

(** val pop_node_leftmost : 'a1 node -> ('a1 * 'a1 node) option **)

let pop_node_leftmost = function
| NOnlyEnd b ->
  (match buf6_pop b with
   | Some p ->
     let (k, b') = p in
     (match k with
      | XBase x -> Some (x, (NOnlyEnd b'))
      | XStored _ -> None)
   | None -> None)
| NOnly (pre, suf) ->
  (match buf6_pop pre with
   | Some p ->
     let (k, pre') = p in
     (match k with
      | XBase x -> Some (x, (NOnly (pre', suf)))
      | XStored _ -> None)
   | None -> None)
| NLeft (pre, suf) ->
  (match buf6_pop pre with
   | Some p ->
     let (k, pre') = p in
     (match k with
      | XBase x -> Some (x, (NLeft (pre', suf)))
      | XStored _ -> None)
   | None -> None)
| NRight (pre, suf) ->
  (match buf6_pop pre with
   | Some p ->
     let (k, pre') = p in
     (match k with
      | XBase x -> Some (x, (NRight (pre', suf)))
      | XStored _ -> None)
   | None -> None)

(** val eject_node_rightmost : 'a1 node -> ('a1 node * 'a1) option **)

let eject_node_rightmost = function
| NOnlyEnd b ->
  (match buf6_eject b with
   | Some p ->
     let (b', k) = p in
     (match k with
      | XBase x -> Some ((NOnlyEnd b'), x)
      | XStored _ -> None)
   | None -> None)
| NOnly (pre, suf) ->
  (match buf6_eject suf with
   | Some p ->
     let (suf', k) = p in
     (match k with
      | XBase x -> Some ((NOnly (pre, suf')), x)
      | XStored _ -> None)
   | None -> None)
| NLeft (pre, suf) ->
  (match buf6_eject suf with
   | Some p ->
     let (suf', k) = p in
     (match k with
      | XBase x -> Some ((NLeft (pre, suf')), x)
      | XStored _ -> None)
   | None -> None)
| NRight (pre, suf) ->
  (match buf6_eject suf with
   | Some p ->
     let (suf', k) = p in
     (match k with
      | XBase x -> Some ((NRight (pre, suf')), x)
      | XStored _ -> None)
   | None -> None)

(** val pop_body_leftmost : 'a1 body -> ('a1 * 'a1 body) option **)

let rec pop_body_leftmost = function
| Hole -> None
| BSingleY (h, b') ->
  (match pop_node_leftmost h with
   | Some p -> let (x, h') = p in Some (x, (BSingleY (h', b')))
   | None -> None)
| BPairY (h, bl, br) ->
  (match pop_node_leftmost h with
   | Some p -> let (x, h') = p in Some (x, (BPairY (h', bl, br)))
   | None -> None)
| BPairO (h, bl, br) ->
  (match pop_node_leftmost h with
   | Some p -> let (x, h') = p in Some (x, (BPairO (h', bl, br)))
   | None -> None)

(** val pop_packet_leftmost : 'a1 packet -> ('a1 * 'a1 packet) option **)

let pop_packet_leftmost = function
| Pkt (body0, tail) ->
  (match body0 with
   | Hole ->
     (match pop_node_leftmost tail with
      | Some p0 -> let (x, tail') = p0 in Some (x, (Pkt (Hole, tail')))
      | None -> None)
   | _ ->
     (match pop_body_leftmost body0 with
      | Some p0 -> let (x, body') = p0 in Some (x, (Pkt (body', tail)))
      | None -> None))

(** val eject_packet_rightmost : 'a1 packet -> ('a1 packet * 'a1) option **)

let eject_packet_rightmost = function
| Pkt (b, tail) ->
  (match b with
   | Hole ->
     (match eject_node_rightmost tail with
      | Some p0 -> let (tail', x) = p0 in Some ((Pkt (Hole, tail')), x)
      | None -> None)
   | _ -> None)

(** val kcad_pop_struct : 'a1 kCadeque -> ('a1 * 'a1 kCadeque) option **)

let rec kcad_pop_struct = function
| KEmpty -> None
| KSingle (r, p, c) ->
  (match pop_packet_leftmost p with
   | Some p0 -> let (x, p') = p0 in Some (x, (KSingle (r, p', c)))
   | None -> None)
| KPair (l, r) ->
  (match kcad_pop_struct l with
   | Some p -> let (x, l') = p in Some (x, (kpair_smart l' r))
   | None -> None)

(** val kcad_eject_struct : 'a1 kCadeque -> ('a1 kCadeque * 'a1) option **)

let rec kcad_eject_struct = function
| KEmpty -> None
| KSingle (r, p, c) ->
  (match c with
   | KEmpty ->
     (match eject_packet_rightmost p with
      | Some p0 -> let (p', x) = p0 in Some ((KSingle (r, p', KEmpty)), x)
      | None -> None)
   | _ ->
     (match kcad_eject_struct c with
      | Some p0 -> let (c', x) = p0 in Some ((KSingle (r, p, c')), x)
      | None -> None))
| KPair (l, r) ->
  (match kcad_eject_struct r with
   | Some p -> let (r', x) = p in Some ((kpair_smart l r'), x)
   | None -> None)

(** val kcad_from_list : 'a1 list -> 'a1 kCadeque **)

let kcad_from_list xs =
  fold_left kcad_inject xs KEmpty

(** val kcad_pop : 'a1 kCadeque -> ('a1 * 'a1 kCadeque) option **)

let kcad_pop k =
  match kcad_pop_struct k with
  | Some r -> Some r
  | None ->
    (match kcad_to_list k with
     | [] -> None
     | x :: xs -> Some (x, (kcad_from_list xs)))

(** val kcad_eject : 'a1 kCadeque -> ('a1 kCadeque * 'a1) option **)

let kcad_eject k =
  match kcad_eject_struct k with
  | Some r -> Some r
  | None ->
    (match rev (kcad_to_list k) with
     | [] -> None
     | x :: xs -> Some ((kcad_from_list (rev xs)), x))

(** val kcad_concat : 'a1 kCadeque -> 'a1 kCadeque -> 'a1 kCadeque **)

let kcad_concat k1 k2 =
  match k1 with
  | KEmpty -> k2
  | _ -> (match k2 with
          | KEmpty -> k1
          | _ -> KPair (k1, k2))
