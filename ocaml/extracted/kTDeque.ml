
type __ = Obj.t

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



module Nat =
 struct
 end

type 'a xpow = __

(** val xflat : int -> 'a1 xpow -> 'a1 list **)

let rec xflat l a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Obj.magic a) :: [])
    (fun l' -> let (x, y) = Obj.magic a in app (xflat l' x) (xflat l' y))
    l

module ElementTree =
 struct
  type 'a t = (int, 'a xpow) sigT

  (** val to_list : 'a1 t -> 'a1 list **)

  let to_list e =
    xflat (projT1 e) (projT2 e)

  (** val level : 'a1 t -> int **)

  let level =
    projT1

  (** val base : 'a1 -> 'a1 t **)

  let base a =
    ExistT (0, (Obj.magic a))

  (** val pair : 'a1 t -> 'a1 t -> 'a1 t **)

  let pair x y =
    ExistT ((Stdlib.Int.succ (level x)),
      (let ExistT (_, x0) = x in let ExistT (_, x1) = y in Obj.magic (x0, x1)))

  (** val unpair : 'a1 t -> ('a1 t * 'a1 t) option **)

  let unpair = function
  | ExistT (x, p) ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> None)
       (fun l' ->
       let (x0, y) = Obj.magic p in Some ((ExistT (l', x0)), (ExistT (l', y))))
       x)
 end

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

(** val buf5_size : 'a1 buf5 -> int **)

let buf5_size = function
| B0 -> 0
| B1 _ -> Stdlib.Int.succ 0
| B2 (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| B3 (_, _, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| B4 (_, _, _, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| B5 (_, _, _, _, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val buf5_seq : ('a1 -> 'a2 list) -> 'a1 buf5 -> 'a2 list **)

let buf5_seq flat = function
| B0 -> []
| B1 a -> flat a
| B2 (a, b0) -> app (flat a) (flat b0)
| B3 (a, b0, c) -> app (flat a) (app (flat b0) (flat c))
| B4 (a, b0, c, d) -> app (flat a) (app (flat b0) (app (flat c) (flat d)))
| B5 (a, b0, c, d, e) ->
  app (flat a) (app (flat b0) (app (flat c) (app (flat d) (flat e))))

(** val buf5_push_naive : 'a1 -> 'a1 buf5 -> 'a1 buf5 option **)

let buf5_push_naive x = function
| B0 -> Some (B1 x)
| B1 a -> Some (B2 (x, a))
| B2 (a, b0) -> Some (B3 (x, a, b0))
| B3 (a, b0, c) -> Some (B4 (x, a, b0, c))
| B4 (a, b0, c, d) -> Some (B5 (x, a, b0, c, d))
| B5 (_, _, _, _, _) -> None

(** val buf5_inject_naive : 'a1 buf5 -> 'a1 -> 'a1 buf5 option **)

let buf5_inject_naive b x =
  match b with
  | B0 -> Some (B1 x)
  | B1 a -> Some (B2 (a, x))
  | B2 (a, b0) -> Some (B3 (a, b0, x))
  | B3 (a, b0, c) -> Some (B4 (a, b0, c, x))
  | B4 (a, b0, c, d) -> Some (B5 (a, b0, c, d, x))
  | B5 (_, _, _, _, _) -> None

(** val buf5_pop_naive : 'a1 buf5 -> ('a1 * 'a1 buf5) option **)

let buf5_pop_naive = function
| B0 -> None
| B1 a -> Some (a, B0)
| B2 (a, b0) -> Some (a, (B1 b0))
| B3 (a, b0, c) -> Some (a, (B2 (b0, c)))
| B4 (a, b0, c, d) -> Some (a, (B3 (b0, c, d)))
| B5 (a, b0, c, d, e) -> Some (a, (B4 (b0, c, d, e)))

(** val buf5_eject_naive : 'a1 buf5 -> ('a1 buf5 * 'a1) option **)

let buf5_eject_naive = function
| B0 -> None
| B1 a -> Some (B0, a)
| B2 (a, b0) -> Some ((B1 a), b0)
| B3 (a, b0, c) -> Some ((B2 (a, b0)), c)
| B4 (a, b0, c, d) -> Some ((B3 (a, b0, c)), d)
| B5 (a, b0, c, d, e) -> Some ((B4 (a, b0, c, d)), e)

module E = ElementTree

type 'a packet =
| Hole
| PNode of 'a E.t buf5 * 'a packet * 'a E.t buf5

type 'a chain =
| Ending of 'a E.t buf5
| ChainCons of 'a packet * 'a chain

(** val buf_seq_E : 'a1 E.t buf5 -> 'a1 list **)

let buf_seq_E b =
  buf5_seq E.to_list b

(** val packet_seq : 'a1 packet -> 'a1 list -> 'a1 list **)

let rec packet_seq p inner =
  match p with
  | Hole -> inner
  | PNode (pre, i, suf) ->
    app (buf_seq_E pre) (app (packet_seq i inner) (buf_seq_E suf))

(** val chain_seq : 'a1 chain -> 'a1 list **)

let rec chain_seq = function
| Ending b -> buf_seq_E b
| ChainCons (p, c') -> packet_seq p (chain_seq c')

(** val chain_to_list : 'a1 chain -> 'a1 list **)

let chain_to_list =
  chain_seq

(** val empty_chain : 'a1 chain **)

let empty_chain =
  Ending B0

(** val push_chain : 'a1 E.t -> 'a1 chain -> 'a1 chain option **)

let push_chain x = function
| Ending b ->
  (match buf5_push_naive x b with
   | Some b' -> Some (Ending b')
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_push_naive x pre with
      | Some pre' -> Some (ChainCons ((PNode (pre', i, suf)), c'))
      | None -> None))

(** val inject_chain : 'a1 chain -> 'a1 E.t -> 'a1 chain option **)

let inject_chain c x =
  match c with
  | Ending b ->
    (match buf5_inject_naive b x with
     | Some b' -> Some (Ending b')
     | None -> None)
  | ChainCons (p, c') ->
    (match p with
     | Hole -> None
     | PNode (pre, i, suf) ->
       (match buf5_inject_naive suf x with
        | Some suf' -> Some (ChainCons ((PNode (pre, i, suf')), c'))
        | None -> None))

(** val pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option **)

let pop_chain = function
| Ending b ->
  (match buf5_pop_naive b with
   | Some p -> let (x, b') = p in Some (x, (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_pop_naive pre with
      | Some p0 ->
        let (x, pre') = p0 in
        Some (x, (ChainCons ((PNode (pre', i, suf)), c')))
      | None -> None))

(** val eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option **)

let eject_chain = function
| Ending b ->
  (match buf5_eject_naive b with
   | Some p -> let (b', x) = p in Some ((Ending b'), x)
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_eject_naive suf with
      | Some p0 ->
        let (suf', x_out) = p0 in
        Some ((ChainCons ((PNode (pre, i, suf')), c')), x_out)
      | None -> None))

(** val make_red_push_chain : 'a1 chain -> 'a1 chain option **)

let make_red_push_chain = function
| Ending b0 ->
  (match b0 with
   | B5 (a, b, cc, d, e) ->
     if (=) (E.level d) (E.level e)
     then Some (ChainCons ((PNode ((B3 (a, b, cc)), Hole, B0)), (Ending (B1
            (E.pair d e)))))
     else None
   | _ -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (b0, p0, suf) ->
     (match b0 with
      | B5 (a, b, cc, d, e) ->
        (match p0 with
         | Hole ->
           if (=) (E.level d) (E.level e)
           then (match push_chain (E.pair d e) c' with
                 | Some c'' ->
                   Some (ChainCons ((PNode ((B3 (a, b, cc)), Hole, suf)),
                     c''))
                 | None -> None)
           else None
         | PNode (pre', i', suf') ->
           if (=) (E.level d) (E.level e)
           then let pde = E.pair d e in
                (match buf5_push_naive pde pre' with
                 | Some pre'' ->
                   (match pre'' with
                    | B5 (_, _, _, _, _) -> None
                    | _ ->
                      Some (ChainCons ((PNode ((B3 (a, b, cc)), Hole, suf)),
                        (ChainCons ((PNode (pre'', i', suf')), c')))))
                 | None -> None)
           else None)
      | _ -> None))

(** val make_red_inject_chain : 'a1 chain -> 'a1 chain option **)

let make_red_inject_chain = function
| Ending b0 ->
  (match b0 with
   | B5 (a, b, cc, d, e) ->
     if (=) (E.level a) (E.level b)
     then Some (ChainCons ((PNode (B0, Hole, (B3 (cc, d, e)))), (Ending (B1
            (E.pair a b)))))
     else None
   | _ -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, p0, b0) ->
     (match p0 with
      | Hole ->
        (match b0 with
         | B5 (a, b, cc, d, e) ->
           if (=) (E.level a) (E.level b)
           then (match inject_chain c' (E.pair a b) with
                 | Some c'' ->
                   Some (ChainCons ((PNode (pre, Hole, (B3 (cc, d, e)))),
                     c''))
                 | None -> None)
           else None
         | _ -> None)
      | PNode (pre', i', suf') ->
        (match b0 with
         | B5 (a, b, cc, d, e) ->
           if (=) (E.level a) (E.level b)
           then let pab = E.pair a b in
                (match buf5_inject_naive suf' pab with
                 | Some suf'' ->
                   (match suf'' with
                    | B5 (_, _, _, _, _) -> None
                    | _ ->
                      Some (ChainCons ((PNode (pre, Hole, (B3 (cc, d, e)))),
                        (ChainCons ((PNode (pre', i', suf'')), c')))))
                 | None -> None)
           else None
         | _ -> None)))

(** val push_chain_full : 'a1 E.t -> 'a1 chain -> 'a1 chain option **)

let push_chain_full x = function
| Ending b ->
  (match buf5_push_naive x b with
   | Some b' ->
     (match b' with
      | B5 (a, b1, cc, d, e) ->
        make_red_push_chain (Ending (B5 (a, b1, cc, d, e)))
      | _ -> Some (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, p0, suf) ->
     (match p0 with
      | Hole ->
        (match buf5_push_naive x pre with
         | Some pre' ->
           (match pre' with
            | B5 (a, b1, cc, d, e) ->
              make_red_push_chain (ChainCons ((PNode ((B5 (a, b1, cc, d, e)),
                Hole, suf)), c'))
            | _ -> Some (ChainCons ((PNode (pre', Hole, suf)), c')))
         | None -> None)
      | PNode (pre', i', suf') ->
        (match buf5_push_naive x pre with
         | Some pre_new ->
           (match pre_new with
            | B5 (a, b1, cc, d, e) ->
              make_red_push_chain (ChainCons ((PNode ((B5 (a, b1, cc, d, e)),
                (PNode (pre', i', suf')), suf)), c'))
            | _ ->
              Some (ChainCons ((PNode (pre_new, (PNode (pre', i', suf')),
                suf)), c')))
         | None -> None)))

(** val inject_chain_full : 'a1 chain -> 'a1 E.t -> 'a1 chain option **)

let inject_chain_full c x =
  match c with
  | Ending b ->
    (match buf5_inject_naive b x with
     | Some b' ->
       (match b' with
        | B5 (a, b1, cc, d, e) ->
          make_red_inject_chain (Ending (B5 (a, b1, cc, d, e)))
        | _ -> Some (Ending b'))
     | None -> None)
  | ChainCons (p, c') ->
    (match p with
     | Hole -> None
     | PNode (pre, p0, suf) ->
       (match p0 with
        | Hole ->
          (match buf5_inject_naive suf x with
           | Some suf' ->
             (match suf' with
              | B5 (a, b1, cc, d, e) ->
                make_red_inject_chain (ChainCons ((PNode (pre, Hole, (B5 (a,
                  b1, cc, d, e)))), c'))
              | _ -> Some (ChainCons ((PNode (pre, Hole, suf')), c')))
           | None -> None)
        | PNode (pre', i', suf') ->
          (match buf5_inject_naive suf x with
           | Some suf_new ->
             (match suf_new with
              | B5 (a, b1, cc, d, e) ->
                make_red_inject_chain (ChainCons ((PNode (pre, (PNode (pre',
                  i', suf')), (B5 (a, b1, cc, d, e)))), c'))
              | _ ->
                Some (ChainCons ((PNode (pre, (PNode (pre', i', suf')),
                  suf_new)), c')))
           | None -> None)))

(** val push_chain_rec : 'a1 E.t -> 'a1 chain -> 'a1 chain option **)

let rec push_chain_rec x = function
| Ending b ->
  (match buf5_push_naive x b with
   | Some b' ->
     (match b' with
      | B5 (a, b1, cc, d, e) ->
        if (=) (E.level d) (E.level e)
        then Some (ChainCons ((PNode ((B3 (a, b1, cc)), Hole, B0)), (Ending
               (B1 (E.pair d e)))))
        else None
      | _ -> Some (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_push_naive x pre with
      | Some pre' ->
        (match pre' with
         | B5 (a, b1, cc, d, e) ->
           (match i with
            | Hole ->
              if (=) (E.level d) (E.level e)
              then (match push_chain_rec (E.pair d e) c' with
                    | Some c'' ->
                      Some (ChainCons ((PNode ((B3 (a, b1, cc)), Hole, suf)),
                        c''))
                    | None -> None)
              else None
            | PNode (_, _, _) -> None)
         | _ -> Some (ChainCons ((PNode (pre', i, suf)), c')))
      | None -> None))

(** val inject_chain_rec : 'a1 chain -> 'a1 E.t -> 'a1 chain option **)

let rec inject_chain_rec c x =
  match c with
  | Ending b ->
    (match buf5_inject_naive b x with
     | Some b' ->
       (match b' with
        | B5 (a, b1, cc, d, e) ->
          if (=) (E.level a) (E.level b1)
          then Some (ChainCons ((PNode (B0, Hole, (B3 (cc, d, e)))), (Ending
                 (B1 (E.pair a b1)))))
          else None
        | _ -> Some (Ending b'))
     | None -> None)
  | ChainCons (p, c') ->
    (match p with
     | Hole -> None
     | PNode (pre, i, suf) ->
       (match buf5_inject_naive suf x with
        | Some suf' ->
          (match suf' with
           | B5 (a, b1, cc, d, e) ->
             (match i with
              | Hole ->
                if (=) (E.level a) (E.level b1)
                then (match inject_chain_rec c' (E.pair a b1) with
                      | Some c'' ->
                        Some (ChainCons ((PNode (pre, Hole, (B3 (cc, d,
                          e)))), c''))
                      | None -> None)
                else None
              | PNode (_, _, _) -> None)
           | _ -> Some (ChainCons ((PNode (pre, i, suf')), c')))
        | None -> None))

(** val pop_chain_rec : 'a1 chain -> ('a1 E.t * 'a1 chain) option **)

let rec pop_chain_rec = function
| Ending b ->
  (match buf5_pop_naive b with
   | Some p -> let (x, b') = p in Some (x, (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_pop_naive pre with
      | Some p0 ->
        let (x, pre') = p0 in
        Some (x, (ChainCons ((PNode (pre', i, suf)), c')))
      | None ->
        (match buf5_pop_naive suf with
         | Some p0 ->
           let (x, suf') = p0 in
           Some (x, (ChainCons ((PNode (pre, i, suf')), c')))
         | None ->
           (match pop_chain_rec c' with
            | Some p0 ->
              let (paired, c'') = p0 in
              (match E.unpair paired with
               | Some p1 ->
                 let (x, y) = p1 in
                 Some (x, (ChainCons ((PNode ((B1 y), i, suf)), c'')))
               | None -> None)
            | None -> None))))

(** val eject_chain_rec : 'a1 chain -> ('a1 chain * 'a1 E.t) option **)

let rec eject_chain_rec = function
| Ending b ->
  (match buf5_eject_naive b with
   | Some p -> let (b', x) = p in Some ((Ending b'), x)
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf5_eject_naive suf with
      | Some p0 ->
        let (suf', x) = p0 in
        Some ((ChainCons ((PNode (pre, i, suf')), c')), x)
      | None ->
        (match buf5_eject_naive pre with
         | Some p0 ->
           let (pre', x) = p0 in
           Some ((ChainCons ((PNode (pre', i, suf)), c')), x)
         | None ->
           (match eject_chain_rec c' with
            | Some p0 ->
              let (c'', paired) = p0 in
              (match E.unpair paired with
               | Some p1 ->
                 let (x, y) = p1 in
                 Some ((ChainCons ((PNode (pre, i, (B1 x))), c'')), y)
               | None -> None)
            | None -> None))))

(** val make_green_pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option **)

let make_green_pop_chain = function
| Ending _ -> None
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (b, p0, suf) ->
     (match b with
      | B0 ->
        (match p0 with
         | Hole ->
           (match pop_chain c' with
            | Some p1 ->
              let (paired, c'') = p1 in
              (match E.unpair paired with
               | Some p2 ->
                 let (x, y) = p2 in
                 Some (x, (ChainCons ((PNode ((B1 y), Hole, suf)), c'')))
               | None -> None)
            | None -> None)
         | PNode (_, _, _) -> None)
      | _ -> None))

(** val make_green_eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option **)

let make_green_eject_chain = function
| Ending _ -> None
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, p0, b) ->
     (match p0 with
      | Hole ->
        (match b with
         | B0 ->
           (match eject_chain c' with
            | Some p1 ->
              let (c'', paired) = p1 in
              (match E.unpair paired with
               | Some p2 ->
                 let (x, y) = p2 in
                 Some ((ChainCons ((PNode (pre, Hole, (B1 x))), c'')), y)
               | None -> None)
            | None -> None)
         | _ -> None)
      | PNode (_, _, _) -> None))

(** val pop_chain_full : 'a1 chain -> ('a1 E.t * 'a1 chain) option **)

let pop_chain_full = function
| Ending b ->
  (match buf5_pop_naive b with
   | Some p -> let (x, b') = p in Some (x, (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, p0, suf) ->
     (match p0 with
      | Hole ->
        (match buf5_pop_naive pre with
         | Some p1 ->
           let (x, pre') = p1 in
           Some (x, (ChainCons ((PNode (pre', Hole, suf)), c')))
         | None ->
           make_green_pop_chain (ChainCons ((PNode (B0, Hole, suf)), c')))
      | PNode (_, _, _) -> None))

(** val eject_chain_full : 'a1 chain -> ('a1 chain * 'a1 E.t) option **)

let eject_chain_full = function
| Ending b ->
  (match buf5_eject_naive b with
   | Some p -> let (b', x) = p in Some ((Ending b'), x)
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, p0, suf) ->
     (match p0 with
      | Hole ->
        (match buf5_eject_naive suf with
         | Some p1 ->
           let (suf', x) = p1 in
           Some ((ChainCons ((PNode (pre, Hole, suf')), c')), x)
         | None ->
           make_green_eject_chain (ChainCons ((PNode (pre, Hole, B0)), c')))
      | PNode (_, _, _) -> None))

type color =
| Green
| Yellow
| Red

(** val buf_color : 'a1 buf5 -> color **)

let buf_color = function
| B0 -> Red
| B1 _ -> Yellow
| B4 (_, _, _, _) -> Yellow
| B5 (_, _, _, _, _) -> Red
| _ -> Green

(** val color_meet : color -> color -> color **)

let color_meet c1 c2 =
  match c1 with
  | Green -> c2
  | Yellow -> (match c2 with
               | Green -> Yellow
               | x -> x)
  | Red -> Red

module Coq_E = E

(** val green_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option **)

let green_push x = function
| B2 (a, b1) -> Some (B3 (x, a, b1))
| B3 (a, b1, c) -> Some (B4 (x, a, b1, c))
| _ -> None

(** val green_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option **)

let green_inject b x =
  match b with
  | B2 (a, b1) -> Some (B3 (a, b1, x))
  | B3 (a, b1, c) -> Some (B4 (a, b1, c, x))
  | _ -> None

(** val yellow_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option **)

let yellow_push x = function
| B1 a -> Some (B2 (x, a))
| B2 (a, b1) -> Some (B3 (x, a, b1))
| B3 (a, b1, c) -> Some (B4 (x, a, b1, c))
| B4 (a, b1, c, d) -> Some (B5 (x, a, b1, c, d))
| _ -> None

(** val yellow_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option **)

let yellow_inject b x =
  match b with
  | B1 a -> Some (B2 (a, x))
  | B2 (a, b1) -> Some (B3 (a, b1, x))
  | B3 (a, b1, c) -> Some (B4 (a, b1, c, x))
  | B4 (a, b1, c, d) -> Some (B5 (a, b1, c, d, x))
  | _ -> None

(** val green_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option **)

let green_pop = function
| B2 (a, b1) -> Some (a, (B1 b1))
| B3 (a, b1, c) -> Some (a, (B2 (b1, c)))
| _ -> None

(** val green_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option **)

let green_eject = function
| B2 (a, b1) -> Some ((B1 a), b1)
| B3 (a, b1, c) -> Some ((B2 (a, b1)), c)
| _ -> None

(** val yellow_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option **)

let yellow_pop = function
| B1 a -> Some (a, B0)
| B2 (a, b1) -> Some (a, (B1 b1))
| B3 (a, b1, c) -> Some (a, (B2 (b1, c)))
| B4 (a, b1, c, d) -> Some (a, (B3 (b1, c, d)))
| _ -> None

(** val yellow_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option **)

let yellow_eject = function
| B1 a -> Some (B0, a)
| B2 (a, b1) -> Some ((B1 a), b1)
| B3 (a, b1, c) -> Some ((B2 (a, b1)), c)
| B4 (a, b1, c, d) -> Some ((B3 (a, b1, c)), d)
| _ -> None

(** val prefix23 : 'a1 option -> ('a1 * 'a1) -> 'a1 buf5 **)

let prefix23 opt = function
| (b, c) -> (match opt with
             | Some a -> B3 (a, b, c)
             | None -> B2 (b, c))

(** val suffix23 : ('a1 * 'a1) -> 'a1 option -> 'a1 buf5 **)

let suffix23 p opt =
  let (a, b) = p in
  (match opt with
   | Some c -> B3 (a, b, c)
   | None -> B2 (a, b))

(** val suffix12 : 'a1 -> 'a1 option -> 'a1 buf5 **)

let suffix12 x = function
| Some y -> B2 (x, y)
| None -> B1 x

type 'x bdecomp_pre =
| BD_pre_underflow of 'x option
| BD_pre_ok of 'x buf5
| BD_pre_overflow of 'x buf5 * 'x * 'x

type 'x bdecomp_suf =
| BD_suf_underflow of 'x option
| BD_suf_ok of 'x buf5
| BD_suf_overflow of 'x buf5 * 'x * 'x

(** val prefix_decompose : 'a1 buf5 -> 'a1 bdecomp_pre **)

let prefix_decompose b = match b with
| B0 -> BD_pre_underflow None
| B1 x -> BD_pre_underflow (Some x)
| B4 (a, b1, c, d) -> BD_pre_overflow ((B2 (a, b1)), c, d)
| B5 (a, b1, c, d, e) -> BD_pre_overflow ((B3 (a, b1, c)), d, e)
| _ -> BD_pre_ok b

(** val suffix_decompose : 'a1 buf5 -> 'a1 bdecomp_suf **)

let suffix_decompose b = match b with
| B0 -> BD_suf_underflow None
| B1 x -> BD_suf_underflow (Some x)
| B4 (a, b1, c, d) -> BD_suf_overflow ((B2 (c, d)), a, b1)
| B5 (a, b1, c, d, e) -> BD_suf_overflow ((B3 (c, d, e)), a, b1)
| _ -> BD_suf_ok b

type 'x bsandwich =
| BS_alone of 'x option
| BS_sandwich of 'x * 'x buf5 * 'x

(** val buffer_unsandwich : 'a1 buf5 -> 'a1 bsandwich **)

let buffer_unsandwich = function
| B0 -> BS_alone None
| B1 a -> BS_alone (Some a)
| B2 (a, b1) -> BS_sandwich (a, B0, b1)
| B3 (a, b1, c) -> BS_sandwich (a, (B1 b1), c)
| B4 (a, b1, c, d) -> BS_sandwich (a, (B2 (b1, c)), d)
| B5 (a, b1, c, d, e) -> BS_sandwich (a, (B3 (b1, c, d)), e)

(** val prefix_rot : 'a1 -> 'a1 buf5 -> 'a1 buf5 * 'a1 **)

let prefix_rot x = function
| B0 -> (B0, x)
| B1 a -> ((B1 x), a)
| B2 (a, b1) -> ((B2 (x, a)), b1)
| B3 (a, b1, c) -> ((B3 (x, a, b1)), c)
| B4 (a, b1, c, d) -> ((B4 (x, a, b1, c)), d)
| B5 (a, b1, c, d, e) -> ((B5 (x, a, b1, c, d)), e)

(** val suffix_rot : 'a1 buf5 -> 'a1 -> 'a1 * 'a1 buf5 **)

let suffix_rot b x =
  match b with
  | B0 -> (x, B0)
  | B1 a -> (a, (B1 x))
  | B2 (a, b1) -> (a, (B2 (b1, x)))
  | B3 (a, b1, c) -> (a, (B3 (b1, c, x)))
  | B4 (a, b1, c, d) -> (a, (B4 (b1, c, d, x)))
  | B5 (a, b1, c, d, e) -> (a, (B5 (b1, c, d, e, x)))

(** val buffer_halve : 'a1 buf5 -> 'a1 option * ('a1 * 'a1) buf5 **)

let buffer_halve = function
| B0 -> (None, B0)
| B1 a -> ((Some a), B0)
| B2 (a, b1) -> (None, (B1 (a, b1)))
| B3 (a, b1, c) -> ((Some a), (B1 (b1, c)))
| B4 (a, b1, c, d) -> (None, (B2 ((a, b1), (c, d))))
| B5 (a, b1, c, d, e) -> ((Some a), (B2 ((b1, c), (d, e))))

(** val green_prefix_concat :
    'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
    buf5) option **)

let green_prefix_concat b1 b2 =
  match prefix_decompose b1 with
  | BD_pre_underflow opt ->
    (match green_pop b2 with
     | Some p ->
       let (ab, b2') = p in
       (match Coq_E.unpair ab with
        | Some p0 -> Some ((prefix23 opt p0), b2')
        | None -> None)
     | None -> None)
  | BD_pre_ok b1' -> Some (b1', b2)
  | BD_pre_overflow (b1', c, d) ->
    if (=) (Coq_E.level c) (Coq_E.level d)
    then (match green_push (Coq_E.pair c d) b2 with
          | Some b2' -> Some (b1', b2')
          | None -> None)
    else None

(** val green_suffix_concat :
    'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
    buf5) option **)

let green_suffix_concat b1 b2 =
  match suffix_decompose b2 with
  | BD_suf_underflow opt ->
    (match green_eject b1 with
     | Some p ->
       let (b1', ab) = p in
       (match Coq_E.unpair ab with
        | Some p0 -> Some (b1', (suffix23 p0 opt))
        | None -> None)
     | None -> None)
  | BD_suf_ok b2' -> Some (b1, b2')
  | BD_suf_overflow (b2', a, b) ->
    if (=) (Coq_E.level a) (Coq_E.level b)
    then (match green_inject b1 (Coq_E.pair a b) with
          | Some b1' -> Some (b1', b2')
          | None -> None)
    else None

(** val prefix_concat :
    'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
    buf5) option **)

let prefix_concat b1 b2 =
  match prefix_decompose b1 with
  | BD_pre_underflow opt ->
    (match yellow_pop b2 with
     | Some p ->
       let (ab, b2') = p in
       (match Coq_E.unpair ab with
        | Some p0 -> Some ((prefix23 opt p0), b2')
        | None -> None)
     | None -> None)
  | BD_pre_ok b1' -> Some (b1', b2)
  | BD_pre_overflow (b1', c, d) ->
    if (=) (Coq_E.level c) (Coq_E.level d)
    then (match yellow_push (Coq_E.pair c d) b2 with
          | Some b2' -> Some (b1', b2')
          | None -> None)
    else None

(** val suffix_concat :
    'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
    buf5) option **)

let suffix_concat b1 b2 =
  match suffix_decompose b2 with
  | BD_suf_underflow opt ->
    (match yellow_eject b1 with
     | Some p ->
       let (b1', ab) = p in
       (match Coq_E.unpair ab with
        | Some p0 -> Some (b1', (suffix23 p0 opt))
        | None -> None)
     | None -> None)
  | BD_suf_ok b2' -> Some (b1, b2')
  | BD_suf_overflow (b2', a, b) ->
    if (=) (Coq_E.level a) (Coq_E.level b)
    then (match yellow_inject b1 (Coq_E.pair a b) with
          | Some b1' -> Some (b1', b2')
          | None -> None)
    else None

(** val buffer_push_chain : 'a1 Coq_E.t -> 'a1 Coq_E.t buf5 -> 'a1 chain **)

let buffer_push_chain x = function
| B0 -> Ending (B1 x)
| B1 a -> Ending (B2 (x, a))
| B2 (a, b1) -> Ending (B3 (x, a, b1))
| B3 (a, b1, c) -> Ending (B4 (x, a, b1, c))
| B4 (a, b1, c, d) -> Ending (B5 (x, a, b1, c, d))
| B5 (a, b1, c, d, e) ->
  ChainCons ((PNode ((B3 (x, a, b1)), Hole, (B3 (c, d, e)))), (Ending B0))

(** val buffer_inject_chain : 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t -> 'a1 chain **)

let buffer_inject_chain b x =
  match b with
  | B0 -> Ending (B1 x)
  | B1 a -> Ending (B2 (a, x))
  | B2 (a, b1) -> Ending (B3 (a, b1, x))
  | B3 (a, b1, c) -> Ending (B4 (a, b1, c, x))
  | B4 (a, b1, c, d) -> Ending (B5 (a, b1, c, d, x))
  | B5 (a, b1, c, d, e) ->
    ChainCons ((PNode ((B3 (a, b1, c)), Hole, (B3 (d, e, x)))), (Ending B0))

(** val pair_one : ('a1 Coq_E.t * 'a1 Coq_E.t) -> 'a1 Coq_E.t option **)

let pair_one = function
| (x, y) ->
  if (=) (Coq_E.level x) (Coq_E.level y) then Some (Coq_E.pair x y) else None

(** val pair_each_buf :
    ('a1 Coq_E.t * 'a1 Coq_E.t) buf5 -> 'a1 Coq_E.t buf5 option **)

let pair_each_buf = function
| B0 -> Some B0
| B1 p -> (match pair_one p with
           | Some xp -> Some (B1 xp)
           | None -> None)
| B2 (p1, p2) ->
  (match pair_one p1 with
   | Some x1 ->
     (match pair_one p2 with
      | Some x2 -> Some (B2 (x1, x2))
      | None -> None)
   | None -> None)
| B3 (p1, p2, p3) ->
  (match pair_one p1 with
   | Some x1 ->
     (match pair_one p2 with
      | Some x2 ->
        (match pair_one p3 with
         | Some x3 -> Some (B3 (x1, x2, x3))
         | None -> None)
      | None -> None)
   | None -> None)
| B4 (p1, p2, p3, p4) ->
  (match pair_one p1 with
   | Some x1 ->
     (match pair_one p2 with
      | Some x2 ->
        (match pair_one p3 with
         | Some x3 ->
           (match pair_one p4 with
            | Some x4 -> Some (B4 (x1, x2, x3, x4))
            | None -> None)
         | None -> None)
      | None -> None)
   | None -> None)
| B5 (p1, p2, p3, p4, p5) ->
  (match pair_one p1 with
   | Some x1 ->
     (match pair_one p2 with
      | Some x2 ->
        (match pair_one p3 with
         | Some x3 ->
           (match pair_one p4 with
            | Some x4 ->
              (match pair_one p5 with
               | Some x5 -> Some (B5 (x1, x2, x3, x4, x5))
               | None -> None)
            | None -> None)
         | None -> None)
      | None -> None)
   | None -> None)

(** val mk_ending_from_options :
    'a1 Coq_E.t option -> ('a1 Coq_E.t * 'a1 Coq_E.t) option -> 'a1 Coq_E.t
    option -> 'a1 chain **)

let mk_ending_from_options p1 mid s1 =
  match p1 with
  | Some a ->
    (match mid with
     | Some p ->
       let (b, c) = p in
       (match s1 with
        | Some d -> Ending (B4 (a, b, c, d))
        | None -> Ending (B3 (a, b, c)))
     | None ->
       (match s1 with
        | Some b -> Ending (B2 (a, b))
        | None -> Ending (B1 a)))
  | None ->
    (match mid with
     | Some p ->
       let (a, b) = p in
       (match s1 with
        | Some c -> Ending (B3 (a, b, c))
        | None -> Ending (B2 (a, b)))
     | None -> (match s1 with
                | Some a -> Ending (B1 a)
                | None -> Ending B0))

(** val make_small :
    'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 chain
    option **)

let make_small b1 b2 b3 =
  match prefix_decompose b1 with
  | BD_pre_underflow p1opt ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       (match buffer_unsandwich b2 with
        | BS_alone midopt ->
          (match midopt with
           | Some elem ->
             (match Coq_E.unpair elem with
              | Some pair_elt ->
                Some (mk_ending_from_options p1opt (Some pair_elt) s1opt)
              | None -> None)
           | None -> Some (mk_ending_from_options p1opt None s1opt))
        | BS_sandwich (ab, rest, cd) ->
          (match Coq_E.unpair ab with
           | Some pair_ab ->
             (match Coq_E.unpair cd with
              | Some pair_cd ->
                Some (ChainCons ((PNode ((prefix23 p1opt pair_ab), Hole,
                  (suffix23 pair_cd s1opt))), (Ending rest)))
              | None -> None)
           | None -> None))
     | BD_suf_ok s1' ->
       (match buf5_pop_naive b2 with
        | Some p ->
          let (cd, rest) = p in
          (match Coq_E.unpair cd with
           | Some pair_cd ->
             Some (ChainCons ((PNode ((prefix23 p1opt pair_cd), Hole, s1')),
               (Ending rest)))
           | None -> None)
        | None ->
          (match p1opt with
           | Some x ->
             (match buf5_push_naive x s1' with
              | Some s1'' -> Some (Ending s1'')
              | None -> None)
           | None -> Some (Ending s1')))
     | BD_suf_overflow (s1', a, b) ->
       if (=) (Coq_E.level a) (Coq_E.level b)
       then let ab_paired = Coq_E.pair a b in
            let (cd_paired, center) = suffix_rot b2 ab_paired in
            (match Coq_E.unpair cd_paired with
             | Some pair_cd ->
               Some (ChainCons ((PNode ((prefix23 p1opt pair_cd), Hole,
                 s1')), (Ending center)))
             | None -> None)
       else None)
  | BD_pre_ok p1' ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       (match buf5_eject_naive b2 with
        | Some p ->
          let (rest, ab) = p in
          (match Coq_E.unpair ab with
           | Some pair_ab ->
             Some (ChainCons ((PNode (p1', Hole, (suffix23 pair_ab s1opt))),
               (Ending rest)))
           | None -> None)
        | None ->
          (match s1opt with
           | Some x ->
             (match buf5_inject_naive p1' x with
              | Some p1'' -> Some (Ending p1'')
              | None -> None)
           | None -> Some (Ending p1')))
     | BD_suf_ok s1' ->
       Some (ChainCons ((PNode (p1', Hole, s1')), (Ending b2)))
     | BD_suf_overflow (s1', a, b) ->
       if (=) (Coq_E.level a) (Coq_E.level b)
       then let ab_paired = Coq_E.pair a b in
            let c2 = buffer_inject_chain b2 ab_paired in
            Some (ChainCons ((PNode (p1', Hole, s1')), c2))
       else None)
  | BD_pre_overflow (p1', c, d) ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       if (=) (Coq_E.level c) (Coq_E.level d)
       then let cd_paired = Coq_E.pair c d in
            let (center, ab_paired) = prefix_rot cd_paired b2 in
            (match Coq_E.unpair ab_paired with
             | Some pair_ab ->
               Some (ChainCons ((PNode (p1', Hole,
                 (suffix23 pair_ab s1opt))), (Ending center)))
             | None -> None)
       else None
     | BD_suf_ok s1' ->
       if (=) (Coq_E.level c) (Coq_E.level d)
       then let cd_paired = Coq_E.pair c d in
            let c2 = buffer_push_chain cd_paired b2 in
            Some (ChainCons ((PNode (p1', Hole, s1')), c2))
       else None
     | BD_suf_overflow (s1', a, b) ->
       if (=) (Coq_E.level c) (Coq_E.level d)
       then if (=) (Coq_E.level a) (Coq_E.level b)
            then let cd_paired = Coq_E.pair c d in
                 let ab_paired = Coq_E.pair a b in
                 let (midopt, rest_pairs) = buffer_halve b2 in
                 (match pair_each_buf rest_pairs with
                  | Some rest ->
                    let p2 = suffix12 cd_paired midopt in
                    Some (ChainCons ((PNode (p1', (PNode (p2, Hole, (B1
                    ab_paired))), s1')), (Ending rest)))
                  | None -> None)
            else None
       else None)

(** val green_of_red : 'a1 chain -> 'a1 chain option **)

let green_of_red = function
| Ending _ -> None
| ChainCons (p, c1) ->
  (match p with
   | Hole -> None
   | PNode (pre1, p0, suf1) ->
     (match p0 with
      | Hole ->
        (match c1 with
         | Ending b -> make_small pre1 b suf1
         | ChainCons (p1, c2) ->
           (match p1 with
            | Hole -> None
            | PNode (pre2, child, suf2) ->
              (match green_prefix_concat pre1 pre2 with
               | Some p2 ->
                 let (pre1', pre2') = p2 in
                 (match green_suffix_concat suf2 suf1 with
                  | Some p3 ->
                    let (suf2', suf1') = p3 in
                    Some (ChainCons ((PNode (pre1', (PNode (pre2', child,
                    suf2')), suf1')), c2))
                  | None -> None)
               | None -> None)))
      | PNode (pre2, child, suf2) ->
        (match prefix_concat pre1 pre2 with
         | Some p1 ->
           let (pre1', pre2') = p1 in
           (match suffix_concat suf2 suf1 with
            | Some p2 ->
              let (suf2', suf1') = p2 in
              Some (ChainCons ((PNode (pre1', Hole, suf1')), (ChainCons
              ((PNode (pre2', child, suf2')), c1))))
            | None -> None)
         | None -> None)))

(** val pkt_outer_color : 'a1 packet -> color **)

let pkt_outer_color = function
| Hole -> Green
| PNode (pre, _, suf) -> color_meet (buf_color pre) (buf_color suf)

(** val ensure_green : 'a1 chain -> 'a1 chain option **)

let ensure_green c = match c with
| Ending _ -> Some c
| ChainCons (p, _) ->
  (match pkt_outer_color p with
   | Red -> green_of_red c
   | _ -> Some c)

(** val make_yellow :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
    chain option **)

let make_yellow pre i suf c =
  match ensure_green c with
  | Some c' -> Some (ChainCons ((PNode (pre, i, suf)), c'))
  | None -> None

(** val make_red :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
    chain option **)

let make_red pre i suf c =
  green_of_red (ChainCons ((PNode (pre, i, suf)), c))

(** val push_kt : 'a1 Coq_E.t -> 'a1 chain -> 'a1 chain option **)

let push_kt x = function
| Ending b ->
  (match buf5_push_naive x b with
   | Some b' -> Some (Ending b')
   | None ->
     (match b with
      | B5 (a1, b1, c1, d1, e1) ->
        Some (ChainCons ((PNode ((B3 (x, a1, b1)), Hole, (B3 (c1, d1, e1)))),
          (Ending B0)))
      | _ -> None))
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf_color pre with
      | Green ->
        (match green_push x pre with
         | Some pre' -> make_yellow pre' i suf c'
         | None -> None)
      | Yellow ->
        (match yellow_push x pre with
         | Some pre' -> make_red pre' i suf c'
         | None -> None)
      | Red -> None))

(** val inject_kt : 'a1 chain -> 'a1 Coq_E.t -> 'a1 chain option **)

let inject_kt c x =
  match c with
  | Ending b ->
    (match buf5_inject_naive b x with
     | Some b' -> Some (Ending b')
     | None ->
       (match b with
        | B5 (a1, b1, c1, d1, e1) ->
          Some (ChainCons ((PNode ((B3 (a1, b1, c1)), Hole, (B3 (d1, e1,
            x)))), (Ending B0)))
        | _ -> None))
  | ChainCons (p, c') ->
    (match p with
     | Hole -> None
     | PNode (pre, i, suf) ->
       (match buf_color suf with
        | Green ->
          (match green_inject suf x with
           | Some suf' -> make_yellow pre i suf' c'
           | None -> None)
        | Yellow ->
          (match yellow_inject suf x with
           | Some suf' -> make_red pre i suf' c'
           | None -> None)
        | Red -> None))

(** val pop_kt : 'a1 chain -> ('a1 Coq_E.t * 'a1 chain) option **)

let pop_kt = function
| Ending b ->
  (match buf5_pop_naive b with
   | Some p -> let (x, b') = p in Some (x, (Ending b'))
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf_color pre with
      | Green ->
        (match green_pop pre with
         | Some p0 ->
           let (x, pre') = p0 in
           (match make_yellow pre' i suf c' with
            | Some c'' -> Some (x, c'')
            | None -> None)
         | None -> None)
      | Yellow ->
        (match yellow_pop pre with
         | Some p0 ->
           let (x, pre') = p0 in
           (match make_red pre' i suf c' with
            | Some c'' -> Some (x, c'')
            | None -> None)
         | None -> None)
      | Red -> None))

(** val eject_kt : 'a1 chain -> ('a1 chain * 'a1 Coq_E.t) option **)

let eject_kt = function
| Ending b ->
  (match buf5_eject_naive b with
   | Some p -> let (b', x) = p in Some ((Ending b'), x)
   | None -> None)
| ChainCons (p, c') ->
  (match p with
   | Hole -> None
   | PNode (pre, i, suf) ->
     (match buf_color suf with
      | Green ->
        (match green_eject suf with
         | Some p0 ->
           let (suf', x) = p0 in
           (match make_yellow pre i suf' c' with
            | Some c'' -> Some (c'', x)
            | None -> None)
         | None -> None)
      | Yellow ->
        (match yellow_eject suf with
         | Some p0 ->
           let (suf', x) = p0 in
           (match make_red pre i suf' c' with
            | Some c'' -> Some (c'', x)
            | None -> None)
         | None -> None)
      | Red -> None))

type 'a kChain =
| KEnding of 'a Coq_E.t buf5
| KCons of color * 'a packet * 'a kChain

(** val empty_kchain : 'a1 kChain **)

let empty_kchain =
  KEnding B0

(** val chain_to_kchain_g : 'a1 chain -> 'a1 kChain **)

let rec chain_to_kchain_g = function
| Ending b -> KEnding b
| ChainCons (p, c') -> KCons (Green, p, (chain_to_kchain_g c'))

(** val kchain_to_chain : 'a1 kChain -> 'a1 chain **)

let rec kchain_to_chain = function
| KEnding b -> Ending b
| KCons (_, p, c') -> ChainCons (p, (kchain_to_chain c'))

(** val kchain_to_list : 'a1 kChain -> 'a1 list **)

let kchain_to_list c =
  chain_to_list (kchain_to_chain c)

(** val green_of_red_k : 'a1 kChain -> 'a1 kChain option **)

let green_of_red_k = function
| KEnding _ -> None
| KCons (c0, p, c1) ->
  (match c0 with
   | Red ->
     (match p with
      | Hole -> None
      | PNode (pre1, p0, suf1) ->
        (match p0 with
         | Hole ->
           (match c1 with
            | KEnding b ->
              (match make_small pre1 b suf1 with
               | Some c'' -> Some (chain_to_kchain_g c'')
               | None -> None)
            | KCons (_, p1, c2) ->
              (match p1 with
               | Hole -> None
               | PNode (pre2, child, suf2) ->
                 (match green_prefix_concat pre1 pre2 with
                  | Some p2 ->
                    let (pre1', pre2') = p2 in
                    (match green_suffix_concat suf2 suf1 with
                     | Some p3 ->
                       let (suf2', suf1') = p3 in
                       Some (KCons (Green, (PNode (pre1', (PNode (pre2',
                       child, suf2')), suf1')), c2))
                     | None -> None)
                  | None -> None)))
         | PNode (pre2, child, suf2) ->
           (match prefix_concat pre1 pre2 with
            | Some p1 ->
              let (pre1', pre2') = p1 in
              (match suffix_concat suf2 suf1 with
               | Some p2 ->
                 let (suf2', suf1') = p2 in
                 Some (KCons (Green, (PNode (pre1', Hole, suf1')), (KCons
                 (Red, (PNode (pre2', child, suf2')), c1))))
               | None -> None)
            | None -> None)))
   | _ -> None)

(** val ensure_green_k : 'a1 kChain -> 'a1 kChain option **)

let ensure_green_k c = match c with
| KEnding _ -> Some c
| KCons (c0, _, _) -> (match c0 with
                       | Red -> green_of_red_k c
                       | _ -> Some c)

(** val make_yellow_k :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
    kChain option **)

let make_yellow_k pre i suf c =
  match ensure_green_k c with
  | Some c' -> Some (KCons (Yellow, (PNode (pre, i, suf)), c'))
  | None -> None

(** val make_red_k :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
    kChain option **)

let make_red_k pre i suf c =
  green_of_red_k (KCons (Red, (PNode (pre, i, suf)), c))

(** val push_kt2 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option **)

let push_kt2 x = function
| KEnding b ->
  (match buf5_push_naive x b with
   | Some b' -> Some (KEnding b')
   | None ->
     (match b with
      | B5 (a1, b1, c1, d1, e1) ->
        Some (KCons (Green, (PNode ((B3 (x, a1, b1)), Hole, (B3 (c1, d1,
          e1)))), (KEnding B0)))
      | _ -> None))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match green_push x pre with
         | Some pre' -> make_yellow_k pre' i suf c'
         | None -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match yellow_push x pre with
         | Some pre' -> make_red_k pre' i suf c'
         | None -> None))
   | Red -> None)

(** val inject_kt2 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option **)

let inject_kt2 c x =
  match c with
  | KEnding b ->
    (match buf5_inject_naive b x with
     | Some b' -> Some (KEnding b')
     | None ->
       (match b with
        | B5 (a1, b1, c1, d1, e1) ->
          Some (KCons (Green, (PNode ((B3 (a1, b1, c1)), Hole, (B3 (d1, e1,
            x)))), (KEnding B0)))
        | _ -> None))
  | KCons (c0, p, c') ->
    (match c0 with
     | Green ->
       (match p with
        | Hole -> None
        | PNode (pre, i, suf) ->
          (match green_inject suf x with
           | Some suf' -> make_yellow_k pre i suf' c'
           | None -> None))
     | Yellow ->
       (match p with
        | Hole -> None
        | PNode (pre, i, suf) ->
          (match yellow_inject suf x with
           | Some suf' -> make_red_k pre i suf' c'
           | None -> None))
     | Red -> None)

(** val pop_kt2 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option **)

let pop_kt2 = function
| KEnding b ->
  (match buf5_pop_naive b with
   | Some p -> let (x, b') = p in Some (x, (KEnding b'))
   | None -> None)
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match green_pop pre with
         | Some p0 ->
           let (x, pre') = p0 in
           (match make_yellow_k pre' i suf c' with
            | Some c'' -> Some (x, c'')
            | None -> None)
         | None -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match yellow_pop pre with
         | Some p0 ->
           let (x, pre') = p0 in
           (match make_red_k pre' i suf c' with
            | Some c'' -> Some (x, c'')
            | None -> None)
         | None -> None))
   | Red -> None)

(** val eject_kt2 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option **)

let eject_kt2 = function
| KEnding b ->
  (match buf5_eject_naive b with
   | Some p -> let (b', x) = p in Some ((KEnding b'), x)
   | None -> None)
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match green_eject suf with
         | Some p0 ->
           let (suf', x) = p0 in
           (match make_yellow_k pre i suf' c' with
            | Some c'' -> Some (c'', x)
            | None -> None)
         | None -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match yellow_eject suf with
         | Some p0 ->
           let (suf', x) = p0 in
           (match make_red_k pre i suf' c' with
            | Some c'' -> Some (c'', x)
            | None -> None)
         | None -> None))
   | Red -> None)

(** val yellow_wrap :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
    kChain option **)

let yellow_wrap pre i suf c = match c with
| KEnding _ -> Some (KCons (Yellow, (PNode (pre, i, suf)), c))
| KCons (c0, _, _) ->
  (match c0 with
   | Red ->
     (match green_of_red_k c with
      | Some c' -> Some (KCons (Yellow, (PNode (pre, i, suf)), c'))
      | None -> None)
   | _ -> Some (KCons (Yellow, (PNode (pre, i, suf)), c)))

(** val push_kt3 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option **)

let push_kt3 x = function
| KEnding b ->
  (match b with
   | B0 -> Some (KEnding (B1 x))
   | B1 a -> Some (KEnding (B2 (x, a)))
   | B2 (a, b1) -> Some (KEnding (B3 (x, a, b1)))
   | B3 (a, b1, c1) -> Some (KEnding (B4 (x, a, b1, c1)))
   | B4 (a, b1, c1, d) -> Some (KEnding (B5 (x, a, b1, c1, d)))
   | B5 (a, b1, c1, d, e) ->
     Some (KCons (Green, (PNode ((B3 (x, a, b1)), Hole, (B3 (c1, d, e)))),
       (KEnding B0))))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) -> yellow_wrap (B3 (x, a, b1)) i suf c'
         | B3 (a, b1, c1) -> yellow_wrap (B4 (x, a, b1, c1)) i suf c'
         | _ -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a -> Some (KCons (Yellow, (PNode ((B2 (x, a)), i, suf)), c'))
         | B2 (a, b1) ->
           Some (KCons (Yellow, (PNode ((B3 (x, a, b1)), i, suf)), c'))
         | B3 (a, b1, c1) ->
           Some (KCons (Yellow, (PNode ((B4 (x, a, b1, c1)), i, suf)), c'))
         | B4 (a, b1, c1, d) ->
           green_of_red_k (KCons (Red, (PNode ((B5 (x, a, b1, c1, d)), i,
             suf)), c'))
         | _ -> None))
   | Red -> None)

(** val inject_kt3 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option **)

let inject_kt3 c x =
  match c with
  | KEnding b ->
    (match b with
     | B0 -> Some (KEnding (B1 x))
     | B1 a -> Some (KEnding (B2 (a, x)))
     | B2 (a, b1) -> Some (KEnding (B3 (a, b1, x)))
     | B3 (a, b1, c1) -> Some (KEnding (B4 (a, b1, c1, x)))
     | B4 (a, b1, c1, d) -> Some (KEnding (B5 (a, b1, c1, d, x)))
     | B5 (a, b1, c1, d, e) ->
       Some (KCons (Green, (PNode ((B3 (a, b1, c1)), Hole, (B3 (d, e, x)))),
         (KEnding B0))))
  | KCons (c0, p, c') ->
    (match c0 with
     | Green ->
       (match p with
        | Hole -> None
        | PNode (pre, i, suf) ->
          (match suf with
           | B2 (a, b1) -> yellow_wrap pre i (B3 (a, b1, x)) c'
           | B3 (a, b1, c1) -> yellow_wrap pre i (B4 (a, b1, c1, x)) c'
           | _ -> None))
     | Yellow ->
       (match p with
        | Hole -> None
        | PNode (pre, i, suf) ->
          (match suf with
           | B1 a -> Some (KCons (Yellow, (PNode (pre, i, (B2 (a, x)))), c'))
           | B2 (a, b1) ->
             Some (KCons (Yellow, (PNode (pre, i, (B3 (a, b1, x)))), c'))
           | B3 (a, b1, c1) ->
             Some (KCons (Yellow, (PNode (pre, i, (B4 (a, b1, c1, x)))), c'))
           | B4 (a, b1, c1, d) ->
             green_of_red_k (KCons (Red, (PNode (pre, i, (B5 (a, b1, c1, d,
               x)))), c'))
           | _ -> None))
     | Red -> None)

(** val pop_kt3 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option **)

let pop_kt3 = function
| KEnding b ->
  (match b with
   | B0 -> None
   | B1 a -> Some (a, (KEnding B0))
   | B2 (a, b1) -> Some (a, (KEnding (B1 b1)))
   | B3 (a, b1, c1) -> Some (a, (KEnding (B2 (b1, c1))))
   | B4 (a, b1, c1, d) -> Some (a, (KEnding (B3 (b1, c1, d))))
   | B5 (a, b1, c1, d, e) -> Some (a, (KEnding (B4 (b1, c1, d, e)))))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           (match yellow_wrap (B1 b1) i suf c' with
            | Some c'' -> Some (a, c'')
            | None -> None)
         | B3 (a, b1, c1) ->
           (match yellow_wrap (B2 (b1, c1)) i suf c' with
            | Some c'' -> Some (a, c'')
            | None -> None)
         | _ -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (B0, i, suf)), c')) with
            | Some c'' -> Some (a, c'')
            | None -> None)
         | B2 (a, b1) ->
           Some (a, (KCons (Yellow, (PNode ((B1 b1), i, suf)), c')))
         | B3 (a, b1, c1) ->
           Some (a, (KCons (Yellow, (PNode ((B2 (b1, c1)), i, suf)), c')))
         | B4 (a, b1, c1, d) ->
           Some (a, (KCons (Yellow, (PNode ((B3 (b1, c1, d)), i, suf)), c')))
         | _ -> None))
   | Red -> None)

(** val eject_kt3 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option **)

let eject_kt3 = function
| KEnding b ->
  (match b with
   | B0 -> None
   | B1 a -> Some ((KEnding B0), a)
   | B2 (a, b1) -> Some ((KEnding (B1 a)), b1)
   | B3 (a, b1, c1) -> Some ((KEnding (B2 (a, b1))), c1)
   | B4 (a, b1, c1, d) -> Some ((KEnding (B3 (a, b1, c1))), d)
   | B5 (a, b1, c1, d, e) -> Some ((KEnding (B4 (a, b1, c1, d))), e))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match suf with
         | B2 (a, b1) ->
           (match yellow_wrap pre i (B1 a) c' with
            | Some c'' -> Some (c'', b1)
            | None -> None)
         | B3 (a, b1, c1) ->
           (match yellow_wrap pre i (B2 (a, b1)) c' with
            | Some c'' -> Some (c'', c1)
            | None -> None)
         | _ -> None))
   | Yellow ->
     (match p with
      | Hole -> None
      | PNode (pre, i, suf) ->
        (match suf with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (pre, i, B0)), c')) with
            | Some c'' -> Some (c'', a)
            | None -> None)
         | B2 (a, b1) ->
           Some ((KCons (Yellow, (PNode (pre, i, (B1 a))), c')), b1)
         | B3 (a, b1, c1) ->
           Some ((KCons (Yellow, (PNode (pre, i, (B2 (a, b1)))), c')), c1)
         | B4 (a, b1, c1, d) ->
           Some ((KCons (Yellow, (PNode (pre, i, (B3 (a, b1, c1)))), c')), d)
         | _ -> None))
   | Red -> None)

type 'a push_result =
| PushFail
| PushOk of 'a kChain

type 'a pop_result =
| PopFail
| PopOk of 'a Coq_E.t * 'a kChain

(** val yellow_wrap_pr :
    'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
    push_result **)

let yellow_wrap_pr pre i suf c = match c with
| KEnding _ -> PushOk (KCons (Yellow, (PNode (pre, i, suf)), c))
| KCons (c0, _, _) ->
  (match c0 with
   | Red ->
     (match green_of_red_k c with
      | Some c' -> PushOk (KCons (Yellow, (PNode (pre, i, suf)), c'))
      | None -> PushFail)
   | _ -> PushOk (KCons (Yellow, (PNode (pre, i, suf)), c)))

(** val push_kt4 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 push_result **)

let push_kt4 x = function
| KEnding b ->
  (match b with
   | B0 -> PushOk (KEnding (B1 x))
   | B1 a -> PushOk (KEnding (B2 (x, a)))
   | B2 (a, b1) -> PushOk (KEnding (B3 (x, a, b1)))
   | B3 (a, b1, c1) -> PushOk (KEnding (B4 (x, a, b1, c1)))
   | B4 (a, b1, c1, d) -> PushOk (KEnding (B5 (x, a, b1, c1, d)))
   | B5 (a, b1, c1, d, e) ->
     PushOk (KCons (Green, (PNode ((B3 (x, a, b1)), Hole, (B3 (c1, d, e)))),
       (KEnding B0))))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> PushFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) -> yellow_wrap_pr (B3 (x, a, b1)) i suf c'
         | B3 (a, b1, c1) -> yellow_wrap_pr (B4 (x, a, b1, c1)) i suf c'
         | _ -> PushFail))
   | Yellow ->
     (match p with
      | Hole -> PushFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a -> PushOk (KCons (Yellow, (PNode ((B2 (x, a)), i, suf)), c'))
         | B2 (a, b1) ->
           PushOk (KCons (Yellow, (PNode ((B3 (x, a, b1)), i, suf)), c'))
         | B3 (a, b1, c1) ->
           PushOk (KCons (Yellow, (PNode ((B4 (x, a, b1, c1)), i, suf)), c'))
         | B4 (a, b1, c1, d) ->
           (match green_of_red_k (KCons (Red, (PNode ((B5 (x, a, b1, c1, d)),
                    i, suf)), c')) with
            | Some c'' -> PushOk c''
            | None -> PushFail)
         | _ -> PushFail))
   | Red -> PushFail)

(** val inject_kt4 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 push_result **)

let inject_kt4 c x =
  match c with
  | KEnding b ->
    (match b with
     | B0 -> PushOk (KEnding (B1 x))
     | B1 a -> PushOk (KEnding (B2 (a, x)))
     | B2 (a, b1) -> PushOk (KEnding (B3 (a, b1, x)))
     | B3 (a, b1, c1) -> PushOk (KEnding (B4 (a, b1, c1, x)))
     | B4 (a, b1, c1, d) -> PushOk (KEnding (B5 (a, b1, c1, d, x)))
     | B5 (a, b1, c1, d, e) ->
       PushOk (KCons (Green, (PNode ((B3 (a, b1, c1)), Hole, (B3 (d, e,
         x)))), (KEnding B0))))
  | KCons (c0, p, c') ->
    (match c0 with
     | Green ->
       (match p with
        | Hole -> PushFail
        | PNode (pre, i, suf) ->
          (match suf with
           | B2 (a, b1) -> yellow_wrap_pr pre i (B3 (a, b1, x)) c'
           | B3 (a, b1, c1) -> yellow_wrap_pr pre i (B4 (a, b1, c1, x)) c'
           | _ -> PushFail))
     | Yellow ->
       (match p with
        | Hole -> PushFail
        | PNode (pre, i, suf) ->
          (match suf with
           | B1 a ->
             PushOk (KCons (Yellow, (PNode (pre, i, (B2 (a, x)))), c'))
           | B2 (a, b1) ->
             PushOk (KCons (Yellow, (PNode (pre, i, (B3 (a, b1, x)))), c'))
           | B3 (a, b1, c1) ->
             PushOk (KCons (Yellow, (PNode (pre, i, (B4 (a, b1, c1, x)))),
               c'))
           | B4 (a, b1, c1, d) ->
             (match green_of_red_k (KCons (Red, (PNode (pre, i, (B5 (a, b1,
                      c1, d, x)))), c')) with
              | Some c'' -> PushOk c''
              | None -> PushFail)
           | _ -> PushFail))
     | Red -> PushFail)

(** val pop_kt4 : 'a1 kChain -> 'a1 pop_result **)

let pop_kt4 = function
| KEnding b ->
  (match b with
   | B0 -> PopFail
   | B1 a -> PopOk (a, (KEnding B0))
   | B2 (a, b1) -> PopOk (a, (KEnding (B1 b1)))
   | B3 (a, b1, c1) -> PopOk (a, (KEnding (B2 (b1, c1))))
   | B4 (a, b1, c1, d) -> PopOk (a, (KEnding (B3 (b1, c1, d))))
   | B5 (a, b1, c1, d, e) -> PopOk (a, (KEnding (B4 (b1, c1, d, e)))))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> PopFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           (match yellow_wrap_pr (B1 b1) i suf c' with
            | PushFail -> PopFail
            | PushOk c'' -> PopOk (a, c''))
         | B3 (a, b1, c1) ->
           (match yellow_wrap_pr (B2 (b1, c1)) i suf c' with
            | PushFail -> PopFail
            | PushOk c'' -> PopOk (a, c''))
         | _ -> PopFail))
   | Yellow ->
     (match p with
      | Hole -> PopFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (B0, i, suf)), c')) with
            | Some c'' -> PopOk (a, c'')
            | None -> PopFail)
         | B2 (a, b1) ->
           PopOk (a, (KCons (Yellow, (PNode ((B1 b1), i, suf)), c')))
         | B3 (a, b1, c1) ->
           PopOk (a, (KCons (Yellow, (PNode ((B2 (b1, c1)), i, suf)), c')))
         | B4 (a, b1, c1, d) ->
           PopOk (a, (KCons (Yellow, (PNode ((B3 (b1, c1, d)), i, suf)), c')))
         | _ -> PopFail))
   | Red -> PopFail)

(** val eject_kt4 : 'a1 kChain -> 'a1 pop_result **)

let eject_kt4 = function
| KEnding b ->
  (match b with
   | B0 -> PopFail
   | B1 a -> PopOk (a, (KEnding B0))
   | B2 (a, b1) -> PopOk (b1, (KEnding (B1 a)))
   | B3 (a, b1, c1) -> PopOk (c1, (KEnding (B2 (a, b1))))
   | B4 (a, b1, c1, d) -> PopOk (d, (KEnding (B3 (a, b1, c1))))
   | B5 (a, b1, c1, d, e) -> PopOk (e, (KEnding (B4 (a, b1, c1, d)))))
| KCons (c0, p, c') ->
  (match c0 with
   | Green ->
     (match p with
      | Hole -> PopFail
      | PNode (pre, i, suf) ->
        (match suf with
         | B2 (a, b1) ->
           (match yellow_wrap_pr pre i (B1 a) c' with
            | PushFail -> PopFail
            | PushOk c'' -> PopOk (b1, c''))
         | B3 (a, b1, c1) ->
           (match yellow_wrap_pr pre i (B2 (a, b1)) c' with
            | PushFail -> PopFail
            | PushOk c'' -> PopOk (c1, c''))
         | _ -> PopFail))
   | Yellow ->
     (match p with
      | Hole -> PopFail
      | PNode (pre, i, suf) ->
        (match suf with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (pre, i, B0)), c')) with
            | Some c'' -> PopOk (a, c'')
            | None -> PopFail)
         | B2 (a, b1) ->
           PopOk (b1, (KCons (Yellow, (PNode (pre, i, (B1 a))), c')))
         | B3 (a, b1, c1) ->
           PopOk (c1, (KCons (Yellow, (PNode (pre, i, (B2 (a, b1)))), c')))
         | B4 (a, b1, c1, d) ->
           PopOk (d, (KCons (Yellow, (PNode (pre, i, (B3 (a, b1, c1)))), c')))
         | _ -> PopFail))
   | Red -> PopFail)
