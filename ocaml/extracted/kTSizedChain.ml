
type __ = Obj.t

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p



module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n
 end

type 'a xpow = __

module ElementTree =
 struct
  type 'x t = 'x Erased_tree.t

  (** val to_list : 'a1 t -> 'a1 list **)

  let to_list = Erased_tree.to_list

  (** val level : 'a1 t -> int **)

  let level = Erased_tree.level

  (** val base : 'a1 -> 'a1 t **)

  let base = Erased_tree.base

  (** val pair : 'a1 t -> 'a1 t -> 'a1 t **)

  let pair = Erased_tree.pair

  (** val unpair : 'a1 t -> ('a1 t * 'a1 t) option **)

  let unpair = Erased_tree.unpair
 end

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

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

type color =
| Green
| Yellow
| Red

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

type 'a kChain =
| KEnding of 'a Coq_E.t buf5
| KCons of color * 'a packet * 'a kChain

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

module Coq0_E = E

type 'a sChain =
| SEnding of int * 'a Coq0_E.t buf5
| SCons of int * color * 'a packet * 'a kChain

(** val s_empty : 'a1 sChain **)

let s_empty =
  SEnding (0, B0)

(** val s_size : 'a1 sChain -> int **)

let s_size = function
| SEnding (n, _) -> n
| SCons (n, _, _, _) -> n

(** val s_erase : 'a1 sChain -> 'a1 kChain **)

let s_erase = function
| SEnding (_, b) -> KEnding b
| SCons (_, col, p, t0) -> KCons (col, p, t0)

(** val s_of : int -> 'a1 kChain -> 'a1 sChain **)

let s_of n = function
| KEnding b -> SEnding (n, b)
| KCons (col, p, t0) -> SCons (n, col, p, t0)

(** val s_to_list : 'a1 sChain -> 'a1 list **)

let s_to_list c =
  kchain_to_list (s_erase c)

(** val yellow_wrap_s :
    'a1 sChain -> int -> 'a1 Coq0_E.t buf5 -> 'a1 packet -> 'a1 Coq0_E.t buf5
    -> 'a1 kChain -> 'a1 sChain **)

let yellow_wrap_s fb n' pre i suf t0 = match t0 with
| KEnding _ -> SCons (n', Yellow, (PNode (pre, i, suf)), t0)
| KCons (c, _, _) ->
  (match c with
   | Red ->
     (match green_of_red_k t0 with
      | Some t' -> SCons (n', Yellow, (PNode (pre, i, suf)), t')
      | None -> fb)
   | _ -> SCons (n', Yellow, (PNode (pre, i, suf)), t0))

(** val push_s : 'a1 Coq0_E.t -> 'a1 sChain -> 'a1 sChain **)

let push_s x c = match c with
| SEnding (n, b) ->
  (match b with
   | B0 -> SEnding ((Stdlib.Int.succ n), (B1 x))
   | B1 a -> SEnding ((Stdlib.Int.succ n), (B2 (x, a)))
   | B2 (a, b1) -> SEnding ((Stdlib.Int.succ n), (B3 (x, a, b1)))
   | B3 (a, b1, c1) -> SEnding ((Stdlib.Int.succ n), (B4 (x, a, b1, c1)))
   | B4 (a, b1, c1, d) ->
     SEnding ((Stdlib.Int.succ n), (B5 (x, a, b1, c1, d)))
   | B5 (a, b1, c1, d, e) ->
     SCons ((Stdlib.Int.succ n), Green, (PNode ((B3 (x, a, b1)), Hole, (B3
       (c1, d, e)))), (KEnding B0)))
| SCons (n, col, p, t0) ->
  (match col with
   | Green ->
     (match p with
      | Hole -> c
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           yellow_wrap_s c (Stdlib.Int.succ n) (B3 (x, a, b1)) i suf t0
         | B3 (a, b1, c1) ->
           yellow_wrap_s c (Stdlib.Int.succ n) (B4 (x, a, b1, c1)) i suf t0
         | _ -> c))
   | Yellow ->
     (match p with
      | Hole -> c
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           SCons ((Stdlib.Int.succ n), Yellow, (PNode ((B2 (x, a)), i, suf)),
             t0)
         | B2 (a, b1) ->
           SCons ((Stdlib.Int.succ n), Yellow, (PNode ((B3 (x, a, b1)), i,
             suf)), t0)
         | B3 (a, b1, c1) ->
           SCons ((Stdlib.Int.succ n), Yellow, (PNode ((B4 (x, a, b1, c1)),
             i, suf)), t0)
         | B4 (a, b1, c1, d) ->
           (match green_of_red_k (KCons (Red, (PNode ((B5 (x, a, b1, c1, d)),
                    i, suf)), t0)) with
            | Some d' -> s_of (Stdlib.Int.succ n) d'
            | None -> c)
         | _ -> c))
   | Red -> c)

(** val inject_s : 'a1 sChain -> 'a1 Coq0_E.t -> 'a1 sChain **)

let inject_s c x =
  match c with
  | SEnding (n, b) ->
    (match b with
     | B0 -> SEnding ((Stdlib.Int.succ n), (B1 x))
     | B1 a -> SEnding ((Stdlib.Int.succ n), (B2 (a, x)))
     | B2 (a, b1) -> SEnding ((Stdlib.Int.succ n), (B3 (a, b1, x)))
     | B3 (a, b1, c1) -> SEnding ((Stdlib.Int.succ n), (B4 (a, b1, c1, x)))
     | B4 (a, b1, c1, d) ->
       SEnding ((Stdlib.Int.succ n), (B5 (a, b1, c1, d, x)))
     | B5 (a, b1, c1, d, e) ->
       SCons ((Stdlib.Int.succ n), Green, (PNode ((B3 (a, b1, c1)), Hole, (B3
         (d, e, x)))), (KEnding B0)))
  | SCons (n, col, p, t0) ->
    (match col with
     | Green ->
       (match p with
        | Hole -> c
        | PNode (pre, i, suf) ->
          (match suf with
           | B2 (a, b1) ->
             yellow_wrap_s c (Stdlib.Int.succ n) pre i (B3 (a, b1, x)) t0
           | B3 (a, b1, c1) ->
             yellow_wrap_s c (Stdlib.Int.succ n) pre i (B4 (a, b1, c1, x)) t0
           | _ -> c))
     | Yellow ->
       (match p with
        | Hole -> c
        | PNode (pre, i, suf) ->
          (match suf with
           | B1 a ->
             SCons ((Stdlib.Int.succ n), Yellow, (PNode (pre, i, (B2 (a,
               x)))), t0)
           | B2 (a, b1) ->
             SCons ((Stdlib.Int.succ n), Yellow, (PNode (pre, i, (B3 (a, b1,
               x)))), t0)
           | B3 (a, b1, c1) ->
             SCons ((Stdlib.Int.succ n), Yellow, (PNode (pre, i, (B4 (a, b1,
               c1, x)))), t0)
           | B4 (a, b1, c1, d) ->
             (match green_of_red_k (KCons (Red, (PNode (pre, i, (B5 (a, b1,
                      c1, d, x)))), t0)) with
              | Some d' -> s_of (Stdlib.Int.succ n) d'
              | None -> c)
           | _ -> c))
     | Red -> c)

type 'a spop_result =
| SPopFail
| SPopOk of 'a Coq0_E.t * 'a sChain

(** val pop_s : 'a1 sChain -> 'a1 spop_result **)

let pop_s = function
| SEnding (n, b) ->
  (match b with
   | B0 -> SPopFail
   | B1 a -> SPopOk (a, (SEnding ((Nat.pred n), B0)))
   | B2 (a, b1) -> SPopOk (a, (SEnding ((Nat.pred n), (B1 b1))))
   | B3 (a, b1, c1) -> SPopOk (a, (SEnding ((Nat.pred n), (B2 (b1, c1)))))
   | B4 (a, b1, c1, d) ->
     SPopOk (a, (SEnding ((Nat.pred n), (B3 (b1, c1, d)))))
   | B5 (a, b1, c1, d, e) ->
     SPopOk (a, (SEnding ((Nat.pred n), (B4 (b1, c1, d, e))))))
| SCons (n, col, p, t0) ->
  (match col with
   | Green ->
     (match p with
      | Hole -> SPopFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           (match t0 with
            | KEnding _ ->
              SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B1 b1), i,
                suf)), t0)))
            | KCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k t0 with
                  | Some t' ->
                    SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B1 b1),
                      i, suf)), t')))
                  | None -> SPopFail)
               | _ ->
                 SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B1 b1), i,
                   suf)), t0)))))
         | B3 (a, b1, c1) ->
           (match t0 with
            | KEnding _ ->
              SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B2 (b1, c1)),
                i, suf)), t0)))
            | KCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k t0 with
                  | Some t' ->
                    SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B2 (b1,
                      c1)), i, suf)), t')))
                  | None -> SPopFail)
               | _ ->
                 SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B2 (b1,
                   c1)), i, suf)), t0)))))
         | _ -> SPopFail))
   | Yellow ->
     (match p with
      | Hole -> SPopFail
      | PNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (B0, i, suf)), t0)) with
            | Some d' -> SPopOk (a, (s_of (Nat.pred n) d'))
            | None -> SPopFail)
         | B2 (a, b1) ->
           SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B1 b1), i,
             suf)), t0)))
         | B3 (a, b1, c1) ->
           SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B2 (b1, c1)), i,
             suf)), t0)))
         | B4 (a, b1, c1, d) ->
           SPopOk (a, (SCons ((Nat.pred n), Yellow, (PNode ((B3 (b1, c1, d)),
             i, suf)), t0)))
         | _ -> SPopFail))
   | Red -> SPopFail)

(** val eject_s : 'a1 sChain -> 'a1 spop_result **)

let eject_s = function
| SEnding (n, b) ->
  (match b with
   | B0 -> SPopFail
   | B1 a -> SPopOk (a, (SEnding ((Nat.pred n), B0)))
   | B2 (a, b1) -> SPopOk (b1, (SEnding ((Nat.pred n), (B1 a))))
   | B3 (a, b1, c1) -> SPopOk (c1, (SEnding ((Nat.pred n), (B2 (a, b1)))))
   | B4 (a, b1, c1, d) ->
     SPopOk (d, (SEnding ((Nat.pred n), (B3 (a, b1, c1)))))
   | B5 (a, b1, c1, d, e) ->
     SPopOk (e, (SEnding ((Nat.pred n), (B4 (a, b1, c1, d))))))
| SCons (n, col, p, t0) ->
  (match col with
   | Green ->
     (match p with
      | Hole -> SPopFail
      | PNode (pre, i, suf) ->
        (match suf with
         | B2 (a, b1) ->
           (match t0 with
            | KEnding _ ->
              SPopOk (b1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i, (B1
                a))), t0)))
            | KCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k t0 with
                  | Some t' ->
                    SPopOk (b1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i,
                      (B1 a))), t')))
                  | None -> SPopFail)
               | _ ->
                 SPopOk (b1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i,
                   (B1 a))), t0)))))
         | B3 (a, b1, c1) ->
           (match t0 with
            | KEnding _ ->
              SPopOk (c1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i, (B2
                (a, b1)))), t0)))
            | KCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k t0 with
                  | Some t' ->
                    SPopOk (c1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i,
                      (B2 (a, b1)))), t')))
                  | None -> SPopFail)
               | _ ->
                 SPopOk (c1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i,
                   (B2 (a, b1)))), t0)))))
         | _ -> SPopFail))
   | Yellow ->
     (match p with
      | Hole -> SPopFail
      | PNode (pre, i, suf) ->
        (match suf with
         | B1 a ->
           (match green_of_red_k (KCons (Red, (PNode (pre, i, B0)), t0)) with
            | Some d' -> SPopOk (a, (s_of (Nat.pred n) d'))
            | None -> SPopFail)
         | B2 (a, b1) ->
           SPopOk (b1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i, (B1
             a))), t0)))
         | B3 (a, b1, c1) ->
           SPopOk (c1, (SCons ((Nat.pred n), Yellow, (PNode (pre, i, (B2 (a,
             b1)))), t0)))
         | B4 (a, b1, c1, d) ->
           SPopOk (d, (SCons ((Nat.pred n), Yellow, (PNode (pre, i, (B3 (a,
             b1, c1)))), t0)))
         | _ -> SPopFail))
   | Red -> SPopFail)
