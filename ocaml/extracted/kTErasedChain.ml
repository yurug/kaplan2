
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n
 end

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

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

type 'x gPacket =
| GHole
| GPNode of 'x buf5 * 'x gPacket * 'x buf5

type 'x gChain =
| GEnding of 'x buf5
| GChainCons of 'x gPacket * 'x gChain

type 'x gKChain =
| GKEnding of 'x buf5
| GKCons of color * 'x gPacket * 'x gKChain

type 'x gSChain =
| GSEnding of int * 'x buf5
| GSCons of int * color * 'x gPacket * 'x gKChain

type 'x gpop_result =
| GPopFail
| GPopOk of 'x * 'x gSChain

(** val buf5_map : ('a1 -> 'a2) -> 'a1 buf5 -> 'a2 buf5 **)

let buf5_map f = function
| B0 -> B0
| B1 a -> B1 (f a)
| B2 (a, b1) -> B2 ((f a), (f b1))
| B3 (a, b1, c) -> B3 ((f a), (f b1), (f c))
| B4 (a, b1, c, d) -> B4 ((f a), (f b1), (f c), (f d))
| B5 (a, b1, c, d, e) -> B5 ((f a), (f b1), (f c), (f d), (f e))

(** val green_prefix_concat_e :
    'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
    option **)

let green_prefix_concat_e b1 b2 =
  match prefix_decompose b1 with
  | BD_pre_underflow opt ->
    (match green_pop b2 with
     | Some p ->
       let (e, b2') = p in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun a b -> Some ((prefix23 opt (a, b)), b2'))
          e)
     | None -> None)
  | BD_pre_ok b1' -> Some (b1', b2)
  | BD_pre_overflow (b1', c, d) ->
    (match green_push (Eraw.pair (c, d)) b2 with
     | Some b2' -> Some (b1', b2')
     | None -> None)

(** val green_suffix_concat_e :
    'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
    option **)

let green_suffix_concat_e b1 b2 =
  match suffix_decompose b2 with
  | BD_suf_underflow opt ->
    (match green_eject b1 with
     | Some p ->
       let (b1', e) = p in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun a b -> Some (b1', (suffix23 (a, b) opt)))
          e)
     | None -> None)
  | BD_suf_ok b2' -> Some (b1, b2')
  | BD_suf_overflow (b2', a, b) ->
    (match green_inject b1 (Eraw.pair (a, b)) with
     | Some b1' -> Some (b1', b2')
     | None -> None)

(** val prefix_concat_e :
    'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
    option **)

let prefix_concat_e b1 b2 =
  match prefix_decompose b1 with
  | BD_pre_underflow opt ->
    (match yellow_pop b2 with
     | Some p ->
       let (e, b2') = p in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun a b -> Some ((prefix23 opt (a, b)), b2'))
          e)
     | None -> None)
  | BD_pre_ok b1' -> Some (b1', b2)
  | BD_pre_overflow (b1', c, d) ->
    (match yellow_push (Eraw.pair (c, d)) b2 with
     | Some b2' -> Some (b1', b2')
     | None -> None)

(** val suffix_concat_e :
    'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
    option **)

let suffix_concat_e b1 b2 =
  match suffix_decompose b2 with
  | BD_suf_underflow opt ->
    (match yellow_eject b1 with
     | Some p ->
       let (b1', e) = p in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun a b -> Some (b1', (suffix23 (a, b) opt)))
          e)
     | None -> None)
  | BD_suf_ok b2' -> Some (b1, b2')
  | BD_suf_overflow (b2', a, b) ->
    (match yellow_inject b1 (Eraw.pair (a, b)) with
     | Some b1' -> Some (b1', b2')
     | None -> None)

(** val gpair_one : ('a1 Eraw.t * 'a1 Eraw.t) -> 'a1 Eraw.t **)

let gpair_one p =
  Eraw.pair ((fst p), (snd p))

(** val gpair_each : ('a1 Eraw.t * 'a1 Eraw.t) buf5 -> 'a1 Eraw.t buf5 **)

let gpair_each b =
  buf5_map gpair_one b

(** val gbuffer_push_chain : 'a1 -> 'a1 buf5 -> 'a1 gChain **)

let gbuffer_push_chain x = function
| B0 -> GEnding (B1 x)
| B1 a -> GEnding (B2 (x, a))
| B2 (a, b1) -> GEnding (B3 (x, a, b1))
| B3 (a, b1, c) -> GEnding (B4 (x, a, b1, c))
| B4 (a, b1, c, d) -> GEnding (B5 (x, a, b1, c, d))
| B5 (a, b1, c, d, e) ->
  GChainCons ((GPNode ((B3 (x, a, b1)), GHole, (B3 (c, d, e)))), (GEnding B0))

(** val gbuffer_inject_chain : 'a1 buf5 -> 'a1 -> 'a1 gChain **)

let gbuffer_inject_chain b x =
  match b with
  | B0 -> GEnding (B1 x)
  | B1 a -> GEnding (B2 (a, x))
  | B2 (a, b1) -> GEnding (B3 (a, b1, x))
  | B3 (a, b1, c) -> GEnding (B4 (a, b1, c, x))
  | B4 (a, b1, c, d) -> GEnding (B5 (a, b1, c, d, x))
  | B5 (a, b1, c, d, e) ->
    GChainCons ((GPNode ((B3 (a, b1, c)), GHole, (B3 (d, e, x)))), (GEnding
      B0))

(** val gmk_ending_from_options :
    'a1 option -> ('a1 * 'a1) option -> 'a1 option -> 'a1 gChain **)

let gmk_ending_from_options p1 mid s1 =
  match p1 with
  | Some a ->
    (match mid with
     | Some p ->
       let (b, c) = p in
       (match s1 with
        | Some d -> GEnding (B4 (a, b, c, d))
        | None -> GEnding (B3 (a, b, c)))
     | None ->
       (match s1 with
        | Some b -> GEnding (B2 (a, b))
        | None -> GEnding (B1 a)))
  | None ->
    (match mid with
     | Some p ->
       let (a, b) = p in
       (match s1 with
        | Some c -> GEnding (B3 (a, b, c))
        | None -> GEnding (B2 (a, b)))
     | None -> (match s1 with
                | Some a -> GEnding (B1 a)
                | None -> GEnding B0))

(** val make_small_e :
    'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t
    gChain option **)

let make_small_e b1 b2 b3 =
  match prefix_decompose b1 with
  | BD_pre_underflow p1opt ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       (match buffer_unsandwich b2 with
        | BS_alone midopt ->
          (match midopt with
           | Some e ->
             ((fun _ fp t -> Eraw.case_pair fp t)
                (fun _ -> None)
                (fun x y -> Some
                (gmk_ending_from_options p1opt (Some (x, y)) s1opt))
                e)
           | None -> Some (gmk_ending_from_options p1opt None s1opt))
        | BS_sandwich (ab, rest, cd) ->
          ((fun _ fp t -> Eraw.case_pair fp t)
             (fun _ -> None)
             (fun ax ay ->
             (fun _ fp t -> Eraw.case_pair fp t)
               (fun _ -> None)
               (fun cx cy -> Some (GChainCons ((GPNode
               ((prefix23 p1opt (ax, ay)), GHole,
               (suffix23 (cx, cy) s1opt))), (GEnding rest))))
               cd)
             ab))
     | BD_suf_ok s1' ->
       (match buf5_pop_naive b2 with
        | Some p ->
          let (cd, rest) = p in
          ((fun _ fp t -> Eraw.case_pair fp t)
             (fun _ -> None)
             (fun cx cy -> Some (GChainCons ((GPNode
             ((prefix23 p1opt (cx, cy)), GHole, s1')), (GEnding rest))))
             cd)
        | None ->
          (match p1opt with
           | Some x ->
             (match buf5_push_naive x s1' with
              | Some s1'' -> Some (GEnding s1'')
              | None -> None)
           | None -> Some (GEnding s1')))
     | BD_suf_overflow (s1', a, b) ->
       let (cd, center) = suffix_rot b2 (Eraw.pair (a, b)) in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun cx cy -> Some (GChainCons ((GPNode ((prefix23 p1opt (cx, cy)),
          GHole, s1')), (GEnding center))))
          cd))
  | BD_pre_ok p1' ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       (match buf5_eject_naive b2 with
        | Some p ->
          let (rest, ab) = p in
          ((fun _ fp t -> Eraw.case_pair fp t)
             (fun _ -> None)
             (fun ax ay -> Some (GChainCons ((GPNode (p1', GHole,
             (suffix23 (ax, ay) s1opt))), (GEnding rest))))
             ab)
        | None ->
          (match s1opt with
           | Some x ->
             (match buf5_inject_naive p1' x with
              | Some p1'' -> Some (GEnding p1'')
              | None -> None)
           | None -> Some (GEnding p1')))
     | BD_suf_ok s1' ->
       Some (GChainCons ((GPNode (p1', GHole, s1')), (GEnding b2)))
     | BD_suf_overflow (s1', a, b) ->
       Some (GChainCons ((GPNode (p1', GHole, s1')),
         (gbuffer_inject_chain b2 (Eraw.pair (a, b))))))
  | BD_pre_overflow (p1', c, d) ->
    (match suffix_decompose b3 with
     | BD_suf_underflow s1opt ->
       let (center, ab) = prefix_rot (Eraw.pair (c, d)) b2 in
       ((fun _ fp t -> Eraw.case_pair fp t)
          (fun _ -> None)
          (fun ax ay -> Some (GChainCons ((GPNode (p1', GHole,
          (suffix23 (ax, ay) s1opt))), (GEnding center))))
          ab)
     | BD_suf_ok s1' ->
       Some (GChainCons ((GPNode (p1', GHole, s1')),
         (gbuffer_push_chain (Eraw.pair (c, d)) b2)))
     | BD_suf_overflow (s1', a, b) ->
       let (midopt, rest_pairs) = buffer_halve b2 in
       Some (GChainCons ((GPNode (p1', (GPNode
       ((suffix12 (Eraw.pair (c, d)) midopt), GHole, (B1 (Eraw.pair (a,
       b))))), s1')), (GEnding (gpair_each rest_pairs)))))

(** val gchain_to_gkchain_g : 'a1 gChain -> 'a1 gKChain **)

let rec gchain_to_gkchain_g = function
| GEnding b -> GKEnding b
| GChainCons (p, c') -> GKCons (Green, p, (gchain_to_gkchain_g c'))

(** val green_of_red_k_e : 'a1 Eraw.t gKChain -> 'a1 Eraw.t gKChain option **)

let green_of_red_k_e = function
| GKEnding _ -> None
| GKCons (c0, g, c1) ->
  (match c0 with
   | Red ->
     (match g with
      | GHole -> None
      | GPNode (pre1, g0, suf1) ->
        (match g0 with
         | GHole ->
           (match c1 with
            | GKEnding b ->
              (match make_small_e pre1 b suf1 with
               | Some c'' -> Some (gchain_to_gkchain_g c'')
               | None -> None)
            | GKCons (_, g1, c2) ->
              (match g1 with
               | GHole -> None
               | GPNode (pre2, child, suf2) ->
                 (match green_prefix_concat_e pre1 pre2 with
                  | Some p ->
                    let (pre1', pre2') = p in
                    (match green_suffix_concat_e suf2 suf1 with
                     | Some p0 ->
                       let (suf2', suf1') = p0 in
                       Some (GKCons (Green, (GPNode (pre1', (GPNode (pre2',
                       child, suf2')), suf1')), c2))
                     | None -> None)
                  | None -> None)))
         | GPNode (pre2, child, suf2) ->
           (match prefix_concat_e pre1 pre2 with
            | Some p ->
              let (pre1', pre2') = p in
              (match suffix_concat_e suf2 suf1 with
               | Some p0 ->
                 let (suf2', suf1') = p0 in
                 Some (GKCons (Green, (GPNode (pre1', GHole, suf1')), (GKCons
                 (Red, (GPNode (pre2', child, suf2')), c1))))
               | None -> None)
            | None -> None)))
   | _ -> None)

(** val gs_of : int -> 'a1 gKChain -> 'a1 gSChain **)

let gs_of n = function
| GKEnding b -> GSEnding (n, b)
| GKCons (col, p, t) -> GSCons (n, col, p, t)

(** val eyellow_wrap :
    'a1 Eraw.t gSChain -> int -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t gPacket -> 'a1
    Eraw.t buf5 -> 'a1 Eraw.t gKChain -> 'a1 Eraw.t gSChain **)

let eyellow_wrap fb n' pre i suf t = match t with
| GKEnding _ -> GSCons (n', Yellow, (GPNode (pre, i, suf)), t)
| GKCons (c, _, _) ->
  (match c with
   | Red ->
     (match green_of_red_k_e t with
      | Some t' -> GSCons (n', Yellow, (GPNode (pre, i, suf)), t')
      | None -> fb)
   | _ -> GSCons (n', Yellow, (GPNode (pre, i, suf)), t))

(** val epush_s : 'a1 Eraw.t -> 'a1 Eraw.t gSChain -> 'a1 Eraw.t gSChain **)

let epush_s x c = match c with
| GSEnding (n, b) ->
  (match b with
   | B0 -> GSEnding ((Stdlib.Int.succ n), (B1 x))
   | B1 a -> GSEnding ((Stdlib.Int.succ n), (B2 (x, a)))
   | B2 (a, b1) -> GSEnding ((Stdlib.Int.succ n), (B3 (x, a, b1)))
   | B3 (a, b1, c1) -> GSEnding ((Stdlib.Int.succ n), (B4 (x, a, b1, c1)))
   | B4 (a, b1, c1, d) ->
     GSEnding ((Stdlib.Int.succ n), (B5 (x, a, b1, c1, d)))
   | B5 (a, b1, c1, d, e) ->
     GSCons ((Stdlib.Int.succ n), Green, (GPNode ((B3 (x, a, b1)), GHole, (B3
       (c1, d, e)))), (GKEnding B0)))
| GSCons (n, col, p, t) ->
  (match col with
   | Green ->
     (match p with
      | GHole -> c
      | GPNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           eyellow_wrap c (Stdlib.Int.succ n) (B3 (x, a, b1)) i suf t
         | B3 (a, b1, c1) ->
           eyellow_wrap c (Stdlib.Int.succ n) (B4 (x, a, b1, c1)) i suf t
         | _ -> c))
   | Yellow ->
     (match p with
      | GHole -> c
      | GPNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           GSCons ((Stdlib.Int.succ n), Yellow, (GPNode ((B2 (x, a)), i,
             suf)), t)
         | B2 (a, b1) ->
           GSCons ((Stdlib.Int.succ n), Yellow, (GPNode ((B3 (x, a, b1)), i,
             suf)), t)
         | B3 (a, b1, c1) ->
           GSCons ((Stdlib.Int.succ n), Yellow, (GPNode ((B4 (x, a, b1, c1)),
             i, suf)), t)
         | B4 (a, b1, c1, d) ->
           (match green_of_red_k_e (GKCons (Red, (GPNode ((B5 (x, a, b1, c1,
                    d)), i, suf)), t)) with
            | Some d' -> gs_of (Stdlib.Int.succ n) d'
            | None -> c)
         | _ -> c))
   | Red -> c)

(** val einject_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t -> 'a1 Eraw.t gSChain **)

let einject_s c x =
  match c with
  | GSEnding (n, b) ->
    (match b with
     | B0 -> GSEnding ((Stdlib.Int.succ n), (B1 x))
     | B1 a -> GSEnding ((Stdlib.Int.succ n), (B2 (a, x)))
     | B2 (a, b1) -> GSEnding ((Stdlib.Int.succ n), (B3 (a, b1, x)))
     | B3 (a, b1, c1) -> GSEnding ((Stdlib.Int.succ n), (B4 (a, b1, c1, x)))
     | B4 (a, b1, c1, d) ->
       GSEnding ((Stdlib.Int.succ n), (B5 (a, b1, c1, d, x)))
     | B5 (a, b1, c1, d, e) ->
       GSCons ((Stdlib.Int.succ n), Green, (GPNode ((B3 (a, b1, c1)), GHole,
         (B3 (d, e, x)))), (GKEnding B0)))
  | GSCons (n, col, p, t) ->
    (match col with
     | Green ->
       (match p with
        | GHole -> c
        | GPNode (pre, i, suf) ->
          (match suf with
           | B2 (a, b1) ->
             eyellow_wrap c (Stdlib.Int.succ n) pre i (B3 (a, b1, x)) t
           | B3 (a, b1, c1) ->
             eyellow_wrap c (Stdlib.Int.succ n) pre i (B4 (a, b1, c1, x)) t
           | _ -> c))
     | Yellow ->
       (match p with
        | GHole -> c
        | GPNode (pre, i, suf) ->
          (match suf with
           | B1 a ->
             GSCons ((Stdlib.Int.succ n), Yellow, (GPNode (pre, i, (B2 (a,
               x)))), t)
           | B2 (a, b1) ->
             GSCons ((Stdlib.Int.succ n), Yellow, (GPNode (pre, i, (B3 (a,
               b1, x)))), t)
           | B3 (a, b1, c1) ->
             GSCons ((Stdlib.Int.succ n), Yellow, (GPNode (pre, i, (B4 (a,
               b1, c1, x)))), t)
           | B4 (a, b1, c1, d) ->
             (match green_of_red_k_e (GKCons (Red, (GPNode (pre, i, (B5 (a,
                      b1, c1, d, x)))), t)) with
              | Some d' -> gs_of (Stdlib.Int.succ n) d'
              | None -> c)
           | _ -> c))
     | Red -> c)

(** val epop_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t gpop_result **)

let epop_s = function
| GSEnding (n, b) ->
  (match b with
   | B0 -> GPopFail
   | B1 a -> GPopOk (a, (GSEnding ((Nat.pred n), B0)))
   | B2 (a, b1) -> GPopOk (a, (GSEnding ((Nat.pred n), (B1 b1))))
   | B3 (a, b1, c1) -> GPopOk (a, (GSEnding ((Nat.pred n), (B2 (b1, c1)))))
   | B4 (a, b1, c1, d) ->
     GPopOk (a, (GSEnding ((Nat.pred n), (B3 (b1, c1, d)))))
   | B5 (a, b1, c1, d, e) ->
     GPopOk (a, (GSEnding ((Nat.pred n), (B4 (b1, c1, d, e))))))
| GSCons (n, col, p, t) ->
  (match col with
   | Green ->
     (match p with
      | GHole -> GPopFail
      | GPNode (pre, i, suf) ->
        (match pre with
         | B2 (a, b1) ->
           (match t with
            | GKEnding _ ->
              GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B1 b1), i,
                suf)), t)))
            | GKCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k_e t with
                  | Some t' ->
                    GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B1
                      b1), i, suf)), t')))
                  | None -> GPopFail)
               | _ ->
                 GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B1 b1),
                   i, suf)), t)))))
         | B3 (a, b1, c1) ->
           (match t with
            | GKEnding _ ->
              GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B2 (b1,
                c1)), i, suf)), t)))
            | GKCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k_e t with
                  | Some t' ->
                    GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B2
                      (b1, c1)), i, suf)), t')))
                  | None -> GPopFail)
               | _ ->
                 GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B2 (b1,
                   c1)), i, suf)), t)))))
         | _ -> GPopFail))
   | Yellow ->
     (match p with
      | GHole -> GPopFail
      | GPNode (pre, i, suf) ->
        (match pre with
         | B1 a ->
           (match green_of_red_k_e (GKCons (Red, (GPNode (B0, i, suf)), t)) with
            | Some d' -> GPopOk (a, (gs_of (Nat.pred n) d'))
            | None -> GPopFail)
         | B2 (a, b1) ->
           GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B1 b1), i,
             suf)), t)))
         | B3 (a, b1, c1) ->
           GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B2 (b1, c1)),
             i, suf)), t)))
         | B4 (a, b1, c1, d) ->
           GPopOk (a, (GSCons ((Nat.pred n), Yellow, (GPNode ((B3 (b1, c1,
             d)), i, suf)), t)))
         | _ -> GPopFail))
   | Red -> GPopFail)

(** val eeject_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t gpop_result **)

let eeject_s = function
| GSEnding (n, b) ->
  (match b with
   | B0 -> GPopFail
   | B1 a -> GPopOk (a, (GSEnding ((Nat.pred n), B0)))
   | B2 (a, b1) -> GPopOk (b1, (GSEnding ((Nat.pred n), (B1 a))))
   | B3 (a, b1, c1) -> GPopOk (c1, (GSEnding ((Nat.pred n), (B2 (a, b1)))))
   | B4 (a, b1, c1, d) ->
     GPopOk (d, (GSEnding ((Nat.pred n), (B3 (a, b1, c1)))))
   | B5 (a, b1, c1, d, e) ->
     GPopOk (e, (GSEnding ((Nat.pred n), (B4 (a, b1, c1, d))))))
| GSCons (n, col, p, t) ->
  (match col with
   | Green ->
     (match p with
      | GHole -> GPopFail
      | GPNode (pre, i, suf) ->
        (match suf with
         | B2 (a, b1) ->
           (match t with
            | GKEnding _ ->
              GPopOk (b1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i, (B1
                a))), t)))
            | GKCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k_e t with
                  | Some t' ->
                    GPopOk (b1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre,
                      i, (B1 a))), t')))
                  | None -> GPopFail)
               | _ ->
                 GPopOk (b1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i,
                   (B1 a))), t)))))
         | B3 (a, b1, c1) ->
           (match t with
            | GKEnding _ ->
              GPopOk (c1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i, (B2
                (a, b1)))), t)))
            | GKCons (c0, _, _) ->
              (match c0 with
               | Red ->
                 (match green_of_red_k_e t with
                  | Some t' ->
                    GPopOk (c1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre,
                      i, (B2 (a, b1)))), t')))
                  | None -> GPopFail)
               | _ ->
                 GPopOk (c1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i,
                   (B2 (a, b1)))), t)))))
         | _ -> GPopFail))
   | Yellow ->
     (match p with
      | GHole -> GPopFail
      | GPNode (pre, i, suf) ->
        (match suf with
         | B1 a ->
           (match green_of_red_k_e (GKCons (Red, (GPNode (pre, i, B0)), t)) with
            | Some d' -> GPopOk (a, (gs_of (Nat.pred n) d'))
            | None -> GPopFail)
         | B2 (a, b1) ->
           GPopOk (b1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i, (B1
             a))), t)))
         | B3 (a, b1, c1) ->
           GPopOk (c1, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i, (B2
             (a, b1)))), t)))
         | B4 (a, b1, c1, d) ->
           GPopOk (d, (GSCons ((Nat.pred n), Yellow, (GPNode (pre, i, (B3 (a,
             b1, c1)))), t)))
         | _ -> GPopFail))
   | Red -> GPopFail)

(** val egs_empty : 'a1 Eraw.t gSChain **)

let egs_empty =
  GSEnding (0, B0)

(** val egs_size : 'a1 gSChain -> int **)

let egs_size = function
| GSEnding (n, _) -> n
| GSCons (n, _, _, _) -> n
