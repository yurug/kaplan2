
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

  (** val min : int -> int -> int **)

  let rec min n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> Stdlib.Int.succ (min n' m'))
        m)
      n
 end

type 'x buffer = 'x Fastbuf.t

type kind =
| KOnly
| KLeft
| KRight

type 'a stored =
| SGround of 'a
| SSmall of 'a stored buffer
| SBig of 'a stored buffer * 'a cchain * 'a stored buffer
and 'a cnode =
| Node of kind * 'a stored buffer * 'a stored buffer
and 'a cbody =
| BHole
| BSingle of 'a cnode * 'a cbody
| BPairY of 'a cnode * 'a cbody * 'a cchain
| BPairO of 'a cnode * 'a cchain * 'a cbody
and 'a cpacket =
| Pkt of 'a cbody * 'a cnode
and 'a cchain =
| CEmpty
| CSingle of 'a cpacket * 'a cchain
| CPair of 'a cchain * 'a cchain

type 'a cadeque = 'a cchain

(** val cad_empty : 'a1 cadeque **)

let cad_empty =
  CEmpty

(** val bempty : 'a1 buffer **)

let bempty = Fastbuf.empty

(** val b1 : 'a1 -> 'a1 buffer **)

let b1 = Fastbuf.b1

(** val b2 : 'a1 -> 'a1 -> 'a1 buffer **)

let b2 = Fastbuf.b2

(** val b3 : 'a1 -> 'a1 -> 'a1 -> 'a1 buffer **)

let b3 = Fastbuf.b3

(** val bpush : 'a1 -> 'a1 buffer -> 'a1 buffer **)

let bpush = Fastbuf.push

(** val binject : 'a1 buffer -> 'a1 -> 'a1 buffer **)

let binject = Fastbuf.inject

(** val bpop : 'a1 buffer -> ('a1 * 'a1 buffer) option **)

let bpop = Fastbuf.pop

(** val beject : 'a1 buffer -> ('a1 buffer * 'a1) option **)

let beject = Fastbuf.eject

(** val bsize : 'a1 buffer -> int **)

let bsize = Fastbuf.size

(** val bis_empty : 'a1 buffer -> bool **)

let bis_empty = Fastbuf.is_empty

(** val bapp : 'a1 buffer -> 'a1 buffer -> 'a1 buffer **)

let bapp = Fastbuf.append

(** val bpop2 : 'a1 buffer -> (('a1 * 'a1) * 'a1 buffer) option **)

let bpop2 = Fastbuf.pop2

(** val beject2 : 'a1 buffer -> (('a1 buffer * 'a1) * 'a1) option **)

let beject2 = Fastbuf.eject2

(** val beject3 : 'a1 buffer -> ((('a1 buffer * 'a1) * 'a1) * 'a1) option **)

let beject3 = Fastbuf.eject3

(** val bfold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 buffer -> 'a2 **)

let bfold_right = Fastbuf.fold_right

(** val bfold_left : ('a2 -> 'a1 -> 'a2) -> 'a1 buffer -> 'a2 -> 'a2 **)

let bfold_left = Fastbuf.fold_left

type gyor =
| CG
| CY
| CO
| CR

(** val chain_has_node : 'a1 cchain -> bool **)

let chain_has_node = function
| CEmpty -> false
| _ -> true

(** val root_and_child :
    'a1 cpacket -> 'a1 cchain -> 'a1 cnode * 'a1 cchain **)

let root_and_child p rest =
  let Pkt (c, n) = p in
  (match c with
   | BHole -> (n, rest)
   | BSingle (hn, b') -> (hn, (CSingle ((Pkt (b', n)), rest)))
   | BPairY (hn, b', rc) ->
     (hn, (CPair ((CSingle ((Pkt (b', n)), rest)), rc)))
   | BPairO (hn, lc, b') ->
     (hn, (CPair (lc, (CSingle ((Pkt (b', n)), rest))))))

(** val node_color_f : bool -> 'a1 cnode -> gyor **)

let node_color_f has_child n =
  if negb has_child
  then CG
  else let Node (k, p, s) = n in
       let m =
         match k with
         | KOnly -> Nat.min (bsize p) (bsize s)
         | KLeft -> bsize p
         | KRight -> bsize s
       in
       if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
       then CG
       else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0)))))))
            then CY
            else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                 then CO
                 else CR

(** val tree_of_f : 'a1 cnode -> 'a1 cchain -> 'a1 cchain **)

let tree_of_f n child =
  match node_color_f (chain_has_node child) n with
  | CY ->
    (match child with
     | CEmpty -> CSingle ((Pkt (BHole, n)), child)
     | CSingle (c, rrest) ->
       let Pkt (rb, rn) = c in CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
     | CPair (c, r) ->
       (match c with
        | CSingle (c0, lrest) ->
          let Pkt (lb, ln) = c0 in
          CSingle ((Pkt ((BPairY (n, lb, r)), ln)), lrest)
        | _ -> CSingle ((Pkt (BHole, n)), child)))
  | CO ->
    (match child with
     | CEmpty -> CSingle ((Pkt (BHole, n)), child)
     | CSingle (c, rrest) ->
       let Pkt (rb, rn) = c in CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
     | CPair (l, c) ->
       (match c with
        | CSingle (c0, rrest) ->
          let Pkt (rb, rn) = c0 in
          CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
        | _ -> CSingle ((Pkt (BHole, n)), child)))
  | _ -> CSingle ((Pkt (BHole, n)), child)

(** val pkt_update_f :
    ('a1 cnode -> 'a1 cnode) -> 'a1 cpacket -> 'a1 cchain -> 'a1 cchain **)

let pkt_update_f upd p rest =
  let (n, child) = root_and_child p rest in tree_of_f (upd n) child

(** val node_push_f : 'a1 stored -> 'a1 cnode -> 'a1 cnode **)

let node_push_f s = function
| Node (k, p, suf) ->
  if bis_empty p
  then Node (k, p, (bpush s suf))
  else Node (k, (bpush s p), suf)

(** val node_inject_f : 'a1 cnode -> 'a1 stored -> 'a1 cnode **)

let node_inject_f n s =
  let Node (k, p, suf) = n in
  if bis_empty suf
  then Node (k, (binject p s), suf)
  else Node (k, p, (binject suf s))

(** val push_chain_f : 'a1 stored -> 'a1 cchain -> 'a1 cchain **)

let rec push_chain_f s = function
| CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, (b1 s), bempty)))), CEmpty)
| CSingle (p, rest) -> pkt_update_f (node_push_f s) p rest
| CPair (l, r) -> CPair ((push_chain_f s l), r)

(** val inject_chain_f : 'a1 cchain -> 'a1 stored -> 'a1 cchain **)

let rec inject_chain_f c s =
  match c with
  | CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, bempty, (b1 s))))), CEmpty)
  | CSingle (p, rest) -> pkt_update_f (fun n -> node_inject_f n s) p rest
  | CPair (l, r) -> CPair (l, (inject_chain_f r s))

(** val cad_push_f : 'a1 -> 'a1 cadeque -> 'a1 cadeque **)

let cad_push_f x d =
  push_chain_f (SGround x) d

(** val cad_inject_f : 'a1 cadeque -> 'a1 -> 'a1 cadeque **)

let cad_inject_f d x =
  inject_chain_f d (SGround x)

(** val degenerate_buf_f : 'a1 cchain -> 'a1 stored buffer option **)

let degenerate_buf_f = function
| CSingle (c, c0) ->
  let Pkt (c1, c2) = c in
  (match c1 with
   | BHole ->
     let Node (k, p, s) = c2 in
     (match k with
      | KOnly ->
        (match c0 with
         | CEmpty ->
           if bis_empty p
           then Some s
           else if bis_empty s then Some p else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val make_left_only_f :
    'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let make_left_only_f p1 d1 s1 =
  match d1 with
  | CEmpty ->
    if (<=) (bsize s1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match beject2 s1 with
          | Some p ->
            let (p0, z) = p in
            let (s1', y) = p0 in
            Some (tree_of_f (Node (KLeft, (bapp p1 s1'), (b2 y z))) CEmpty)
          | None -> None)
    else (match bpop s1 with
          | Some p ->
            let (a, t1) = p in
            (match bpop t1 with
             | Some p0 ->
               let (b, t2) = p0 in
               (match bpop t2 with
                | Some p2 ->
                  let (c, srest) = p2 in
                  (match beject2 srest with
                   | Some p3 ->
                     let (p4, z) = p3 in
                     let (smid, y) = p4 in
                     Some
                     (tree_of_f (Node (KLeft, (bapp p1 (b3 a b c)),
                       (b2 y z))) (push_chain_f (SSmall smid) CEmpty))
                   | None -> None)
                | None -> None)
             | None -> None)
          | None -> None)
  | _ ->
    (match beject2 s1 with
     | Some p ->
       let (p0, z) = p in
       let (s1', y) = p0 in
       Some
       (tree_of_f (Node (KLeft, p1, (b2 y z)))
         (inject_chain_f d1 (SSmall s1')))
     | None -> None)

(** val make_left_f : 'a1 cchain -> 'a1 cchain option **)

let make_left_f = function
| CEmpty -> None
| CSingle (p, r) ->
  let (c, d1) = root_and_child p r in
  let Node (_, p1, s1) = c in make_left_only_f p1 d1 s1
| CPair (c, c0) ->
  (match c with
   | CSingle (pl, rl) ->
     (match c0 with
      | CSingle (pr, rr) ->
        let (c1, d1) = root_and_child pl rl in
        let Node (_, p1, s1) = c1 in
        let (c2, d2) = root_and_child pr rr in
        let Node (_, p2, s2) = c2 in
        (match d1 with
         | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
         | _ ->
           (match beject2 s2 with
            | Some p ->
              let (p0, z) = p in
              let (s2', y) = p0 in
              Some
              (tree_of_f (Node (KLeft, p1, (b2 y z)))
                (inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))))
            | None -> None))
      | _ -> None)
   | _ -> None)

(** val make_right_only_f :
    'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let make_right_only_f p1 d1 s1 =
  match d1 with
  | CEmpty ->
    if (<=) (bsize p1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match bpop2 p1 with
          | Some p ->
            let (p0, p1') = p in
            let (x, y) = p0 in
            Some (tree_of_f (Node (KRight, (b2 x y), (bapp p1' s1))) CEmpty)
          | None -> None)
    else (match bpop2 p1 with
          | Some p ->
            let (p0, p1') = p in
            let (x, y) = p0 in
            (match beject3 p1' with
             | Some p2 ->
               let (p3, c) = p2 in
               let (p4, b) = p3 in
               let (pmid, a) = p4 in
               Some
               (tree_of_f (Node (KRight, (b2 x y), (bapp (b3 a b c) s1)))
                 (push_chain_f (SSmall pmid) CEmpty))
             | None -> None)
          | None -> None)
  | _ ->
    (match bpop2 p1 with
     | Some p ->
       let (p0, p1') = p in
       let (x, y) = p0 in
       Some
       (tree_of_f (Node (KRight, (b2 x y), s1))
         (push_chain_f (SSmall p1') d1))
     | None -> None)

(** val make_right_f : 'a1 cchain -> 'a1 cchain option **)

let make_right_f = function
| CEmpty -> None
| CSingle (p, r) ->
  let (c, d1) = root_and_child p r in
  let Node (_, p1, s1) = c in make_right_only_f p1 d1 s1
| CPair (c, c0) ->
  (match c with
   | CSingle (pl, rl) ->
     (match c0 with
      | CSingle (pr, rr) ->
        let (c1, d1) = root_and_child pl rl in
        let Node (_, p1, s1) = c1 in
        let (c2, d2) = root_and_child pr rr in
        let Node (_, p2, s2) = c2 in
        (match d2 with
         | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
         | _ ->
           (match bpop2 p1 with
            | Some p ->
              let (p0, p1') = p in
              let (x, y) = p0 in
              Some
              (tree_of_f (Node (KRight, (b2 x y), s2))
                (push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2))
            | None -> None))
      | _ -> None)
   | _ -> None)

(** val concat_small_left_f :
    'a1 stored buffer -> 'a1 cchain -> 'a1 cchain option **)

let concat_small_left_f p3 e =
  if Nat.ltb (bsize p3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (bfold_right push_chain_f e p3)
  else (match e with
        | CEmpty -> None
        | CSingle (p, r) ->
          let (c, d2) = root_and_child p r in
          let Node (_, p2, s2) = c in
          (match d2 with
           | CEmpty ->
             (match beject2 p2 with
              | Some p0 ->
                let (p1, z) = p0 in
                let (p2', y) = p1 in
                Some
                (tree_of_f (Node (KOnly, p3, (bpush y (bpush z s2))))
                  (push_chain_f (SSmall p2') CEmpty))
              | None -> None)
           | _ ->
             Some
               (tree_of_f (Node (KOnly, p3, s2))
                 (push_chain_f (SSmall p2) d2)))
        | CPair (c, rt) ->
          (match c with
           | CSingle (pl, rl) ->
             let (c0, d2) = root_and_child pl rl in
             let Node (_, p2, s2) = c0 in
             Some (CPair
             ((tree_of_f (Node (KLeft, p3, s2)) (push_chain_f (SSmall p2) d2)),
             rt))
           | _ -> None))

(** val concat_small_right_f :
    'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let concat_small_right_f d s3 =
  if Nat.ltb (bsize s3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (bfold_left inject_chain_f s3 d)
  else (match d with
        | CEmpty -> None
        | CSingle (p, r) ->
          let (c, d1) = root_and_child p r in
          let Node (_, p1, s1) = c in
          (match d1 with
           | CEmpty ->
             (match bpop2 s1 with
              | Some p0 ->
                let (p2, s1') = p0 in
                let (x, y) = p2 in
                Some
                (tree_of_f (Node (KOnly, (binject (binject p1 x) y), s3))
                  (push_chain_f (SSmall s1') CEmpty))
              | None -> None)
           | _ ->
             Some
               (tree_of_f (Node (KOnly, p1, s3))
                 (inject_chain_f d1 (SSmall s1))))
        | CPair (lt, c) ->
          (match c with
           | CSingle (pr, rr) ->
             let (c0, d1) = root_and_child pr rr in
             let Node (_, p1, s1) = c0 in
             Some (CPair (lt,
             (tree_of_f (Node (KRight, p1, s3))
               (inject_chain_f d1 (SSmall s1)))))
           | _ -> None))

(** val cad_concat_f : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque option **)

let cad_concat_f d e =
  match d with
  | CEmpty -> Some e
  | _ ->
    (match e with
     | CEmpty -> Some d
     | _ ->
       (match degenerate_buf_f d with
        | Some p ->
          (match degenerate_buf_f e with
           | Some s ->
             if (||)
                  (Nat.ltb (bsize p) (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0)))))))))
                  (Nat.ltb (bsize s) (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0)))))))))
             then Some (CSingle ((Pkt (BHole, (Node (KOnly, (bapp p s),
                    bempty)))), CEmpty))
             else Some (CSingle ((Pkt (BHole, (Node (KOnly, p, s)))), CEmpty))
           | None -> concat_small_left_f p e)
        | None ->
          (match degenerate_buf_f e with
           | Some s -> concat_small_right_f d s
           | None ->
             (match make_left_f d with
              | Some t ->
                (match make_right_f e with
                 | Some u -> Some (CPair (t, u))
                 | None -> None)
              | None -> None))))

(** val node_pop_f : 'a1 cnode -> ('a1 stored * 'a1 cnode) option **)

let node_pop_f = function
| Node (k, p, s) ->
  (match bpop p with
   | Some p0 -> let (x, p') = p0 in Some (x, (Node (k, p', s)))
   | None ->
     (match bpop s with
      | Some p0 -> let (x, s') = p0 in Some (x, (Node (k, p, s')))
      | None -> None))

(** val node_eject_f : 'a1 cnode -> ('a1 cnode * 'a1 stored) option **)

let node_eject_f = function
| Node (k, p, s) ->
  (match beject s with
   | Some p0 -> let (s', x) = p0 in Some ((Node (k, p, s')), x)
   | None ->
     (match beject p with
      | Some p0 -> let (p', x) = p0 in Some ((Node (k, p', bempty)), x)
      | None -> None))

(** val rebuild_childless_f : 'a1 cnode -> 'a1 cchain **)

let rebuild_childless_f n = match n with
| Node (k, p, s) ->
  if (&&) (bis_empty p) (bis_empty s)
  then CEmpty
  else (match k with
        | KOnly ->
          if (||) (bis_empty p) (bis_empty s)
          then CSingle ((Pkt (BHole, n)), CEmpty)
          else if (||)
                    (Nat.ltb (bsize p) (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
                    (Nat.ltb (bsize s) (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0))))))
               then CSingle ((Pkt (BHole, (Node (KOnly, (bapp p s),
                      bempty)))), CEmpty)
               else CSingle ((Pkt (BHole, n)), CEmpty)
        | _ -> CSingle ((Pkt (BHole, n)), CEmpty))

(** val pop_raw_f : 'a1 cchain -> ('a1 stored * 'a1 cchain) option **)

let rec pop_raw_f = function
| CEmpty -> None
| CSingle (p, rest) ->
  let (n, child) = root_and_child p rest in
  (match node_pop_f n with
   | Some p0 ->
     let (x, n') = p0 in
     (match child with
      | CEmpty -> Some (x, (rebuild_childless_f n'))
      | _ -> Some (x, (tree_of_f n' child)))
   | None -> None)
| CPair (l, r) ->
  (match pop_raw_f l with
   | Some p ->
     let (x, l') = p in
     (match l' with
      | CEmpty -> Some (x, r)
      | CSingle (c0, c1) ->
        let Pkt (c2, c3) = c0 in
        (match c2 with
         | BHole ->
           let Node (_, lp, ls) = c3 in
           (match c1 with
            | CEmpty ->
              if Nat.ltb (bsize lp) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match r with
                    | CSingle (pr, rr) ->
                      let (c4, d2) = root_and_child pr rr in
                      let Node (_, p2, s2) = c4 in
                      Some (x,
                      (tree_of_f (Node (KOnly, (bapp lp (bapp ls p2)), s2))
                        d2))
                    | _ -> None)
              else Some (x, (CPair (l', r)))
            | _ -> Some (x, (CPair (l', r))))
         | _ -> Some (x, (CPair (l', r))))
      | CPair (_, _) -> Some (x, (CPair (l', r))))
   | None -> None)

(** val eject_raw_f : 'a1 cchain -> ('a1 cchain * 'a1 stored) option **)

let rec eject_raw_f = function
| CEmpty -> None
| CSingle (p, rest) ->
  let (n, child) = root_and_child p rest in
  (match node_eject_f n with
   | Some p0 ->
     let (n', x) = p0 in
     (match child with
      | CEmpty -> Some ((rebuild_childless_f n'), x)
      | _ -> Some ((tree_of_f n' child), x))
   | None -> None)
| CPair (l, r) ->
  (match eject_raw_f r with
   | Some p ->
     let (r', x) = p in
     (match r' with
      | CEmpty -> Some (l, x)
      | CSingle (c0, c1) ->
        let Pkt (c2, c3) = c0 in
        (match c2 with
         | BHole ->
           let Node (_, rp, rs) = c3 in
           (match c1 with
            | CEmpty ->
              if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match l with
                    | CSingle (pl, rl) ->
                      let (c4, d1) = root_and_child pl rl in
                      let Node (_, p1, s1) = c4 in
                      Some
                      ((tree_of_f (Node (KOnly, p1, (bapp s1 (bapp rp rs))))
                         d1),
                      x)
                    | _ -> None)
              else Some ((CPair (l, r')), x)
            | _ -> Some ((CPair (l, r')), x))
         | _ -> Some ((CPair (l, r')), x))
      | CPair (_, _) -> Some ((CPair (l, r')), x))
   | None -> None)

(** val repair_front_f :
    kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
    -> 'a1 cchain option **)

let repair_front_f k body p1 s1 rest =
  match pop_raw_f rest with
  | Some p ->
    let (s, d1') = p in
    (match s with
     | SGround _ -> None
     | SSmall b ->
       Some (CSingle ((Pkt (body, (Node (k, (bapp p1 b), s1)))), d1'))
     | SBig (p2, d2, s2) ->
       (match cad_concat_f d2 (push_chain_f (SSmall s2) d1') with
        | Some d3 ->
          Some (CSingle ((Pkt (body, (Node (k, (bapp p1 p2), s1)))), d3))
        | None -> None))
  | None -> None

(** val repair_back_f :
    kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
    -> 'a1 cchain option **)

let repair_back_f k body p1 s1 rest =
  match eject_raw_f rest with
  | Some p ->
    let (d1', s) = p in
    (match s with
     | SGround _ -> None
     | SSmall b ->
       Some (CSingle ((Pkt (body, (Node (k, p1, (bapp b s1))))), d1'))
     | SBig (p2, d2, s2) ->
       (match cad_concat_f (inject_chain_f d1' (SSmall p2)) d2 with
        | Some d3 ->
          Some (CSingle ((Pkt (body, (Node (k, p1, (bapp s2 s1))))), d3))
        | None -> None))
  | None -> None

(** val drain_both_f :
    'a1 cchain -> (('a1 stored * 'a1 stored option) * 'a1 cchain) option **)

let drain_both_f = function
| CEmpty -> None
| CSingle (p, r) ->
  let (n, dd) = root_and_child p r in
  (match node_pop_f n with
   | Some p0 ->
     let (cellF, n1) = p0 in
     (match node_eject_f n1 with
      | Some p1 ->
        let (n2, cellB) = p1 in
        (match dd with
         | CEmpty -> Some ((cellF, (Some cellB)), (rebuild_childless_f n2))
         | _ -> Some ((cellF, (Some cellB)), (tree_of_f n2 dd)))
      | None ->
        (match dd with
         | CEmpty -> Some ((cellF, None), CEmpty)
         | _ -> None))
   | None -> None)
| CPair (l, r) ->
  (match pop_raw_f l with
   | Some p ->
     let (cellF, l') = p in
     (match eject_raw_f r with
      | Some p0 ->
        let (r', cellB) = p0 in
        (match l' with
         | CSingle (pl', rl') ->
           let Pkt (c, c0) = pl' in
           (match c with
            | BHole ->
              let Node (_, lp, ls) = c0 in
              (match rl' with
               | CEmpty ->
                 (match r' with
                  | CSingle (pr', rr') ->
                    let Pkt (c1, c2) = pr' in
                    (match c1 with
                     | BHole ->
                       let Node (_, rp, rs) = c2 in
                       (match rr' with
                        | CEmpty ->
                          if (||)
                               (Nat.ltb (bsize lp) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                               (Nat.ltb (bsize rs) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                          then Some ((cellF, (Some cellB)), (CSingle ((Pkt
                                 (BHole, (Node (KOnly, (bapp lp ls),
                                 (bapp rp rs))))), CEmpty)))
                          else Some ((cellF, (Some cellB)), (CPair (l', r')))
                        | _ ->
                          if Nat.ltb (bsize lp) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then let (c3, d2) = root_and_child pr' rr' in
                               let Node (_, p2, s2) = c3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_f (Node (KOnly,
                                 (bapp lp (bapp ls p2)), s2)) d2))
                          else Some ((cellF, (Some cellB)), (CPair (l', r'))))
                     | _ ->
                       if Nat.ltb (bsize lp) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c3, d2) = root_and_child pr' rr' in
                            let Node (_, p2, s2) = c3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_f (Node (KOnly, (bapp lp (bapp ls p2)),
                              s2)) d2))
                       else Some ((cellF, (Some cellB)), (CPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
               | _ ->
                 (match r' with
                  | CSingle (c3, c4) ->
                    let Pkt (c5, c6) = c3 in
                    (match c5 with
                     | BHole ->
                       let Node (_, rp, rs) = c6 in
                       (match c4 with
                        | CEmpty ->
                          if Nat.ltb (bsize rs) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then let (c1, d2) = root_and_child pl' rl' in
                               let Node (_, p2, s2) = c1 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_f (Node (KOnly, p2,
                                 (bapp s2 (bapp rp rs)))) d2))
                          else Some ((cellF, (Some cellB)), (CPair (l', r')))
                        | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
                     | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (CPair (l', r')))))
            | BSingle (_, _) ->
              (match r' with
               | CSingle (c3, c4) ->
                 let Pkt (c5, c6) = c3 in
                 (match c5 with
                  | BHole ->
                    let Node (_, rp, rs) = c6 in
                    (match c4 with
                     | CEmpty ->
                       if Nat.ltb (bsize rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c1, d2) = root_and_child pl' rl' in
                            let Node (_, p2, s2) = c1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_f (Node (KOnly, p2,
                              (bapp s2 (bapp rp rs)))) d2))
                       else Some ((cellF, (Some cellB)), (CPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
            | _ ->
              (match r' with
               | CSingle (c4, c5) ->
                 let Pkt (c6, c7) = c4 in
                 (match c6 with
                  | BHole ->
                    let Node (_, rp, rs) = c7 in
                    (match c5 with
                     | CEmpty ->
                       if Nat.ltb (bsize rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c1, d2) = root_and_child pl' rl' in
                            let Node (_, p2, s2) = c1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_f (Node (KOnly, p2,
                              (bapp s2 (bapp rp rs)))) d2))
                       else Some ((cellF, (Some cellB)), (CPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (CPair (l', r')))))
         | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
      | None -> None)
   | None -> None)

(** val repair_both_f :
    'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain -> 'a1
    cchain option **)

let repair_both_f body p1 s1 rest =
  match drain_both_f rest with
  | Some p ->
    let (p0, mid) = p in
    let (cellF, o) = p0 in
    (match o with
     | Some cellB ->
       let front =
         match cellF with
         | SGround _ -> None
         | SSmall b -> Some (b, mid)
         | SBig (p2, d2, s2) ->
           (match cad_concat_f d2 (push_chain_f (SSmall s2) mid) with
            | Some d4 -> Some (p2, d4)
            | None -> None)
       in
       (match front with
        | Some p2 ->
          let (pf, d4) = p2 in
          (match cellB with
           | SGround _ -> None
           | SSmall b ->
             Some (CSingle ((Pkt (body, (Node (KOnly, (bapp p1 pf),
               (bapp b s1))))), d4))
           | SBig (p3, d3, s3) ->
             (match cad_concat_f (inject_chain_f d4 (SSmall p3)) d3 with
              | Some d5 ->
                Some (CSingle ((Pkt (body, (Node (KOnly, (bapp p1 pf),
                  (bapp s3 s1))))), d5))
              | None -> None))
        | None -> None)
     | None ->
       (match cellF with
        | SGround _ -> None
        | SSmall b ->
          Some (CSingle ((Pkt (body, (Node (KOnly, (bapp p1 b), s1)))),
            CEmpty))
        | SBig (p2, d2, s2) ->
          Some (CSingle ((Pkt (body, (Node (KOnly, (bapp p1 p2),
            (bapp s2 s1))))), d2))))
  | None -> None

(** val repair_packet_f : 'a1 cpacket -> 'a1 cchain -> 'a1 cchain option **)

let repair_packet_f p rest =
  let Pkt (body, n) = p in
  (match node_color_f (chain_has_node rest) n with
   | CR ->
     let Node (k, p1, s1) = n in
     (match k with
      | KOnly ->
        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (bsize s1)
        then repair_front_f KOnly body p1 s1 rest
        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (bsize p1)
             then repair_back_f KOnly body p1 s1 rest
             else repair_both_f body p1 s1 rest
      | KLeft -> repair_front_f KLeft body p1 s1 rest
      | KRight -> repair_back_f KRight body p1 s1 rest)
   | _ -> Some (CSingle (p, rest)))

(** val repair_pop_side_f : 'a1 cchain -> 'a1 cchain option **)

let repair_pop_side_f = function
| CEmpty -> Some CEmpty
| CSingle (p, rest) -> repair_packet_f p rest
| CPair (c0, r) ->
  (match c0 with
   | CSingle (pl, rl) ->
     (match repair_packet_f pl rl with
      | Some l' -> Some (CPair (l', r))
      | None -> None)
   | _ -> None)

(** val repair_eject_side_f : 'a1 cchain -> 'a1 cchain option **)

let repair_eject_side_f = function
| CEmpty -> Some CEmpty
| CSingle (p, rest) -> repair_packet_f p rest
| CPair (l, c0) ->
  (match c0 with
   | CSingle (pr, rr) ->
     (match repair_packet_f pr rr with
      | Some r' -> Some (CPair (l, r'))
      | None -> None)
   | _ -> None)

(** val cad_pop_f : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop_f d =
  match pop_raw_f d with
  | Some p ->
    let (s, d') = p in
    (match s with
     | SGround x ->
       (match repair_pop_side_f d' with
        | Some d'' -> Some (x, d'')
        | None -> None)
     | _ -> None)
  | None -> None

(** val cad_eject_f : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject_f d =
  match eject_raw_f d with
  | Some p ->
    let (d', s) = p in
    (match s with
     | SGround x ->
       (match repair_eject_side_f d' with
        | Some d'' -> Some (d'', x)
        | None -> None)
     | _ -> None)
  | None -> None
