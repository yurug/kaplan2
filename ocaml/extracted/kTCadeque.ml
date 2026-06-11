
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

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

type 'x buffer = 'x list

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

(** val stored_seq : 'a1 stored -> 'a1 list **)

let rec stored_seq = function
| SGround a -> a :: []
| SSmall b ->
  let rec go = function
  | [] -> []
  | x :: r -> app (stored_seq x) (go r)
  in go b
| SBig (p, c, q) ->
  app
    (let rec go = function
     | [] -> []
     | x :: r -> app (stored_seq x) (go r)
     in go p)
    (app (cchain_seq c)
      (let rec go = function
       | [] -> []
       | x :: r -> app (stored_seq x) (go r)
       in go q))

(** val cnode_seq : 'a1 cnode -> 'a1 list -> 'a1 list **)

and cnode_seq n mid =
  let Node (_, p, q) = n in
  app
    (let rec go = function
     | [] -> []
     | x :: r -> app (stored_seq x) (go r)
     in go p)
    (app mid
      (let rec go = function
       | [] -> []
       | x :: r -> app (stored_seq x) (go r)
       in go q))

(** val cbody_seq : 'a1 cbody -> 'a1 list -> 'a1 list **)

and cbody_seq b inner =
  match b with
  | BHole -> inner
  | BSingle (n, b') -> cnode_seq n (cbody_seq b' inner)
  | BPairY (n, b', rc) ->
    cnode_seq n (app (cbody_seq b' inner) (cchain_seq rc))
  | BPairO (n, lc, b') ->
    cnode_seq n (app (cchain_seq lc) (cbody_seq b' inner))

(** val cpacket_seq : 'a1 cpacket -> 'a1 list -> 'a1 list **)

and cpacket_seq p inner =
  let Pkt (b, n) = p in cbody_seq b (cnode_seq n inner)

(** val cchain_seq : 'a1 cchain -> 'a1 list **)

and cchain_seq = function
| CEmpty -> []
| CSingle (p, rest) -> cpacket_seq p (cchain_seq rest)
| CPair (l, r) -> app (cchain_seq l) (cchain_seq r)

(** val cad_to_list : 'a1 cadeque -> 'a1 list **)

let cad_to_list =
  cchain_seq

type gyor =
| CG
| CY
| CO
| CR

(** val node_color : bool -> 'a1 cnode -> gyor **)

let node_color has_child n =
  if negb has_child
  then CG
  else let Node (k, p, s) = n in
       let m =
         match k with
         | KOnly -> Nat.min (length p) (length s)
         | KLeft -> length p
         | KRight -> length s
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

(** val chain_has_node : 'a1 cchain -> bool **)

let chain_has_node = function
| CEmpty -> false
| _ -> true

(** val node_push : 'a1 stored -> 'a1 cnode -> 'a1 cnode **)

let node_push s = function
| Node (k, p, suf) ->
  (match p with
   | [] -> Node (k, [], (s :: suf))
   | _ :: _ -> Node (k, (s :: p), suf))

(** val node_inject : 'a1 cnode -> 'a1 stored -> 'a1 cnode **)

let node_inject n s =
  let Node (k, p, suf) = n in
  (match suf with
   | [] -> Node (k, (app p (s :: [])), [])
   | _ :: _ -> Node (k, p, (app suf (s :: []))))

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

(** val tree_of : 'a1 cnode -> 'a1 cchain -> 'a1 cchain **)

let tree_of n child =
  match node_color (chain_has_node child) n with
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

(** val pkt_update :
    ('a1 cnode -> 'a1 cnode) -> 'a1 cpacket -> 'a1 cchain -> 'a1 cchain **)

let pkt_update upd p rest =
  let (n, child) = root_and_child p rest in tree_of (upd n) child

(** val push_chain : 'a1 stored -> 'a1 cchain -> 'a1 cchain **)

let rec push_chain s = function
| CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, (s :: []), [])))), CEmpty)
| CSingle (p, rest) -> pkt_update (node_push s) p rest
| CPair (l, r) -> CPair ((push_chain s l), r)

(** val inject_chain : 'a1 cchain -> 'a1 stored -> 'a1 cchain **)

let rec inject_chain c s =
  match c with
  | CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, [], (s :: []))))), CEmpty)
  | CSingle (p, rest) -> pkt_update (fun n -> node_inject n s) p rest
  | CPair (l, r) -> CPair (l, (inject_chain r s))

(** val cad_push : 'a1 -> 'a1 cadeque -> 'a1 cadeque **)

let cad_push x d =
  push_chain (SGround x) d

(** val cad_inject : 'a1 cadeque -> 'a1 -> 'a1 cadeque **)

let cad_inject d x =
  inject_chain d (SGround x)

(** val buf_pop2 : 'a1 buffer -> (('a1 * 'a1) * 'a1 buffer) option **)

let buf_pop2 = function
| [] -> None
| x :: l -> (match l with
             | [] -> None
             | y :: r -> Some ((x, y), r))

(** val buf_eject2 : 'a1 buffer -> (('a1 buffer * 'a1) * 'a1) option **)

let buf_eject2 b =
  match rev b with
  | [] -> None
  | z :: l -> (match l with
               | [] -> None
               | y :: r -> Some (((rev r), y), z))

(** val buf_eject3 :
    'a1 buffer -> ((('a1 buffer * 'a1) * 'a1) * 'a1) option **)

let buf_eject3 b =
  match rev b with
  | [] -> None
  | c :: l ->
    (match l with
     | [] -> None
     | bb :: l0 ->
       (match l0 with
        | [] -> None
        | a :: r -> Some ((((rev r), a), bb), c)))

(** val degenerate_buf : 'a1 cchain -> 'a1 stored buffer option **)

let degenerate_buf = function
| CSingle (c, c0) ->
  let Pkt (c1, c2) = c in
  (match c1 with
   | BHole ->
     let Node (k, p, s) = c2 in
     (match k with
      | KOnly ->
        (match c0 with
         | CEmpty ->
           (match p with
            | [] -> Some s
            | _ :: _ -> (match s with
                         | [] -> Some p
                         | _ :: _ -> None))
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val make_left_only :
    'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let make_left_only p1 d1 s1 =
  match d1 with
  | CEmpty ->
    if (<=) (length s1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match buf_eject2 s1 with
          | Some p ->
            let (p0, z) = p in
            let (s1', y) = p0 in
            Some
            (tree_of (Node (KLeft, (app p1 s1'), (y :: (z :: [])))) CEmpty)
          | None -> None)
    else (match s1 with
          | [] -> None
          | a :: l ->
            (match l with
             | [] -> None
             | b :: l0 ->
               (match l0 with
                | [] -> None
                | c :: srest ->
                  (match buf_eject2 srest with
                   | Some p ->
                     let (p0, z) = p in
                     let (smid, y) = p0 in
                     Some
                     (tree_of (Node (KLeft, (app p1 (a :: (b :: (c :: [])))),
                       (y :: (z :: [])))) (push_chain (SSmall smid) CEmpty))
                   | None -> None))))
  | _ ->
    (match buf_eject2 s1 with
     | Some p ->
       let (p0, z) = p in
       let (s1', y) = p0 in
       Some
       (tree_of (Node (KLeft, p1, (y :: (z :: []))))
         (inject_chain d1 (SSmall s1')))
     | None -> None)

(** val make_left : 'a1 cchain -> 'a1 cchain option **)

let make_left = function
| CEmpty -> None
| CSingle (p, r) ->
  let (c, d1) = root_and_child p r in
  let Node (_, p1, s1) = c in make_left_only p1 d1 s1
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
         | CEmpty -> make_left_only (app p1 (app s1 p2)) d2 s2
         | _ ->
           (match buf_eject2 s2 with
            | Some p ->
              let (p0, z) = p in
              let (s2', y) = p0 in
              Some
              (tree_of (Node (KLeft, p1, (y :: (z :: []))))
                (inject_chain d1 (SBig ((app s1 p2), d2, s2'))))
            | None -> None))
      | _ -> None)
   | _ -> None)

(** val make_right_only :
    'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let make_right_only p1 d1 s1 =
  match d1 with
  | CEmpty ->
    if (<=) (length p1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match buf_pop2 p1 with
          | Some p ->
            let (p0, p1') = p in
            let (x, y) = p0 in
            Some
            (tree_of (Node (KRight, (x :: (y :: [])), (app p1' s1))) CEmpty)
          | None -> None)
    else (match buf_pop2 p1 with
          | Some p ->
            let (p0, p1') = p in
            let (x, y) = p0 in
            (match buf_eject3 p1' with
             | Some p2 ->
               let (p3, c) = p2 in
               let (p4, b) = p3 in
               let (pmid, a) = p4 in
               Some
               (tree_of (Node (KRight, (x :: (y :: [])),
                 (app (a :: (b :: (c :: []))) s1)))
                 (push_chain (SSmall pmid) CEmpty))
             | None -> None)
          | None -> None)
  | _ ->
    (match buf_pop2 p1 with
     | Some p ->
       let (p0, p1') = p in
       let (x, y) = p0 in
       Some
       (tree_of (Node (KRight, (x :: (y :: [])), s1))
         (push_chain (SSmall p1') d1))
     | None -> None)

(** val make_right : 'a1 cchain -> 'a1 cchain option **)

let make_right = function
| CEmpty -> None
| CSingle (p, r) ->
  let (c, d1) = root_and_child p r in
  let Node (_, p1, s1) = c in make_right_only p1 d1 s1
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
         | CEmpty -> make_right_only p1 d1 (app s1 (app p2 s2))
         | _ ->
           (match buf_pop2 p1 with
            | Some p ->
              let (p0, p1') = p in
              let (x, y) = p0 in
              Some
              (tree_of (Node (KRight, (x :: (y :: [])), s2))
                (push_chain (SBig (p1', d1, (app s1 p2))) d2))
            | None -> None))
      | _ -> None)
   | _ -> None)

(** val concat_small_left :
    'a1 stored buffer -> 'a1 cchain -> 'a1 cchain option **)

let concat_small_left p3 e =
  if Nat.ltb (length p3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (fold_right push_chain e p3)
  else (match e with
        | CEmpty -> None
        | CSingle (p, r) ->
          let (c, d2) = root_and_child p r in
          let Node (_, p2, s2) = c in
          (match d2 with
           | CEmpty ->
             (match buf_eject2 p2 with
              | Some p0 ->
                let (p1, z) = p0 in
                let (p2', y) = p1 in
                Some
                (tree_of (Node (KOnly, p3, (y :: (z :: s2))))
                  (push_chain (SSmall p2') CEmpty))
              | None -> None)
           | _ ->
             Some (tree_of (Node (KOnly, p3, s2)) (push_chain (SSmall p2) d2)))
        | CPair (c, rt) ->
          (match c with
           | CSingle (pl, rl) ->
             let (c0, d2) = root_and_child pl rl in
             let Node (_, p2, s2) = c0 in
             Some (CPair
             ((tree_of (Node (KLeft, p3, s2)) (push_chain (SSmall p2) d2)),
             rt))
           | _ -> None))

(** val concat_small_right :
    'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option **)

let concat_small_right d s3 =
  if Nat.ltb (length s3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (fold_left inject_chain s3 d)
  else (match d with
        | CEmpty -> None
        | CSingle (p, r) ->
          let (c, d1) = root_and_child p r in
          let Node (_, p1, s1) = c in
          (match d1 with
           | CEmpty ->
             (match buf_pop2 s1 with
              | Some p0 ->
                let (p2, s1') = p0 in
                let (x, y) = p2 in
                Some
                (tree_of (Node (KOnly, (app p1 (x :: (y :: []))), s3))
                  (push_chain (SSmall s1') CEmpty))
              | None -> None)
           | _ ->
             Some
               (tree_of (Node (KOnly, p1, s3)) (inject_chain d1 (SSmall s1))))
        | CPair (lt, c) ->
          (match c with
           | CSingle (pr, rr) ->
             let (c0, d1) = root_and_child pr rr in
             let Node (_, p1, s1) = c0 in
             Some (CPair (lt,
             (tree_of (Node (KRight, p1, s3)) (inject_chain d1 (SSmall s1)))))
           | _ -> None))

(** val cad_concat : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque option **)

let cad_concat d e =
  match d with
  | CEmpty -> Some e
  | _ ->
    (match e with
     | CEmpty -> Some d
     | _ ->
       (match degenerate_buf d with
        | Some p ->
          (match degenerate_buf e with
           | Some s ->
             if (||)
                  (Nat.ltb (length p) (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0)))))))))
                  (Nat.ltb (length s) (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    0)))))))))
             then Some (CSingle ((Pkt (BHole, (Node (KOnly, (app p s),
                    [])))), CEmpty))
             else Some (CSingle ((Pkt (BHole, (Node (KOnly, p, s)))), CEmpty))
           | None -> concat_small_left p e)
        | None ->
          (match degenerate_buf e with
           | Some s -> concat_small_right d s
           | None ->
             (match make_left d with
              | Some t ->
                (match make_right e with
                 | Some u -> Some (CPair (t, u))
                 | None -> None)
              | None -> None))))

(** val node_pop : 'a1 cnode -> ('a1 stored * 'a1 cnode) option **)

let node_pop = function
| Node (k, b, s) ->
  (match b with
   | [] -> (match s with
            | [] -> None
            | x :: s0 -> Some (x, (Node (k, [], s0))))
   | x :: p -> Some (x, (Node (k, p, s))))

(** val node_eject : 'a1 cnode -> ('a1 cnode * 'a1 stored) option **)

let node_eject = function
| Node (k, p, s) ->
  (match rev s with
   | [] ->
     (match rev p with
      | [] -> None
      | x :: p' -> Some ((Node (k, (rev p'), [])), x))
   | x :: s' -> Some ((Node (k, p, (rev s'))), x))

(** val rebuild_childless : 'a1 cnode -> 'a1 cchain **)

let rebuild_childless n = match n with
| Node (k, p, s) ->
  (match k with
   | KOnly ->
     (match p with
      | [] ->
        (match s with
         | [] -> CEmpty
         | _ :: _ ->
           (match p with
            | [] -> CSingle ((Pkt (BHole, n)), CEmpty)
            | _ :: _ ->
              (match s with
               | [] -> CSingle ((Pkt (BHole, n)), CEmpty)
               | _ :: _ ->
                 if (||)
                      (Nat.ltb (length p) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        0))))))
                      (Nat.ltb (length s) (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        0))))))
                 then CSingle ((Pkt (BHole, (Node (KOnly, (app p s), [])))),
                        CEmpty)
                 else CSingle ((Pkt (BHole, n)), CEmpty))))
      | _ :: _ ->
        (match p with
         | [] -> CSingle ((Pkt (BHole, n)), CEmpty)
         | _ :: _ ->
           (match s with
            | [] -> CSingle ((Pkt (BHole, n)), CEmpty)
            | _ :: _ ->
              if (||)
                   (Nat.ltb (length p) (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     0))))))
                   (Nat.ltb (length s) (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     0))))))
              then CSingle ((Pkt (BHole, (Node (KOnly, (app p s), [])))),
                     CEmpty)
              else CSingle ((Pkt (BHole, n)), CEmpty))))
   | _ ->
     (match p with
      | [] ->
        (match s with
         | [] -> CEmpty
         | _ :: _ -> CSingle ((Pkt (BHole, n)), CEmpty))
      | _ :: _ -> CSingle ((Pkt (BHole, n)), CEmpty)))

(** val pop_raw : 'a1 cchain -> ('a1 stored * 'a1 cchain) option **)

let rec pop_raw = function
| CEmpty -> None
| CSingle (p, rest) ->
  let (n, child) = root_and_child p rest in
  (match node_pop n with
   | Some p0 ->
     let (x, n') = p0 in
     (match child with
      | CEmpty -> Some (x, (rebuild_childless n'))
      | _ -> Some (x, (tree_of n' child)))
   | None -> None)
| CPair (l, r) ->
  (match pop_raw l with
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
              if Nat.ltb (length lp) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match r with
                    | CSingle (pr, rr) ->
                      let (c4, d2) = root_and_child pr rr in
                      let Node (_, p2, s2) = c4 in
                      Some (x,
                      (tree_of (Node (KOnly, (app lp (app ls p2)), s2)) d2))
                    | _ -> None)
              else Some (x, (CPair (l', r)))
            | _ -> Some (x, (CPair (l', r))))
         | _ -> Some (x, (CPair (l', r))))
      | CPair (_, _) -> Some (x, (CPair (l', r))))
   | None -> None)

(** val eject_raw : 'a1 cchain -> ('a1 cchain * 'a1 stored) option **)

let rec eject_raw = function
| CEmpty -> None
| CSingle (p, rest) ->
  let (n, child) = root_and_child p rest in
  (match node_eject n with
   | Some p0 ->
     let (n', x) = p0 in
     (match child with
      | CEmpty -> Some ((rebuild_childless n'), x)
      | _ -> Some ((tree_of n' child), x))
   | None -> None)
| CPair (l, r) ->
  (match eject_raw r with
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
              if Nat.ltb (length rs) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match l with
                    | CSingle (pl, rl) ->
                      let (c4, d1) = root_and_child pl rl in
                      let Node (_, p1, s1) = c4 in
                      Some
                      ((tree_of (Node (KOnly, p1, (app s1 (app rp rs)))) d1),
                      x)
                    | _ -> None)
              else Some ((CPair (l, r')), x)
            | _ -> Some ((CPair (l, r')), x))
         | _ -> Some ((CPair (l, r')), x))
      | CPair (_, _) -> Some ((CPair (l, r')), x))
   | None -> None)

(** val repair_front :
    kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
    -> 'a1 cchain option **)

let repair_front k body p1 s1 rest =
  match pop_raw rest with
  | Some p ->
    let (s, d1') = p in
    (match s with
     | SGround _ -> None
     | SSmall b ->
       Some (CSingle ((Pkt (body, (Node (k, (app p1 b), s1)))), d1'))
     | SBig (p2, d2, s2) ->
       (match cad_concat d2 (push_chain (SSmall s2) d1') with
        | Some d3 ->
          Some (CSingle ((Pkt (body, (Node (k, (app p1 p2), s1)))), d3))
        | None -> None))
  | None -> None

(** val repair_back :
    kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
    -> 'a1 cchain option **)

let repair_back k body p1 s1 rest =
  match eject_raw rest with
  | Some p ->
    let (d1', s) = p in
    (match s with
     | SGround _ -> None
     | SSmall b ->
       Some (CSingle ((Pkt (body, (Node (k, p1, (app b s1))))), d1'))
     | SBig (p2, d2, s2) ->
       (match cad_concat (inject_chain d1' (SSmall p2)) d2 with
        | Some d3 ->
          Some (CSingle ((Pkt (body, (Node (k, p1, (app s2 s1))))), d3))
        | None -> None))
  | None -> None

(** val drain_both :
    'a1 cchain -> (('a1 stored * 'a1 stored option) * 'a1 cchain) option **)

let drain_both = function
| CEmpty -> None
| CSingle (p, r) ->
  let (n, dd) = root_and_child p r in
  (match node_pop n with
   | Some p0 ->
     let (cellF, n1) = p0 in
     (match node_eject n1 with
      | Some p1 ->
        let (n2, cellB) = p1 in
        (match dd with
         | CEmpty -> Some ((cellF, (Some cellB)), (rebuild_childless n2))
         | _ -> Some ((cellF, (Some cellB)), (tree_of n2 dd)))
      | None ->
        (match dd with
         | CEmpty -> Some ((cellF, None), CEmpty)
         | _ -> None))
   | None -> None)
| CPair (l, r) ->
  (match pop_raw l with
   | Some p ->
     let (cellF, l') = p in
     (match eject_raw r with
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
                               (Nat.ltb (length lp) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                               (Nat.ltb (length rs) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                          then Some ((cellF, (Some cellB)), (CSingle ((Pkt
                                 (BHole, (Node (KOnly, (app lp ls),
                                 (app rp rs))))), CEmpty)))
                          else Some ((cellF, (Some cellB)), (CPair (l', r')))
                        | _ ->
                          if Nat.ltb (length lp) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then let (c3, d2) = root_and_child pr' rr' in
                               let Node (_, p2, s2) = c3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of (Node (KOnly, (app lp (app ls p2)),
                                 s2)) d2))
                          else Some ((cellF, (Some cellB)), (CPair (l', r'))))
                     | _ ->
                       if Nat.ltb (length lp) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c3, d2) = root_and_child pr' rr' in
                            let Node (_, p2, s2) = c3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of (Node (KOnly, (app lp (app ls p2)), s2))
                              d2))
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
                          if Nat.ltb (length rs) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then let (c1, d2) = root_and_child pl' rl' in
                               let Node (_, p2, s2) = c1 in
                               Some ((cellF, (Some cellB)),
                               (tree_of (Node (KOnly, p2,
                                 (app s2 (app rp rs)))) d2))
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
                       if Nat.ltb (length rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c1, d2) = root_and_child pl' rl' in
                            let Node (_, p2, s2) = c1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of (Node (KOnly, p2, (app s2 (app rp rs))))
                              d2))
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
                       if Nat.ltb (length rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let (c1, d2) = root_and_child pl' rl' in
                            let Node (_, p2, s2) = c1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of (Node (KOnly, p2, (app s2 (app rp rs))))
                              d2))
                       else Some ((cellF, (Some cellB)), (CPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (CPair (l', r')))))
         | _ -> Some ((cellF, (Some cellB)), (CPair (l', r'))))
      | None -> None)
   | None -> None)

(** val repair_both :
    'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain -> 'a1
    cchain option **)

let repair_both body p1 s1 rest =
  match drain_both rest with
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
           (match cad_concat d2 (push_chain (SSmall s2) mid) with
            | Some d4 -> Some (p2, d4)
            | None -> None)
       in
       (match front with
        | Some p2 ->
          let (pf, d4) = p2 in
          (match cellB with
           | SGround _ -> None
           | SSmall b ->
             Some (CSingle ((Pkt (body, (Node (KOnly, (app p1 pf),
               (app b s1))))), d4))
           | SBig (p3, d3, s3) ->
             (match cad_concat (inject_chain d4 (SSmall p3)) d3 with
              | Some d5 ->
                Some (CSingle ((Pkt (body, (Node (KOnly, (app p1 pf),
                  (app s3 s1))))), d5))
              | None -> None))
        | None -> None)
     | None ->
       (match cellF with
        | SGround _ -> None
        | SSmall b ->
          Some (CSingle ((Pkt (body, (Node (KOnly, (app p1 b), s1)))),
            CEmpty))
        | SBig (p2, d2, s2) ->
          Some (CSingle ((Pkt (body, (Node (KOnly, (app p1 p2),
            (app s2 s1))))), d2))))
  | None -> None

(** val repair_packet : 'a1 cpacket -> 'a1 cchain -> 'a1 cchain option **)

let repair_packet p rest =
  let Pkt (body, n) = p in
  (match node_color (chain_has_node rest) n with
   | CR ->
     let Node (k, p1, s1) = n in
     (match k with
      | KOnly ->
        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (length s1)
        then repair_front KOnly body p1 s1 rest
        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (length p1)
             then repair_back KOnly body p1 s1 rest
             else repair_both body p1 s1 rest
      | KLeft -> repair_front KLeft body p1 s1 rest
      | KRight -> repair_back KRight body p1 s1 rest)
   | _ -> Some (CSingle (p, rest)))

(** val repair_pop_side : 'a1 cchain -> 'a1 cchain option **)

let repair_pop_side = function
| CEmpty -> Some CEmpty
| CSingle (p, rest) -> repair_packet p rest
| CPair (c0, r) ->
  (match c0 with
   | CSingle (pl, rl) ->
     (match repair_packet pl rl with
      | Some l' -> Some (CPair (l', r))
      | None -> None)
   | _ -> None)

(** val repair_eject_side : 'a1 cchain -> 'a1 cchain option **)

let repair_eject_side = function
| CEmpty -> Some CEmpty
| CSingle (p, rest) -> repair_packet p rest
| CPair (l, c0) ->
  (match c0 with
   | CSingle (pr, rr) ->
     (match repair_packet pr rr with
      | Some r' -> Some (CPair (l, r'))
      | None -> None)
   | _ -> None)

(** val cad_pop : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop d =
  match pop_raw d with
  | Some p ->
    let (s, d') = p in
    (match s with
     | SGround x ->
       (match repair_pop_side d' with
        | Some d'' -> Some (x, d'')
        | None -> None)
     | _ -> None)
  | None -> None

(** val cad_eject : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject d =
  match eject_raw d with
  | Some p ->
    let (d', s) = p in
    (match s with
     | SGround x ->
       (match repair_eject_side d' with
        | Some d'' -> Some (d'', x)
        | None -> None)
     | _ -> None)
  | None -> None
