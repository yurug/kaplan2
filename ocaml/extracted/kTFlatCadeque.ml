
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

  let rec min = (fun a b -> if (a:int) <= b then a else b)
 end

type 'x buffer = 'x Fastbuf.t

type kind =
| KOnly
| KLeft
| KRight

type gyor =
| CG
| CY
| CO
| CR

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

type 'a fnode =
| FNode of kind * 'a Sraw.t buffer * 'a Sraw.t buffer
and 'a fbody =
| FHole
| FBSingle of 'a fnode * 'a fbody
| FBPairY of 'a fnode * 'a fbody * 'a fchain
| FBPairO of 'a fnode * 'a fchain * 'a fbody
and 'a fchain =
| FEmpty
| FFlat of kind * 'a Sraw.t buffer * 'a Sraw.t buffer * 'a fchain
| FSingle of 'a fbody * 'a fnode * 'a fchain
| FPair of 'a fchain * 'a fchain

(** val cell_case_ground : 'a1 Sraw.t -> ('a1 -> 'a2) -> 'a2 -> 'a2 **)

let cell_case_ground = (fun c kg _ -> kg (Obj.magic c))

(** val cell_case_struct :
    'a1 Sraw.t -> ('a1 Sraw.t buffer -> 'a2) -> ('a1 Sraw.t buffer -> 'a1
    fchain -> 'a1 Sraw.t buffer -> 'a2) -> 'a2 -> 'a2 **)

let cell_case_struct = (fun c ks kb _ -> Sraw.case_struct ks kb c)

(** val tree_of_x : 'a1 fnode -> 'a1 fchain -> 'a1 fchain **)

let tree_of_x n child =
  match if negb (match child with
                 | FEmpty -> false
                 | _ -> true)
        then CG
        else let FNode (k, p, s) = n in
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
                  else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                       then CO
                       else CR with
  | CY ->
    (match child with
     | FEmpty ->
       let b = FHole in
       (match b with
        | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, child)
        | _ -> FSingle (b, n, child))
     | FFlat (k2, p2, s2, rrest) ->
       FSingle ((FBSingle (n, FHole)), (FNode (k2, p2, s2)), rrest)
     | FSingle (rb, rn, rrest) -> FSingle ((FBSingle (n, rb)), rn, rrest)
     | FPair (f, r) ->
       (match f with
        | FFlat (k2, p2, s2, lrest) ->
          FSingle ((FBPairY (n, FHole, r)), (FNode (k2, p2, s2)), lrest)
        | FSingle (lb, ln, lrest) -> FSingle ((FBPairY (n, lb, r)), ln, lrest)
        | _ ->
          let b = FHole in
          (match b with
           | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, child)
           | _ -> FSingle (b, n, child))))
  | CO ->
    (match child with
     | FEmpty ->
       let b = FHole in
       (match b with
        | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, child)
        | _ -> FSingle (b, n, child))
     | FFlat (k2, p2, s2, rrest) ->
       FSingle ((FBSingle (n, FHole)), (FNode (k2, p2, s2)), rrest)
     | FSingle (rb, rn, rrest) -> FSingle ((FBSingle (n, rb)), rn, rrest)
     | FPair (l, f) ->
       (match f with
        | FFlat (k2, p2, s2, rrest) ->
          FSingle ((FBPairO (n, l, FHole)), (FNode (k2, p2, s2)), rrest)
        | FSingle (rb, rn, rrest) -> FSingle ((FBPairO (n, l, rb)), rn, rrest)
        | _ ->
          let b = FHole in
          (match b with
           | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, child)
           | _ -> FSingle (b, n, child))))
  | _ ->
    let b = FHole in
    (match b with
     | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, child)
     | _ -> FSingle (b, n, child))

(** val root_and_child_x :
    'a1 fbody -> 'a1 fnode -> 'a1 fchain -> 'a1 fnode * 'a1 fchain **)

let root_and_child_x b n rest =
  match b with
  | FHole -> (n, rest)
  | FBSingle (hn, b') ->
    (hn,
      (match b' with
       | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, rest)
       | _ -> FSingle (b', n, rest)))
  | FBPairY (hn, b', rc) ->
    (hn, (FPair
      ((match b' with
        | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, rest)
        | _ -> FSingle (b', n, rest)),
      rc)))
  | FBPairO (hn, lc, b') ->
    (hn, (FPair (lc,
      (match b' with
       | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, rest)
       | _ -> FSingle (b', n, rest)))))

(** val push_chain_x : 'a1 Sraw.t -> 'a1 fchain -> 'a1 fchain **)

let rec push_chain_x s = function
| FEmpty -> FFlat (KOnly, (b1 s), bempty, FEmpty)
| FFlat (k, p, sf, rest) ->
  tree_of_x
    (if bis_empty p
     then FNode (k, p, (bpush s sf))
     else FNode (k, (bpush s p), sf))
    rest
| FSingle (b, n, rest) ->
  (match b with
   | FHole ->
     tree_of_x
       (let FNode (k, p, suf) = n in
        if bis_empty p
        then FNode (k, p, (bpush s suf))
        else FNode (k, (bpush s p), suf))
       rest
   | FBSingle (hn, b') ->
     let hn' =
       let FNode (k, p, suf) = hn in
       if bis_empty p
       then FNode (k, p, (bpush s suf))
       else FNode (k, (bpush s p), suf)
     in
     (match if negb true
            then CG
            else let FNode (k, p, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p) (bsize s0)
                   | KLeft -> bsize p
                   | KRight -> bsize s0
                 in
                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                 then CG
                 else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
                      then CY
                      else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CO
                           else CR with
      | CG ->
        let b0 = FHole in
        (match b0 with
         | FHole ->
           let FNode (k, p, s0) = hn' in
           FFlat (k, p, s0,
           (match b' with
            | FHole -> let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
            | _ -> FSingle (b', n, rest)))
         | _ ->
           FSingle (b0, hn',
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest))))
      | CR ->
        let b0 = FHole in
        (match b0 with
         | FHole ->
           let FNode (k, p, s0) = hn' in
           FFlat (k, p, s0,
           (match b' with
            | FHole -> let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
            | _ -> FSingle (b', n, rest)))
         | _ ->
           FSingle (b0, hn',
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest))))
      | _ -> FSingle ((FBSingle (hn', b')), n, rest))
   | FBPairY (hn, b', rc) ->
     let hn' =
       let FNode (k, p, suf) = hn in
       if bis_empty p
       then FNode (k, p, (bpush s suf))
       else FNode (k, (bpush s p), suf)
     in
     (match if negb true
            then CG
            else let FNode (k, p, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p) (bsize s0)
                   | KLeft -> bsize p
                   | KRight -> bsize s0
                 in
                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                 then CG
                 else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
                      then CY
                      else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CO
                           else CR with
      | CY -> FSingle ((FBPairY (hn', b', rc)), n, rest)
      | CO ->
        (match rc with
         | FFlat (k2, p2, s2, rrest) ->
           FSingle ((FBPairO (hn',
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest)),
             FHole)), (FNode (k2, p2, s2)), rrest)
         | FSingle (rb, rn, rrest) ->
           FSingle ((FBPairO (hn',
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest)),
             rb)), rn, rrest)
         | _ ->
           let b0 = FHole in
           (match b0 with
            | FHole ->
              let FNode (k, p, s0) = hn' in
              FFlat (k, p, s0, (FPair
              ((match b' with
                | FHole ->
                  let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
                | _ -> FSingle (b', n, rest)),
              rc)))
            | _ ->
              FSingle (b0, hn', (FPair
                ((match b' with
                  | FHole ->
                    let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                  | _ -> FSingle (b', n, rest)),
                rc)))))
      | _ ->
        let b0 = FHole in
        (match b0 with
         | FHole ->
           let FNode (k, p, s0) = hn' in
           FFlat (k, p, s0, (FPair
           ((match b' with
             | FHole -> let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
             | _ -> FSingle (b', n, rest)),
           rc)))
         | _ ->
           FSingle (b0, hn', (FPair
             ((match b' with
               | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
               | _ -> FSingle (b', n, rest)),
             rc)))))
   | FBPairO (hn, lc, b') ->
     let hn' =
       let FNode (k, p, suf) = hn in
       if bis_empty p
       then FNode (k, p, (bpush s suf))
       else FNode (k, (bpush s p), suf)
     in
     (match if negb true
            then CG
            else let FNode (k, p, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p) (bsize s0)
                   | KLeft -> bsize p
                   | KRight -> bsize s0
                 in
                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                 then CG
                 else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))
                      then CY
                      else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CO
                           else CR with
      | CY ->
        (match lc with
         | FFlat (k2, p2, s2, lrest) ->
           FSingle ((FBPairY (hn', FHole,
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest)))),
             (FNode (k2, p2, s2)), lrest)
         | FSingle (lb, ln, lrest) ->
           FSingle ((FBPairY (hn', lb,
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest)))),
             ln, lrest)
         | _ ->
           let b0 = FHole in
           (match b0 with
            | FHole ->
              let FNode (k, p, s0) = hn' in
              FFlat (k, p, s0, (FPair (lc,
              (match b' with
               | FHole ->
                 let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
               | _ -> FSingle (b', n, rest)))))
            | _ ->
              FSingle (b0, hn', (FPair (lc,
                (match b' with
                 | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                 | _ -> FSingle (b', n, rest)))))))
      | CO -> FSingle ((FBPairO (hn', lc, b')), n, rest)
      | _ ->
        let b0 = FHole in
        (match b0 with
         | FHole ->
           let FNode (k, p, s0) = hn' in
           FFlat (k, p, s0, (FPair (lc,
           (match b' with
            | FHole -> let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
            | _ -> FSingle (b', n, rest)))))
         | _ ->
           FSingle (b0, hn', (FPair (lc,
             (match b' with
              | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
              | _ -> FSingle (b', n, rest))))))))
| FPair (l, r) -> FPair ((push_chain_x s l), r)

(** val inject_chain_x : 'a1 fchain -> 'a1 Sraw.t -> 'a1 fchain **)

let rec inject_chain_x c s =
  match c with
  | FEmpty -> FFlat (KOnly, bempty, (b1 s), FEmpty)
  | FFlat (k, p, sf, rest) ->
    tree_of_x
      (if bis_empty sf
       then FNode (k, (binject p s), sf)
       else FNode (k, p, (binject sf s)))
      rest
  | FSingle (b, n, rest) ->
    (match b with
     | FHole ->
       tree_of_x
         (let FNode (k, p, suf) = n in
          if bis_empty suf
          then FNode (k, (binject p s), suf)
          else FNode (k, p, (binject suf s)))
         rest
     | FBSingle (hn, b') ->
       let hn' =
         let FNode (k, p, suf) = hn in
         if bis_empty suf
         then FNode (k, (binject p s), suf)
         else FNode (k, p, (binject suf s))
       in
       (match if negb true
              then CG
              else let FNode (k, p, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p) (bsize s0)
                     | KLeft -> bsize p
                     | KRight -> bsize s0
                   in
                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                   then CG
                   else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ 0)))))))
                        then CY
                        else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             then CO
                             else CR with
        | CG ->
          let b0 = FHole in
          (match b0 with
           | FHole ->
             let FNode (k, p, s0) = hn' in
             FFlat (k, p, s0,
             (match b' with
              | FHole ->
                let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
              | _ -> FSingle (b', n, rest)))
           | _ ->
             FSingle (b0, hn',
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest))))
        | CR ->
          let b0 = FHole in
          (match b0 with
           | FHole ->
             let FNode (k, p, s0) = hn' in
             FFlat (k, p, s0,
             (match b' with
              | FHole ->
                let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
              | _ -> FSingle (b', n, rest)))
           | _ ->
             FSingle (b0, hn',
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest))))
        | _ -> FSingle ((FBSingle (hn', b')), n, rest))
     | FBPairY (hn, b', rc) ->
       let hn' =
         let FNode (k, p, suf) = hn in
         if bis_empty suf
         then FNode (k, (binject p s), suf)
         else FNode (k, p, (binject suf s))
       in
       (match if negb true
              then CG
              else let FNode (k, p, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p) (bsize s0)
                     | KLeft -> bsize p
                     | KRight -> bsize s0
                   in
                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                   then CG
                   else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ 0)))))))
                        then CY
                        else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             then CO
                             else CR with
        | CY -> FSingle ((FBPairY (hn', b', rc)), n, rest)
        | CO ->
          (match rc with
           | FFlat (k2, p2, s2, rrest) ->
             FSingle ((FBPairO (hn',
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest)),
               FHole)), (FNode (k2, p2, s2)), rrest)
           | FSingle (rb, rn, rrest) ->
             FSingle ((FBPairO (hn',
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest)),
               rb)), rn, rrest)
           | _ ->
             let b0 = FHole in
             (match b0 with
              | FHole ->
                let FNode (k, p, s0) = hn' in
                FFlat (k, p, s0, (FPair
                ((match b' with
                  | FHole ->
                    let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
                  | _ -> FSingle (b', n, rest)),
                rc)))
              | _ ->
                FSingle (b0, hn', (FPair
                  ((match b' with
                    | FHole ->
                      let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                    | _ -> FSingle (b', n, rest)),
                  rc)))))
        | _ ->
          let b0 = FHole in
          (match b0 with
           | FHole ->
             let FNode (k, p, s0) = hn' in
             FFlat (k, p, s0, (FPair
             ((match b' with
               | FHole ->
                 let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
               | _ -> FSingle (b', n, rest)),
             rc)))
           | _ ->
             FSingle (b0, hn', (FPair
               ((match b' with
                 | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                 | _ -> FSingle (b', n, rest)),
               rc)))))
     | FBPairO (hn, lc, b') ->
       let hn' =
         let FNode (k, p, suf) = hn in
         if bis_empty suf
         then FNode (k, (binject p s), suf)
         else FNode (k, p, (binject suf s))
       in
       (match if negb true
              then CG
              else let FNode (k, p, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p) (bsize s0)
                     | KLeft -> bsize p
                     | KRight -> bsize s0
                   in
                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                   then CG
                   else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ 0)))))))
                        then CY
                        else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             then CO
                             else CR with
        | CY ->
          (match lc with
           | FFlat (k2, p2, s2, lrest) ->
             FSingle ((FBPairY (hn', FHole,
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest)))),
               (FNode (k2, p2, s2)), lrest)
           | FSingle (lb, ln, lrest) ->
             FSingle ((FBPairY (hn', lb,
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest)))),
               ln, lrest)
           | _ ->
             let b0 = FHole in
             (match b0 with
              | FHole ->
                let FNode (k, p, s0) = hn' in
                FFlat (k, p, s0, (FPair (lc,
                (match b' with
                 | FHole ->
                   let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
                 | _ -> FSingle (b', n, rest)))))
              | _ ->
                FSingle (b0, hn', (FPair (lc,
                  (match b' with
                   | FHole ->
                     let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                   | _ -> FSingle (b', n, rest)))))))
        | CO -> FSingle ((FBPairO (hn', lc, b')), n, rest)
        | _ ->
          let b0 = FHole in
          (match b0 with
           | FHole ->
             let FNode (k, p, s0) = hn' in
             FFlat (k, p, s0, (FPair (lc,
             (match b' with
              | FHole ->
                let FNode (k0, p0, s1) = n in FFlat (k0, p0, s1, rest)
              | _ -> FSingle (b', n, rest)))))
           | _ ->
             FSingle (b0, hn', (FPair (lc,
               (match b' with
                | FHole -> let FNode (k, p, s0) = n in FFlat (k, p, s0, rest)
                | _ -> FSingle (b', n, rest))))))))
  | FPair (l, r) -> FPair (l, (inject_chain_x r s))

(** val cad_push_x : 'a1 -> 'a1 fchain -> 'a1 fchain **)

let cad_push_x x d =
  push_chain_x (Sraw.ground x) d

(** val cad_inject_x : 'a1 fchain -> 'a1 -> 'a1 fchain **)

let cad_inject_x d x =
  inject_chain_x d (Sraw.ground x)

(** val degenerate_buf_x : 'a1 fchain -> 'a1 Sraw.t buffer option **)

let degenerate_buf_x = function
| FFlat (k, p, s, f) ->
  (match k with
   | KOnly ->
     (match f with
      | FEmpty ->
        if bis_empty p then Some s else if bis_empty s then Some p else None
      | _ -> None)
   | _ -> None)
| FSingle (f, f0, f1) ->
  (match f with
   | FHole ->
     let FNode (k, p, s) = f0 in
     (match k with
      | KOnly ->
        (match f1 with
         | FEmpty ->
           if bis_empty p
           then Some s
           else if bis_empty s then Some p else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val make_left_only_x :
    'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option **)

let make_left_only_x p1 d1 s1 =
  match d1 with
  | FEmpty ->
    if (<=) (bsize s1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match beject2 s1 with
          | Some p ->
            let (p0, z) = p in
            let (s1', y) = p0 in
            Some (tree_of_x (FNode (KLeft, (bapp p1 s1'), (b2 y z))) FEmpty)
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
                     (tree_of_x (FNode (KLeft, (bapp p1 (b3 a b c)),
                       (b2 y z))) (push_chain_x (Sraw.small smid) FEmpty))
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
       (tree_of_x (FNode (KLeft, p1, (b2 y z)))
         (inject_chain_x d1 (Sraw.small s1')))
     | None -> None)

(** val make_left_x : 'a1 fchain -> 'a1 fchain option **)

let make_left_x d = match d with
| FEmpty -> None
| FPair (l, r) ->
  (match l with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rl) = p0 in
     let (bl, nl) = p1 in
     (match r with
      | FFlat (k0, p2, s0, rest0) ->
        let p3 = ((FHole, (FNode (k0, p2, s0))), rest0) in
        let (p4, rr) = p3 in
        let (br, nr) = p4 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p5, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p6, s2) = f0 in
        (match d1 with
         | FEmpty -> make_left_only_x (bapp p5 (bapp s1 p6)) d2 s2
         | _ ->
           (match beject2 s2 with
            | Some p7 ->
              let (p8, z) = p7 in
              let (s2', y) = p8 in
              Some
              (tree_of_x (FNode (KLeft, p5, (b2 y z)))
                (inject_chain_x d1 (Sraw.big ((bapp s1 p6), d2, s2'))))
            | None -> None))
      | FSingle (b, n, rest0) ->
        let p2 = ((b, n), rest0) in
        let (p3, rr) = p2 in
        let (br, nr) = p3 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p4, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p5, s2) = f0 in
        (match d1 with
         | FEmpty -> make_left_only_x (bapp p4 (bapp s1 p5)) d2 s2
         | _ ->
           (match beject2 s2 with
            | Some p6 ->
              let (p7, z) = p6 in
              let (s2', y) = p7 in
              Some
              (tree_of_x (FNode (KLeft, p4, (b2 y z)))
                (inject_chain_x d1 (Sraw.big ((bapp s1 p5), d2, s2'))))
            | None -> None))
      | _ -> None)
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rl) = p in
     let (bl, nl) = p0 in
     (match r with
      | FFlat (k, p1, s, rest0) ->
        let p2 = ((FHole, (FNode (k, p1, s))), rest0) in
        let (p3, rr) = p2 in
        let (br, nr) = p3 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p4, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p5, s2) = f0 in
        (match d1 with
         | FEmpty -> make_left_only_x (bapp p4 (bapp s1 p5)) d2 s2
         | _ ->
           (match beject2 s2 with
            | Some p6 ->
              let (p7, z) = p6 in
              let (s2', y) = p7 in
              Some
              (tree_of_x (FNode (KLeft, p4, (b2 y z)))
                (inject_chain_x d1 (Sraw.big ((bapp s1 p5), d2, s2'))))
            | None -> None))
      | FSingle (b0, n0, rest0) ->
        let p1 = ((b0, n0), rest0) in
        let (p2, rr) = p1 in
        let (br, nr) = p2 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p3, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p4, s2) = f0 in
        (match d1 with
         | FEmpty -> make_left_only_x (bapp p3 (bapp s1 p4)) d2 s2
         | _ ->
           (match beject2 s2 with
            | Some p5 ->
              let (p6, z) = p5 in
              let (s2', y) = p6 in
              Some
              (tree_of_x (FNode (KLeft, p3, (b2 y z)))
                (inject_chain_x d1 (Sraw.big ((bapp s1 p4), d2, s2'))))
            | None -> None))
      | _ -> None)
   | _ -> None)
| _ ->
  (match d with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rest0) = p0 in
     let (b, n) = p1 in
     let (f, d1) = root_and_child_x b n rest0 in
     let FNode (_, p2, s1) = f in make_left_only_x p2 d1 s1
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rest0) = p in
     let (b0, n0) = p0 in
     let (f, d1) = root_and_child_x b0 n0 rest0 in
     let FNode (_, p1, s1) = f in make_left_only_x p1 d1 s1
   | _ -> None)

(** val make_right_only_x :
    'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option **)

let make_right_only_x p1 d1 s1 =
  match d1 with
  | FEmpty ->
    if (<=) (bsize p1) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0))))))))
    then (match bpop2 p1 with
          | Some p ->
            let (p0, p1') = p in
            let (x, y) = p0 in
            Some (tree_of_x (FNode (KRight, (b2 x y), (bapp p1' s1))) FEmpty)
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
               (tree_of_x (FNode (KRight, (b2 x y), (bapp (b3 a b c) s1)))
                 (push_chain_x (Sraw.small pmid) FEmpty))
             | None -> None)
          | None -> None)
  | _ ->
    (match bpop2 p1 with
     | Some p ->
       let (p0, p1') = p in
       let (x, y) = p0 in
       Some
       (tree_of_x (FNode (KRight, (b2 x y), s1))
         (push_chain_x (Sraw.small p1') d1))
     | None -> None)

(** val make_right_x : 'a1 fchain -> 'a1 fchain option **)

let make_right_x e = match e with
| FEmpty -> None
| FPair (l, r) ->
  (match l with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rl) = p0 in
     let (bl, nl) = p1 in
     (match r with
      | FFlat (k0, p2, s0, rest0) ->
        let p3 = ((FHole, (FNode (k0, p2, s0))), rest0) in
        let (p4, rr) = p3 in
        let (br, nr) = p4 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p5, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p6, s2) = f0 in
        (match d2 with
         | FEmpty -> make_right_only_x p5 d1 (bapp s1 (bapp p6 s2))
         | _ ->
           (match bpop2 p5 with
            | Some p7 ->
              let (p8, p1') = p7 in
              let (x, y) = p8 in
              Some
              (tree_of_x (FNode (KRight, (b2 x y), s2))
                (push_chain_x (Sraw.big (p1', d1, (bapp s1 p6))) d2))
            | None -> None))
      | FSingle (b, n, rest0) ->
        let p2 = ((b, n), rest0) in
        let (p3, rr) = p2 in
        let (br, nr) = p3 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p4, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p5, s2) = f0 in
        (match d2 with
         | FEmpty -> make_right_only_x p4 d1 (bapp s1 (bapp p5 s2))
         | _ ->
           (match bpop2 p4 with
            | Some p6 ->
              let (p7, p1') = p6 in
              let (x, y) = p7 in
              Some
              (tree_of_x (FNode (KRight, (b2 x y), s2))
                (push_chain_x (Sraw.big (p1', d1, (bapp s1 p5))) d2))
            | None -> None))
      | _ -> None)
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rl) = p in
     let (bl, nl) = p0 in
     (match r with
      | FFlat (k, p1, s, rest0) ->
        let p2 = ((FHole, (FNode (k, p1, s))), rest0) in
        let (p3, rr) = p2 in
        let (br, nr) = p3 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p4, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p5, s2) = f0 in
        (match d2 with
         | FEmpty -> make_right_only_x p4 d1 (bapp s1 (bapp p5 s2))
         | _ ->
           (match bpop2 p4 with
            | Some p6 ->
              let (p7, p1') = p6 in
              let (x, y) = p7 in
              Some
              (tree_of_x (FNode (KRight, (b2 x y), s2))
                (push_chain_x (Sraw.big (p1', d1, (bapp s1 p5))) d2))
            | None -> None))
      | FSingle (b0, n0, rest0) ->
        let p1 = ((b0, n0), rest0) in
        let (p2, rr) = p1 in
        let (br, nr) = p2 in
        let (f, d1) = root_and_child_x bl nl rl in
        let FNode (_, p3, s1) = f in
        let (f0, d2) = root_and_child_x br nr rr in
        let FNode (_, p4, s2) = f0 in
        (match d2 with
         | FEmpty -> make_right_only_x p3 d1 (bapp s1 (bapp p4 s2))
         | _ ->
           (match bpop2 p3 with
            | Some p5 ->
              let (p6, p1') = p5 in
              let (x, y) = p6 in
              Some
              (tree_of_x (FNode (KRight, (b2 x y), s2))
                (push_chain_x (Sraw.big (p1', d1, (bapp s1 p4))) d2))
            | None -> None))
      | _ -> None)
   | _ -> None)
| _ ->
  (match e with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rest0) = p0 in
     let (b, n) = p1 in
     let (f, d1) = root_and_child_x b n rest0 in
     let FNode (_, p2, s1) = f in make_right_only_x p2 d1 s1
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rest0) = p in
     let (b0, n0) = p0 in
     let (f, d1) = root_and_child_x b0 n0 rest0 in
     let FNode (_, p1, s1) = f in make_right_only_x p1 d1 s1
   | _ -> None)

(** val concat_small_left_x :
    'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 fchain option **)

let concat_small_left_x p3 e =
  if Nat.ltb (bsize p3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (bfold_right push_chain_x e p3)
  else (match e with
        | FEmpty -> None
        | FPair (l, rt) ->
          (match l with
           | FFlat (k, p, s, rest) ->
             let p0 = ((FHole, (FNode (k, p, s))), rest) in
             let (p1, rl) = p0 in
             let (bl, nl) = p1 in
             let (f, d2) = root_and_child_x bl nl rl in
             let FNode (_, p2, s2) = f in
             Some (FPair
             ((tree_of_x (FNode (KLeft, p3, s2))
                (push_chain_x (Sraw.small p2) d2)),
             rt))
           | FSingle (b, n, rest) ->
             let p = ((b, n), rest) in
             let (p0, rl) = p in
             let (bl, nl) = p0 in
             let (f, d2) = root_and_child_x bl nl rl in
             let FNode (_, p2, s2) = f in
             Some (FPair
             ((tree_of_x (FNode (KLeft, p3, s2))
                (push_chain_x (Sraw.small p2) d2)),
             rt))
           | _ -> None)
        | _ ->
          (match e with
           | FFlat (k, p, s, rest) ->
             let p0 = ((FHole, (FNode (k, p, s))), rest) in
             let (p1, rest0) = p0 in
             let (b, n) = p1 in
             let (f, d2) = root_and_child_x b n rest0 in
             let FNode (_, p2, s2) = f in
             (match d2 with
              | FEmpty ->
                (match beject2 p2 with
                 | Some p4 ->
                   let (p5, z) = p4 in
                   let (p2', y) = p5 in
                   Some
                   (tree_of_x (FNode (KOnly, p3, (bpush y (bpush z s2))))
                     (push_chain_x (Sraw.small p2') FEmpty))
                 | None -> None)
              | _ ->
                Some
                  (tree_of_x (FNode (KOnly, p3, s2))
                    (push_chain_x (Sraw.small p2) d2)))
           | FSingle (b, n, rest) ->
             let p = ((b, n), rest) in
             let (p0, rest0) = p in
             let (b0, n0) = p0 in
             let (f, d2) = root_and_child_x b0 n0 rest0 in
             let FNode (_, p2, s2) = f in
             (match d2 with
              | FEmpty ->
                (match beject2 p2 with
                 | Some p1 ->
                   let (p4, z) = p1 in
                   let (p2', y) = p4 in
                   Some
                   (tree_of_x (FNode (KOnly, p3, (bpush y (bpush z s2))))
                     (push_chain_x (Sraw.small p2') FEmpty))
                 | None -> None)
              | _ ->
                Some
                  (tree_of_x (FNode (KOnly, p3, s2))
                    (push_chain_x (Sraw.small p2) d2)))
           | _ -> None))

(** val concat_small_right_x :
    'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option **)

let concat_small_right_x d s3 =
  if Nat.ltb (bsize s3) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))
  then Some (bfold_left inject_chain_x s3 d)
  else (match d with
        | FEmpty -> None
        | FPair (lt, r) ->
          (match r with
           | FFlat (k, p, s, rest) ->
             let p0 = ((FHole, (FNode (k, p, s))), rest) in
             let (p1, rr) = p0 in
             let (br, nr) = p1 in
             let (f, d1) = root_and_child_x br nr rr in
             let FNode (_, p2, s1) = f in
             Some (FPair (lt,
             (tree_of_x (FNode (KRight, p2, s3))
               (inject_chain_x d1 (Sraw.small s1)))))
           | FSingle (b, n, rest) ->
             let p = ((b, n), rest) in
             let (p0, rr) = p in
             let (br, nr) = p0 in
             let (f, d1) = root_and_child_x br nr rr in
             let FNode (_, p1, s1) = f in
             Some (FPair (lt,
             (tree_of_x (FNode (KRight, p1, s3))
               (inject_chain_x d1 (Sraw.small s1)))))
           | _ -> None)
        | _ ->
          (match d with
           | FFlat (k, p, s, rest) ->
             let p0 = ((FHole, (FNode (k, p, s))), rest) in
             let (p1, rest0) = p0 in
             let (b, n) = p1 in
             let (f, d1) = root_and_child_x b n rest0 in
             let FNode (_, p2, s1) = f in
             (match d1 with
              | FEmpty ->
                (match bpop2 s1 with
                 | Some p3 ->
                   let (p4, s1') = p3 in
                   let (x, y) = p4 in
                   Some
                   (tree_of_x (FNode (KOnly, (binject (binject p2 x) y), s3))
                     (push_chain_x (Sraw.small s1') FEmpty))
                 | None -> None)
              | _ ->
                Some
                  (tree_of_x (FNode (KOnly, p2, s3))
                    (inject_chain_x d1 (Sraw.small s1))))
           | FSingle (b, n, rest) ->
             let p = ((b, n), rest) in
             let (p0, rest0) = p in
             let (b0, n0) = p0 in
             let (f, d1) = root_and_child_x b0 n0 rest0 in
             let FNode (_, p1, s1) = f in
             (match d1 with
              | FEmpty ->
                (match bpop2 s1 with
                 | Some p2 ->
                   let (p3, s1') = p2 in
                   let (x, y) = p3 in
                   Some
                   (tree_of_x (FNode (KOnly, (binject (binject p1 x) y), s3))
                     (push_chain_x (Sraw.small s1') FEmpty))
                 | None -> None)
              | _ ->
                Some
                  (tree_of_x (FNode (KOnly, p1, s3))
                    (inject_chain_x d1 (Sraw.small s1))))
           | _ -> None))

(** val cad_concat_x : 'a1 fchain -> 'a1 fchain -> 'a1 fchain option **)

let cad_concat_x d e =
  match d with
  | FEmpty -> Some e
  | _ ->
    (match e with
     | FEmpty -> Some d
     | _ ->
       (match degenerate_buf_x d with
        | Some p ->
          (match degenerate_buf_x e with
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
             then Some (FFlat (KOnly, (bapp p s), bempty, FEmpty))
             else Some (FFlat (KOnly, p, s, FEmpty))
           | None -> concat_small_left_x p e)
        | None ->
          (match degenerate_buf_x e with
           | Some s -> concat_small_right_x d s
           | None ->
             (match make_left_x d with
              | Some t ->
                (match make_right_x e with
                 | Some u -> Some (FPair (t, u))
                 | None -> None)
              | None -> None))))

(** val pop_raw_x : 'a1 fchain -> ('a1 Sraw.t * 'a1 fchain) option **)

let rec pop_raw_x = function
| FEmpty -> None
| FFlat (k, p, s, rest) ->
  (match bpop p with
   | Some p0 ->
     let (x, p') = p0 in
     let p1 = (x, (FNode (k, p', s))) in
     let (x0, n') = p1 in
     (match rest with
      | FEmpty ->
        Some (x0,
          (let FNode (k0, p2, s0) = n' in
           if (&&) (bis_empty p2) (bis_empty s0)
           then FEmpty
           else (match k0 with
                 | KOnly ->
                   if (||) (bis_empty p2) (bis_empty s0)
                   then FFlat (k0, p2, s0, FEmpty)
                   else if (||)
                             (Nat.ltb (bsize p2) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             (Nat.ltb (bsize s0) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                        then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                        else FFlat (k0, p2, s0, FEmpty)
                 | _ -> FFlat (k0, p2, s0, FEmpty))))
      | _ -> Some (x0, (tree_of_x n' rest)))
   | None ->
     (match bpop s with
      | Some p0 ->
        let (x, s') = p0 in
        let p1 = (x, (FNode (k, p, s'))) in
        let (x0, n') = p1 in
        (match rest with
         | FEmpty ->
           Some (x0,
             (let FNode (k0, p2, s0) = n' in
              if (&&) (bis_empty p2) (bis_empty s0)
              then FEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p2) (bis_empty s0)
                      then FFlat (k0, p2, s0, FEmpty)
                      else if (||)
                                (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                           else FFlat (k0, p2, s0, FEmpty)
                    | _ -> FFlat (k0, p2, s0, FEmpty))))
         | _ -> Some (x0, (tree_of_x n' rest)))
      | None -> None))
| FSingle (b, n, rest) ->
  let (n0, child) = root_and_child_x b n rest in
  let FNode (k, p, s) = n0 in
  (match bpop p with
   | Some p0 ->
     let (x, p') = p0 in
     let p1 = (x, (FNode (k, p', s))) in
     let (x0, n') = p1 in
     (match child with
      | FEmpty ->
        Some (x0,
          (let FNode (k0, p2, s0) = n' in
           if (&&) (bis_empty p2) (bis_empty s0)
           then FEmpty
           else (match k0 with
                 | KOnly ->
                   if (||) (bis_empty p2) (bis_empty s0)
                   then FFlat (k0, p2, s0, FEmpty)
                   else if (||)
                             (Nat.ltb (bsize p2) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             (Nat.ltb (bsize s0) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                        then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                        else FFlat (k0, p2, s0, FEmpty)
                 | _ -> FFlat (k0, p2, s0, FEmpty))))
      | _ -> Some (x0, (tree_of_x n' child)))
   | None ->
     (match bpop s with
      | Some p0 ->
        let (x, s') = p0 in
        let p1 = (x, (FNode (k, p, s'))) in
        let (x0, n') = p1 in
        (match child with
         | FEmpty ->
           Some (x0,
             (let FNode (k0, p2, s0) = n' in
              if (&&) (bis_empty p2) (bis_empty s0)
              then FEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p2) (bis_empty s0)
                      then FFlat (k0, p2, s0, FEmpty)
                      else if (||)
                                (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                           else FFlat (k0, p2, s0, FEmpty)
                    | _ -> FFlat (k0, p2, s0, FEmpty))))
         | _ -> Some (x0, (tree_of_x n' child)))
      | None -> None))
| FPair (l, r) ->
  (match pop_raw_x l with
   | Some p ->
     let (x, l') = p in
     (match l' with
      | FEmpty -> Some (x, r)
      | FFlat (_, lp, ls, f) ->
        (match f with
         | FEmpty ->
           if Nat.ltb (bsize lp) (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
           then (match r with
                 | FFlat (k, p0, s, rest) ->
                   let p1 = ((FHole, (FNode (k, p0, s))), rest) in
                   let (p2, rr) = p1 in
                   let (br, nr) = p2 in
                   let (f0, d2) = root_and_child_x br nr rr in
                   let FNode (_, p3, s2) = f0 in
                   Some (x,
                   (tree_of_x (FNode (KOnly, (bapp lp (bapp ls p3)), s2)) d2))
                 | FSingle (b, n, rest) ->
                   let p0 = ((b, n), rest) in
                   let (p1, rr) = p0 in
                   let (br, nr) = p1 in
                   let (f0, d2) = root_and_child_x br nr rr in
                   let FNode (_, p2, s2) = f0 in
                   Some (x,
                   (tree_of_x (FNode (KOnly, (bapp lp (bapp ls p2)), s2)) d2))
                 | _ -> None)
           else Some (x, (FPair (l', r)))
         | _ -> Some (x, (FPair (l', r))))
      | FSingle (f, f0, f1) ->
        (match f with
         | FHole ->
           let FNode (_, lp, ls) = f0 in
           (match f1 with
            | FEmpty ->
              if Nat.ltb (bsize lp) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match r with
                    | FFlat (k, p0, s, rest) ->
                      let p1 = ((FHole, (FNode (k, p0, s))), rest) in
                      let (p2, rr) = p1 in
                      let (br, nr) = p2 in
                      let (f2, d2) = root_and_child_x br nr rr in
                      let FNode (_, p3, s2) = f2 in
                      Some (x,
                      (tree_of_x (FNode (KOnly, (bapp lp (bapp ls p3)), s2))
                        d2))
                    | FSingle (b, n, rest) ->
                      let p0 = ((b, n), rest) in
                      let (p1, rr) = p0 in
                      let (br, nr) = p1 in
                      let (f2, d2) = root_and_child_x br nr rr in
                      let FNode (_, p2, s2) = f2 in
                      Some (x,
                      (tree_of_x (FNode (KOnly, (bapp lp (bapp ls p2)), s2))
                        d2))
                    | _ -> None)
              else Some (x, (FPair (l', r)))
            | _ -> Some (x, (FPair (l', r))))
         | _ -> Some (x, (FPair (l', r))))
      | FPair (_, _) -> Some (x, (FPair (l', r))))
   | None -> None)

(** val eject_raw_x : 'a1 fchain -> ('a1 fchain * 'a1 Sraw.t) option **)

let rec eject_raw_x = function
| FEmpty -> None
| FFlat (k, p, s, rest) ->
  (match beject s with
   | Some p0 ->
     let (s', x) = p0 in
     let p1 = ((FNode (k, p, s')), x) in
     let (n', x0) = p1 in
     (match rest with
      | FEmpty ->
        Some
          ((let FNode (k0, p2, s0) = n' in
            if (&&) (bis_empty p2) (bis_empty s0)
            then FEmpty
            else (match k0 with
                  | KOnly ->
                    if (||) (bis_empty p2) (bis_empty s0)
                    then FFlat (k0, p2, s0, FEmpty)
                    else if (||)
                              (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                         then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                         else FFlat (k0, p2, s0, FEmpty)
                  | _ -> FFlat (k0, p2, s0, FEmpty))),
          x0)
      | _ -> Some ((tree_of_x n' rest), x0))
   | None ->
     (match beject p with
      | Some p0 ->
        let (p', x) = p0 in
        let p1 = ((FNode (k, p', bempty)), x) in
        let (n', x0) = p1 in
        (match rest with
         | FEmpty ->
           Some
             ((let FNode (k0, p2, s0) = n' in
               if (&&) (bis_empty p2) (bis_empty s0)
               then FEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p2) (bis_empty s0)
                       then FFlat (k0, p2, s0, FEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                            else FFlat (k0, p2, s0, FEmpty)
                     | _ -> FFlat (k0, p2, s0, FEmpty))),
             x0)
         | _ -> Some ((tree_of_x n' rest), x0))
      | None -> None))
| FSingle (b, n, rest) ->
  let (n0, child) = root_and_child_x b n rest in
  let FNode (k, p, s) = n0 in
  (match beject s with
   | Some p0 ->
     let (s', x) = p0 in
     let p1 = ((FNode (k, p, s')), x) in
     let (n', x0) = p1 in
     (match child with
      | FEmpty ->
        Some
          ((let FNode (k0, p2, s0) = n' in
            if (&&) (bis_empty p2) (bis_empty s0)
            then FEmpty
            else (match k0 with
                  | KOnly ->
                    if (||) (bis_empty p2) (bis_empty s0)
                    then FFlat (k0, p2, s0, FEmpty)
                    else if (||)
                              (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                         then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                         else FFlat (k0, p2, s0, FEmpty)
                  | _ -> FFlat (k0, p2, s0, FEmpty))),
          x0)
      | _ -> Some ((tree_of_x n' child), x0))
   | None ->
     (match beject p with
      | Some p0 ->
        let (p', x) = p0 in
        let p1 = ((FNode (k, p', bempty)), x) in
        let (n', x0) = p1 in
        (match child with
         | FEmpty ->
           Some
             ((let FNode (k0, p2, s0) = n' in
               if (&&) (bis_empty p2) (bis_empty s0)
               then FEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p2) (bis_empty s0)
                       then FFlat (k0, p2, s0, FEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                            else FFlat (k0, p2, s0, FEmpty)
                     | _ -> FFlat (k0, p2, s0, FEmpty))),
             x0)
         | _ -> Some ((tree_of_x n' child), x0))
      | None -> None))
| FPair (l, r) ->
  (match eject_raw_x r with
   | Some p ->
     let (r', x) = p in
     (match r' with
      | FEmpty -> Some (l, x)
      | FFlat (_, rp, rs, f) ->
        (match f with
         | FEmpty ->
           if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
           then (match l with
                 | FFlat (k, p0, s, rest) ->
                   let p1 = ((FHole, (FNode (k, p0, s))), rest) in
                   let (p2, rl) = p1 in
                   let (bl, nl) = p2 in
                   let (f0, d1) = root_and_child_x bl nl rl in
                   let FNode (_, p3, s1) = f0 in
                   Some
                   ((tree_of_x (FNode (KOnly, p3, (bapp s1 (bapp rp rs)))) d1),
                   x)
                 | FSingle (b, n, rest) ->
                   let p0 = ((b, n), rest) in
                   let (p1, rl) = p0 in
                   let (bl, nl) = p1 in
                   let (f0, d1) = root_and_child_x bl nl rl in
                   let FNode (_, p2, s1) = f0 in
                   Some
                   ((tree_of_x (FNode (KOnly, p2, (bapp s1 (bapp rp rs)))) d1),
                   x)
                 | _ -> None)
           else Some ((FPair (l, r')), x)
         | _ -> Some ((FPair (l, r')), x))
      | FSingle (f, f0, f1) ->
        (match f with
         | FHole ->
           let FNode (_, rp, rs) = f0 in
           (match f1 with
            | FEmpty ->
              if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
              then (match l with
                    | FFlat (k, p0, s, rest) ->
                      let p1 = ((FHole, (FNode (k, p0, s))), rest) in
                      let (p2, rl) = p1 in
                      let (bl, nl) = p2 in
                      let (f2, d1) = root_and_child_x bl nl rl in
                      let FNode (_, p3, s1) = f2 in
                      Some
                      ((tree_of_x (FNode (KOnly, p3, (bapp s1 (bapp rp rs))))
                         d1),
                      x)
                    | FSingle (b, n, rest) ->
                      let p0 = ((b, n), rest) in
                      let (p1, rl) = p0 in
                      let (bl, nl) = p1 in
                      let (f2, d1) = root_and_child_x bl nl rl in
                      let FNode (_, p2, s1) = f2 in
                      Some
                      ((tree_of_x (FNode (KOnly, p2, (bapp s1 (bapp rp rs))))
                         d1),
                      x)
                    | _ -> None)
              else Some ((FPair (l, r')), x)
            | _ -> Some ((FPair (l, r')), x))
         | _ -> Some ((FPair (l, r')), x))
      | FPair (_, _) -> Some ((FPair (l, r')), x))
   | None -> None)

(** val repair_front_x :
    kind -> 'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain
    -> 'a1 fchain option **)

let repair_front_x k body p1 s1 rest =
  match pop_raw_x rest with
  | Some p ->
    let (cell, d1') = p in
    cell_case_struct cell (fun b -> Some
      (match body with
       | FHole -> let p0 = bapp p1 b in FFlat (k, p0, s1, d1')
       | _ -> FSingle (body, (FNode (k, (bapp p1 b), s1)), d1')))
      (fun p2 d2 s2 ->
      match cad_concat_x d2 (push_chain_x (Sraw.small s2) d1') with
      | Some d3 ->
        Some
          (match body with
           | FHole -> let p0 = bapp p1 p2 in FFlat (k, p0, s1, d3)
           | _ -> FSingle (body, (FNode (k, (bapp p1 p2), s1)), d3))
      | None -> None) None
  | None -> None

(** val repair_back_x :
    kind -> 'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain
    -> 'a1 fchain option **)

let repair_back_x k body p1 s1 rest =
  match eject_raw_x rest with
  | Some p ->
    let (d1', cell) = p in
    cell_case_struct cell (fun b -> Some
      (match body with
       | FHole -> let s = bapp b s1 in FFlat (k, p1, s, d1')
       | _ -> FSingle (body, (FNode (k, p1, (bapp b s1))), d1')))
      (fun p2 d2 s2 ->
      match cad_concat_x (inject_chain_x d1' (Sraw.small p2)) d2 with
      | Some d3 ->
        Some
          (match body with
           | FHole -> let s = bapp s2 s1 in FFlat (k, p1, s, d3)
           | _ -> FSingle (body, (FNode (k, p1, (bapp s2 s1))), d3))
      | None -> None) None
  | None -> None

(** val drain_both_x :
    'a1 fchain -> (('a1 Sraw.t * 'a1 Sraw.t option) * 'a1 fchain) option **)

let drain_both_x rest = match rest with
| FEmpty -> None
| FPair (l, r) ->
  (match pop_raw_x l with
   | Some p ->
     let (cellF, l') = p in
     (match eject_raw_x r with
      | Some p0 ->
        let (r', cellB) = p0 in
        (match l' with
         | FFlat (_, lp, ls, f) ->
           (match f with
            | FEmpty ->
              let p1 = (lp, ls) in
              let (lp0, ls0) = p1 in
              (match r' with
               | FFlat (_, lp1, ls1, f0) ->
                 (match f0 with
                  | FEmpty ->
                    let p2 = (lp1, ls1) in
                    let (rp, rs) = p2 in
                    if (||)
                         (Nat.ltb (bsize lp0) (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ 0))))))
                         (Nat.ltb (bsize rs) (Stdlib.Int.succ
                           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                           (Stdlib.Int.succ 0))))))
                    then Some ((cellF, (Some cellB)), (FFlat (KOnly,
                           (bapp lp0 ls0), (bapp rp rs), FEmpty)))
                    else Some ((cellF, (Some cellB)), (FPair (l', r')))
                  | _ ->
                    if Nat.ltb (bsize lp0) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match r' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rr) = p3 in
                            let (br, nr) = p4 in
                            let (f1, d2) = root_and_child_x br nr rr in
                            let FNode (_, p5, s2) = f1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p5)), s2)) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rr) = p2 in
                            let (br, nr) = p3 in
                            let (f1, d2) = root_and_child_x br nr rr in
                            let FNode (_, p4, s2) = f1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p4)), s2)) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | FSingle (f0, f1, f2) ->
                 (match f0 with
                  | FHole ->
                    let FNode (_, lp1, ls1) = f1 in
                    (match f2 with
                     | FEmpty ->
                       let p2 = (lp1, ls1) in
                       let (rp, rs) = p2 in
                       if (||)
                            (Nat.ltb (bsize lp0) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            (Nat.ltb (bsize rs) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                       then Some ((cellF, (Some cellB)), (FFlat (KOnly,
                              (bapp lp0 ls0), (bapp rp rs), FEmpty)))
                       else Some ((cellF, (Some cellB)), (FPair (l', r')))
                     | _ ->
                       if Nat.ltb (bsize lp0) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match r' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rr) = p3 in
                               let (br, nr) = p4 in
                               let (f3, d2) = root_and_child_x br nr rr in
                               let FNode (_, p5, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p5)), s2)) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rr) = p2 in
                               let (br, nr) = p3 in
                               let (f3, d2) = root_and_child_x br nr rr in
                               let FNode (_, p4, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p4)), s2)) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | _ ->
                    if Nat.ltb (bsize lp0) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match r' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rr) = p3 in
                            let (br, nr) = p4 in
                            let (f3, d2) = root_and_child_x br nr rr in
                            let FNode (_, p5, s2) = f3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p5)), s2)) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rr) = p2 in
                            let (br, nr) = p3 in
                            let (f3, d2) = root_and_child_x br nr rr in
                            let FNode (_, p4, s2) = f3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p4)), s2)) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | _ ->
                 if Nat.ltb (bsize lp0) (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0)))))
                 then (match r' with
                       | FFlat (k, p2, s, rest0) ->
                         let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                         let (p4, rr) = p3 in
                         let (br, nr) = p4 in
                         let (f0, d2) = root_and_child_x br nr rr in
                         let FNode (_, p5, s2) = f0 in
                         Some ((cellF, (Some cellB)),
                         (tree_of_x (FNode (KOnly, (bapp lp0 (bapp ls0 p5)),
                           s2)) d2))
                       | FSingle (b, n, rest0) ->
                         let p2 = ((b, n), rest0) in
                         let (p3, rr) = p2 in
                         let (br, nr) = p3 in
                         let (f0, d2) = root_and_child_x br nr rr in
                         let FNode (_, p4, s2) = f0 in
                         Some ((cellF, (Some cellB)),
                         (tree_of_x (FNode (KOnly, (bapp lp0 (bapp ls0 p4)),
                           s2)) d2))
                       | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                 else Some ((cellF, (Some cellB)), (FPair (l', r'))))
            | _ ->
              (match r' with
               | FFlat (_, lp0, ls0, f0) ->
                 (match f0 with
                  | FEmpty ->
                    let p1 = (lp0, ls0) in
                    let (rp, rs) = p1 in
                    if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match l' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rl) = p3 in
                            let (bl, nl) = p4 in
                            let (f1, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p5, s2) = f1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p5,
                              (bapp s2 (bapp rp rs)))) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rl) = p2 in
                            let (bl, nl) = p3 in
                            let (f1, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p4, s2) = f1 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p4,
                              (bapp s2 (bapp rp rs)))) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r')))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | FSingle (f0, f1, f2) ->
                 (match f0 with
                  | FHole ->
                    let FNode (_, lp0, ls0) = f1 in
                    (match f2 with
                     | FEmpty ->
                       let p1 = (lp0, ls0) in
                       let (rp, rs) = p1 in
                       if Nat.ltb (bsize rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match l' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rl) = p3 in
                               let (bl, nl) = p4 in
                               let (f3, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p5, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p5,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rl) = p2 in
                               let (bl, nl) = p3 in
                               let (f3, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p4, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p4,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (FPair (l', r')))))
         | FSingle (f, f0, f1) ->
           (match f with
            | FHole ->
              let FNode (_, lp, ls) = f0 in
              (match f1 with
               | FEmpty ->
                 let p1 = (lp, ls) in
                 let (lp0, ls0) = p1 in
                 (match r' with
                  | FFlat (_, lp1, ls1, f2) ->
                    (match f2 with
                     | FEmpty ->
                       let p2 = (lp1, ls1) in
                       let (rp, rs) = p2 in
                       if (||)
                            (Nat.ltb (bsize lp0) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            (Nat.ltb (bsize rs) (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ
                              (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                       then Some ((cellF, (Some cellB)), (FFlat (KOnly,
                              (bapp lp0 ls0), (bapp rp rs), FEmpty)))
                       else Some ((cellF, (Some cellB)), (FPair (l', r')))
                     | _ ->
                       if Nat.ltb (bsize lp0) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match r' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rr) = p3 in
                               let (br, nr) = p4 in
                               let (f3, d2) = root_and_child_x br nr rr in
                               let FNode (_, p5, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p5)), s2)) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rr) = p2 in
                               let (br, nr) = p3 in
                               let (f3, d2) = root_and_child_x br nr rr in
                               let FNode (_, p4, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p4)), s2)) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | FSingle (f2, f3, f4) ->
                    (match f2 with
                     | FHole ->
                       let FNode (_, lp1, ls1) = f3 in
                       (match f4 with
                        | FEmpty ->
                          let p2 = (lp1, ls1) in
                          let (rp, rs) = p2 in
                          if (||)
                               (Nat.ltb (bsize lp0) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                               (Nat.ltb (bsize rs) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                          then Some ((cellF, (Some cellB)), (FFlat (KOnly,
                                 (bapp lp0 ls0), (bapp rp rs), FEmpty)))
                          else Some ((cellF, (Some cellB)), (FPair (l', r')))
                        | _ ->
                          if Nat.ltb (bsize lp0) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then (match r' with
                                | FFlat (k, p2, s, rest0) ->
                                  let p3 = ((FHole, (FNode (k, p2, s))),
                                    rest0)
                                  in
                                  let (p4, rr) = p3 in
                                  let (br, nr) = p4 in
                                  let (f5, d2) = root_and_child_x br nr rr in
                                  let FNode (_, p5, s2) = f5 in
                                  Some ((cellF, (Some cellB)),
                                  (tree_of_x (FNode (KOnly,
                                    (bapp lp0 (bapp ls0 p5)), s2)) d2))
                                | FSingle (b, n, rest0) ->
                                  let p2 = ((b, n), rest0) in
                                  let (p3, rr) = p2 in
                                  let (br, nr) = p3 in
                                  let (f5, d2) = root_and_child_x br nr rr in
                                  let FNode (_, p4, s2) = f5 in
                                  Some ((cellF, (Some cellB)),
                                  (tree_of_x (FNode (KOnly,
                                    (bapp lp0 (bapp ls0 p4)), s2)) d2))
                                | _ ->
                                  Some ((cellF, (Some cellB)), (FPair (l',
                                    r'))))
                          else Some ((cellF, (Some cellB)), (FPair (l', r'))))
                     | _ ->
                       if Nat.ltb (bsize lp0) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match r' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rr) = p3 in
                               let (br, nr) = p4 in
                               let (f5, d2) = root_and_child_x br nr rr in
                               let FNode (_, p5, s2) = f5 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p5)), s2)) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rr) = p2 in
                               let (br, nr) = p3 in
                               let (f5, d2) = root_and_child_x br nr rr in
                               let FNode (_, p4, s2) = f5 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly,
                                 (bapp lp0 (bapp ls0 p4)), s2)) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | _ ->
                    if Nat.ltb (bsize lp0) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match r' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rr) = p3 in
                            let (br, nr) = p4 in
                            let (f2, d2) = root_and_child_x br nr rr in
                            let FNode (_, p5, s2) = f2 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p5)), s2)) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rr) = p2 in
                            let (br, nr) = p3 in
                            let (f2, d2) = root_and_child_x br nr rr in
                            let FNode (_, p4, s2) = f2 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly,
                              (bapp lp0 (bapp ls0 p4)), s2)) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | _ ->
                 (match r' with
                  | FFlat (_, lp0, ls0, f2) ->
                    (match f2 with
                     | FEmpty ->
                       let p1 = (lp0, ls0) in
                       let (rp, rs) = p1 in
                       if Nat.ltb (bsize rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match l' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rl) = p3 in
                               let (bl, nl) = p4 in
                               let (f3, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p5, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p5,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rl) = p2 in
                               let (bl, nl) = p3 in
                               let (f3, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p4, s2) = f3 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p4,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | FSingle (f2, f3, f4) ->
                    (match f2 with
                     | FHole ->
                       let FNode (_, lp0, ls0) = f3 in
                       (match f4 with
                        | FEmpty ->
                          let p1 = (lp0, ls0) in
                          let (rp, rs) = p1 in
                          if Nat.ltb (bsize rs) (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                          then (match l' with
                                | FFlat (k, p2, s, rest0) ->
                                  let p3 = ((FHole, (FNode (k, p2, s))),
                                    rest0)
                                  in
                                  let (p4, rl) = p3 in
                                  let (bl, nl) = p4 in
                                  let (f5, d2) = root_and_child_x bl nl rl in
                                  let FNode (_, p5, s2) = f5 in
                                  Some ((cellF, (Some cellB)),
                                  (tree_of_x (FNode (KOnly, p5,
                                    (bapp s2 (bapp rp rs)))) d2))
                                | FSingle (b, n, rest0) ->
                                  let p2 = ((b, n), rest0) in
                                  let (p3, rl) = p2 in
                                  let (bl, nl) = p3 in
                                  let (f5, d2) = root_and_child_x bl nl rl in
                                  let FNode (_, p4, s2) = f5 in
                                  Some ((cellF, (Some cellB)),
                                  (tree_of_x (FNode (KOnly, p4,
                                    (bapp s2 (bapp rp rs)))) d2))
                                | _ ->
                                  Some ((cellF, (Some cellB)), (FPair (l',
                                    r'))))
                          else Some ((cellF, (Some cellB)), (FPair (l', r')))
                        | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                     | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r')))))
            | _ ->
              (match r' with
               | FFlat (_, lp, ls, f2) ->
                 (match f2 with
                  | FEmpty ->
                    let p1 = (lp, ls) in
                    let (rp, rs) = p1 in
                    if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match l' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rl) = p3 in
                            let (bl, nl) = p4 in
                            let (f3, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p5, s2) = f3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p5,
                              (bapp s2 (bapp rp rs)))) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rl) = p2 in
                            let (bl, nl) = p3 in
                            let (f3, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p4, s2) = f3 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p4,
                              (bapp s2 (bapp rp rs)))) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r')))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | FSingle (f2, f3, f4) ->
                 (match f2 with
                  | FHole ->
                    let FNode (_, lp, ls) = f3 in
                    (match f4 with
                     | FEmpty ->
                       let p1 = (lp, ls) in
                       let (rp, rs) = p1 in
                       if Nat.ltb (bsize rs) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then (match l' with
                             | FFlat (k, p2, s, rest0) ->
                               let p3 = ((FHole, (FNode (k, p2, s))), rest0)
                               in
                               let (p4, rl) = p3 in
                               let (bl, nl) = p4 in
                               let (f5, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p5, s2) = f5 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p5,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | FSingle (b, n, rest0) ->
                               let p2 = ((b, n), rest0) in
                               let (p3, rl) = p2 in
                               let (bl, nl) = p3 in
                               let (f5, d2) = root_and_child_x bl nl rl in
                               let FNode (_, p4, s2) = f5 in
                               Some ((cellF, (Some cellB)),
                               (tree_of_x (FNode (KOnly, p4,
                                 (bapp s2 (bapp rp rs)))) d2))
                             | _ ->
                               Some ((cellF, (Some cellB)), (FPair (l', r'))))
                       else Some ((cellF, (Some cellB)), (FPair (l', r')))
                     | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (FPair (l', r')))))
         | _ ->
           (match r' with
            | FFlat (_, lp, ls, f) ->
              (match f with
               | FEmpty ->
                 let p1 = (lp, ls) in
                 let (rp, rs) = p1 in
                 if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      0)))))
                 then (match l' with
                       | FFlat (k, p2, s, rest0) ->
                         let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                         let (p4, rl) = p3 in
                         let (bl, nl) = p4 in
                         let (f0, d2) = root_and_child_x bl nl rl in
                         let FNode (_, p5, s2) = f0 in
                         Some ((cellF, (Some cellB)),
                         (tree_of_x (FNode (KOnly, p5,
                           (bapp s2 (bapp rp rs)))) d2))
                       | FSingle (b, n, rest0) ->
                         let p2 = ((b, n), rest0) in
                         let (p3, rl) = p2 in
                         let (bl, nl) = p3 in
                         let (f0, d2) = root_and_child_x bl nl rl in
                         let FNode (_, p4, s2) = f0 in
                         Some ((cellF, (Some cellB)),
                         (tree_of_x (FNode (KOnly, p4,
                           (bapp s2 (bapp rp rs)))) d2))
                       | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
                 else Some ((cellF, (Some cellB)), (FPair (l', r')))
               | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
            | FSingle (f, f0, f1) ->
              (match f with
               | FHole ->
                 let FNode (_, lp, ls) = f0 in
                 (match f1 with
                  | FEmpty ->
                    let p1 = (lp, ls) in
                    let (rp, rs) = p1 in
                    if Nat.ltb (bsize rs) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))
                    then (match l' with
                          | FFlat (k, p2, s, rest0) ->
                            let p3 = ((FHole, (FNode (k, p2, s))), rest0) in
                            let (p4, rl) = p3 in
                            let (bl, nl) = p4 in
                            let (f2, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p5, s2) = f2 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p5,
                              (bapp s2 (bapp rp rs)))) d2))
                          | FSingle (b, n, rest0) ->
                            let p2 = ((b, n), rest0) in
                            let (p3, rl) = p2 in
                            let (bl, nl) = p3 in
                            let (f2, d2) = root_and_child_x bl nl rl in
                            let FNode (_, p4, s2) = f2 in
                            Some ((cellF, (Some cellB)),
                            (tree_of_x (FNode (KOnly, p4,
                              (bapp s2 (bapp rp rs)))) d2))
                          | _ ->
                            Some ((cellF, (Some cellB)), (FPair (l', r'))))
                    else Some ((cellF, (Some cellB)), (FPair (l', r')))
                  | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
               | _ -> Some ((cellF, (Some cellB)), (FPair (l', r'))))
            | _ -> Some ((cellF, (Some cellB)), (FPair (l', r')))))
      | None -> None)
   | None -> None)
| _ ->
  (match rest with
   | FFlat (k, p, s, rest0) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest0) in
     let (p1, r0) = p0 in
     let (b, n) = p1 in
     let (n0, dd) = root_and_child_x b n r0 in
     let FNode (k0, p2, s0) = n0 in
     (match bpop p2 with
      | Some p3 ->
        let (x, p') = p3 in
        let p4 = (x, (FNode (k0, p', s0))) in
        let (cellF, n1) = p4 in
        let FNode (k1, p5, s1) = n1 in
        (match beject s1 with
         | Some p6 ->
           let (s', x0) = p6 in
           let p7 = ((FNode (k1, p5, s')), x0) in
           let (n2, cellB) = p7 in
           (match dd with
            | FEmpty ->
              Some ((cellF, (Some cellB)),
                (let FNode (k2, p8, s2) = n2 in
                 if (&&) (bis_empty p8) (bis_empty s2)
                 then FEmpty
                 else (match k2 with
                       | KOnly ->
                         if (||) (bis_empty p8) (bis_empty s2)
                         then FFlat (k2, p8, s2, FEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p8) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s2) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then FFlat (KOnly, (bapp p8 s2), bempty, FEmpty)
                              else FFlat (k2, p8, s2, FEmpty)
                       | _ -> FFlat (k2, p8, s2, FEmpty))))
            | _ -> Some ((cellF, (Some cellB)), (tree_of_x n2 dd)))
         | None ->
           (match beject p5 with
            | Some p6 ->
              let (p'0, x0) = p6 in
              let p7 = ((FNode (k1, p'0, bempty)), x0) in
              let (n2, cellB) = p7 in
              (match dd with
               | FEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let FNode (k2, p8, s2) = n2 in
                    if (&&) (bis_empty p8) (bis_empty s2)
                    then FEmpty
                    else (match k2 with
                          | KOnly ->
                            if (||) (bis_empty p8) (bis_empty s2)
                            then FFlat (k2, p8, s2, FEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p8) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s2) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then FFlat (KOnly, (bapp p8 s2), bempty,
                                        FEmpty)
                                 else FFlat (k2, p8, s2, FEmpty)
                          | _ -> FFlat (k2, p8, s2, FEmpty))))
               | _ -> Some ((cellF, (Some cellB)), (tree_of_x n2 dd)))
            | None ->
              (match dd with
               | FEmpty -> Some ((cellF, None), FEmpty)
               | _ -> None)))
      | None ->
        (match bpop s0 with
         | Some p3 ->
           let (x, s') = p3 in
           let p4 = (x, (FNode (k0, p2, s'))) in
           let (cellF, n1) = p4 in
           let FNode (k1, p5, s1) = n1 in
           (match beject s1 with
            | Some p6 ->
              let (s'0, x0) = p6 in
              let p7 = ((FNode (k1, p5, s'0)), x0) in
              let (n2, cellB) = p7 in
              (match dd with
               | FEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let FNode (k2, p8, s2) = n2 in
                    if (&&) (bis_empty p8) (bis_empty s2)
                    then FEmpty
                    else (match k2 with
                          | KOnly ->
                            if (||) (bis_empty p8) (bis_empty s2)
                            then FFlat (k2, p8, s2, FEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p8) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s2) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then FFlat (KOnly, (bapp p8 s2), bempty,
                                        FEmpty)
                                 else FFlat (k2, p8, s2, FEmpty)
                          | _ -> FFlat (k2, p8, s2, FEmpty))))
               | _ -> Some ((cellF, (Some cellB)), (tree_of_x n2 dd)))
            | None ->
              (match beject p5 with
               | Some p6 ->
                 let (p', x0) = p6 in
                 let p7 = ((FNode (k1, p', bempty)), x0) in
                 let (n2, cellB) = p7 in
                 (match dd with
                  | FEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let FNode (k2, p8, s2) = n2 in
                       if (&&) (bis_empty p8) (bis_empty s2)
                       then FEmpty
                       else (match k2 with
                             | KOnly ->
                               if (||) (bis_empty p8) (bis_empty s2)
                               then FFlat (k2, p8, s2, FEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p8) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s2) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then FFlat (KOnly, (bapp p8 s2), bempty,
                                           FEmpty)
                                    else FFlat (k2, p8, s2, FEmpty)
                             | _ -> FFlat (k2, p8, s2, FEmpty))))
                  | _ -> Some ((cellF, (Some cellB)), (tree_of_x n2 dd)))
               | None ->
                 (match dd with
                  | FEmpty -> Some ((cellF, None), FEmpty)
                  | _ -> None)))
         | None -> None))
   | FSingle (b, n, rest0) ->
     let p = ((b, n), rest0) in
     let (p0, r0) = p in
     let (b0, n0) = p0 in
     let (n1, dd) = root_and_child_x b0 n0 r0 in
     let FNode (k, p1, s) = n1 in
     (match bpop p1 with
      | Some p2 ->
        let (x, p') = p2 in
        let p3 = (x, (FNode (k, p', s))) in
        let (cellF, n2) = p3 in
        let FNode (k0, p4, s0) = n2 in
        (match beject s0 with
         | Some p5 ->
           let (s', x0) = p5 in
           let p6 = ((FNode (k0, p4, s')), x0) in
           let (n3, cellB) = p6 in
           (match dd with
            | FEmpty ->
              Some ((cellF, (Some cellB)),
                (let FNode (k1, p7, s1) = n3 in
                 if (&&) (bis_empty p7) (bis_empty s1)
                 then FEmpty
                 else (match k1 with
                       | KOnly ->
                         if (||) (bis_empty p7) (bis_empty s1)
                         then FFlat (k1, p7, s1, FEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p7) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then FFlat (KOnly, (bapp p7 s1), bempty, FEmpty)
                              else FFlat (k1, p7, s1, FEmpty)
                       | _ -> FFlat (k1, p7, s1, FEmpty))))
            | _ -> Some ((cellF, (Some cellB)), (tree_of_x n3 dd)))
         | None ->
           (match beject p4 with
            | Some p5 ->
              let (p'0, x0) = p5 in
              let p6 = ((FNode (k0, p'0, bempty)), x0) in
              let (n3, cellB) = p6 in
              (match dd with
               | FEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let FNode (k1, p7, s1) = n3 in
                    if (&&) (bis_empty p7) (bis_empty s1)
                    then FEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p7) (bis_empty s1)
                            then FFlat (k1, p7, s1, FEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p7) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then FFlat (KOnly, (bapp p7 s1), bempty,
                                        FEmpty)
                                 else FFlat (k1, p7, s1, FEmpty)
                          | _ -> FFlat (k1, p7, s1, FEmpty))))
               | _ -> Some ((cellF, (Some cellB)), (tree_of_x n3 dd)))
            | None ->
              (match dd with
               | FEmpty -> Some ((cellF, None), FEmpty)
               | _ -> None)))
      | None ->
        (match bpop s with
         | Some p2 ->
           let (x, s') = p2 in
           let p3 = (x, (FNode (k, p1, s'))) in
           let (cellF, n2) = p3 in
           let FNode (k0, p4, s0) = n2 in
           (match beject s0 with
            | Some p5 ->
              let (s'0, x0) = p5 in
              let p6 = ((FNode (k0, p4, s'0)), x0) in
              let (n3, cellB) = p6 in
              (match dd with
               | FEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let FNode (k1, p7, s1) = n3 in
                    if (&&) (bis_empty p7) (bis_empty s1)
                    then FEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p7) (bis_empty s1)
                            then FFlat (k1, p7, s1, FEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p7) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then FFlat (KOnly, (bapp p7 s1), bempty,
                                        FEmpty)
                                 else FFlat (k1, p7, s1, FEmpty)
                          | _ -> FFlat (k1, p7, s1, FEmpty))))
               | _ -> Some ((cellF, (Some cellB)), (tree_of_x n3 dd)))
            | None ->
              (match beject p4 with
               | Some p5 ->
                 let (p', x0) = p5 in
                 let p6 = ((FNode (k0, p', bempty)), x0) in
                 let (n3, cellB) = p6 in
                 (match dd with
                  | FEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let FNode (k1, p7, s1) = n3 in
                       if (&&) (bis_empty p7) (bis_empty s1)
                       then FEmpty
                       else (match k1 with
                             | KOnly ->
                               if (||) (bis_empty p7) (bis_empty s1)
                               then FFlat (k1, p7, s1, FEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p7) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then FFlat (KOnly, (bapp p7 s1), bempty,
                                           FEmpty)
                                    else FFlat (k1, p7, s1, FEmpty)
                             | _ -> FFlat (k1, p7, s1, FEmpty))))
                  | _ -> Some ((cellF, (Some cellB)), (tree_of_x n3 dd)))
               | None ->
                 (match dd with
                  | FEmpty -> Some ((cellF, None), FEmpty)
                  | _ -> None)))
         | None -> None))
   | _ -> None)

(** val repair_both_x :
    'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain -> 'a1
    fchain option **)

let repair_both_x body p1 s1 rest =
  match drain_both_x rest with
  | Some p ->
    let (p0, mid) = p in
    let (cellF, o) = p0 in
    (match o with
     | Some cellB ->
       let front =
         cell_case_struct cellF (fun b -> Some (b, mid)) (fun p2 d2 s2 ->
           match cad_concat_x d2 (push_chain_x (Sraw.small s2) mid) with
           | Some d4 -> Some (p2, d4)
           | None -> None) None
       in
       (match front with
        | Some p2 ->
          let (pf, d4) = p2 in
          cell_case_struct cellB (fun b -> Some
            (match body with
             | FHole ->
               let k = KOnly in
               let p3 = bapp p1 pf in
               let s = bapp b s1 in FFlat (k, p3, s, d4)
             | _ ->
               FSingle (body, (FNode (KOnly, (bapp p1 pf), (bapp b s1))), d4)))
            (fun p3 d3 s3 ->
            match cad_concat_x (inject_chain_x d4 (Sraw.small p3)) d3 with
            | Some d5 ->
              Some
                (match body with
                 | FHole ->
                   let k = KOnly in
                   let p4 = bapp p1 pf in
                   let s = bapp s3 s1 in FFlat (k, p4, s, d5)
                 | _ ->
                   FSingle (body, (FNode (KOnly, (bapp p1 pf),
                     (bapp s3 s1))), d5))
            | None -> None) None
        | None -> None)
     | None ->
       cell_case_struct cellF (fun b -> Some
         (match body with
          | FHole ->
            let k = KOnly in let p2 = bapp p1 b in FFlat (k, p2, s1, FEmpty)
          | _ -> FSingle (body, (FNode (KOnly, (bapp p1 b), s1)), FEmpty)))
         (fun p2 d2 s2 -> Some
         (match body with
          | FHole ->
            let k = KOnly in
            let p3 = bapp p1 p2 in let s = bapp s2 s1 in FFlat (k, p3, s, d2)
          | _ ->
            FSingle (body, (FNode (KOnly, (bapp p1 p2), (bapp s2 s1))), d2)))
         None)
  | None -> None

(** val repair_packet_x :
    'a1 fbody -> 'a1 fnode -> 'a1 fchain -> 'a1 fchain option **)

let repair_packet_x body n rest =
  match if negb (match rest with
                 | FEmpty -> false
                 | _ -> true)
        then CG
        else let FNode (k, p, s) = n in
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
                  else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                       then CO
                       else CR with
  | CR ->
    let FNode (k, p1, s1) = n in
    (match k with
     | KOnly ->
       if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (bsize s1)
       then repair_front_x KOnly body p1 s1 rest
       else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) (bsize p1)
            then repair_back_x KOnly body p1 s1 rest
            else repair_both_x body p1 s1 rest
     | KLeft -> repair_front_x KLeft body p1 s1 rest
     | KRight -> repair_back_x KRight body p1 s1 rest)
  | _ ->
    Some
      (match body with
       | FHole -> let FNode (k, p, s) = n in FFlat (k, p, s, rest)
       | _ -> FSingle (body, n, rest))

(** val repair_pop_side_x : 'a1 fchain -> 'a1 fchain option **)

let repair_pop_side_x = function
| FEmpty -> Some FEmpty
| FFlat (k, p, s, rest) -> repair_packet_x FHole (FNode (k, p, s)) rest
| FSingle (b, n, rest) -> repair_packet_x b n rest
| FPair (l, r) ->
  (match l with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rl) = p0 in
     let (bl, nl) = p1 in
     (match repair_packet_x bl nl rl with
      | Some l' -> Some (FPair (l', r))
      | None -> None)
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rl) = p in
     let (bl, nl) = p0 in
     (match repair_packet_x bl nl rl with
      | Some l' -> Some (FPair (l', r))
      | None -> None)
   | _ -> None)

(** val repair_eject_side_x : 'a1 fchain -> 'a1 fchain option **)

let repair_eject_side_x = function
| FEmpty -> Some FEmpty
| FFlat (k, p, s, rest) -> repair_packet_x FHole (FNode (k, p, s)) rest
| FSingle (b, n, rest) -> repair_packet_x b n rest
| FPair (l, r) ->
  (match r with
   | FFlat (k, p, s, rest) ->
     let p0 = ((FHole, (FNode (k, p, s))), rest) in
     let (p1, rr) = p0 in
     let (br, nr) = p1 in
     (match repair_packet_x br nr rr with
      | Some r' -> Some (FPair (l, r'))
      | None -> None)
   | FSingle (b, n, rest) ->
     let p = ((b, n), rest) in
     let (p0, rr) = p in
     let (br, nr) = p0 in
     (match repair_packet_x br nr rr with
      | Some r' -> Some (FPair (l, r'))
      | None -> None)
   | _ -> None)

(** val cad_pop_x : 'a1 fchain -> ('a1 * 'a1 fchain) option **)

let cad_pop_x d = match d with
| FEmpty -> None
| FFlat (k, p, s, rest) ->
  (match bpop p with
   | Some p0 ->
     let (x, p') = p0 in
     let p1 = (x, (FNode (k, p', s))) in
     let (cell, n') = p1 in
     cell_case_ground cell (fun a ->
       match rest with
       | FEmpty ->
         Some (a,
           (let FNode (k0, p2, s0) = n' in
            if (&&) (bis_empty p2) (bis_empty s0)
            then FEmpty
            else (match k0 with
                  | KOnly ->
                    if (||) (bis_empty p2) (bis_empty s0)
                    then FFlat (k0, p2, s0, FEmpty)
                    else if (||)
                              (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                         then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                         else FFlat (k0, p2, s0, FEmpty)
                  | _ -> FFlat (k0, p2, s0, FEmpty))))
       | _ ->
         (match match if negb (match rest with
                               | FEmpty -> false
                               | _ -> true)
                      then CG
                      else let FNode (k0, p2, s0) = n' in
                           let m =
                             match k0 with
                             | KOnly -> Nat.min (bsize p2) (bsize s0)
                             | KLeft -> bsize p2
                             | KRight -> bsize s0
                           in
                           if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                           then CG
                           else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ 0)))))))
                                then CY
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                     then CO
                                     else CR with
                | CG ->
                  Some
                    (let b = FHole in
                     match b with
                     | FHole ->
                       let FNode (k0, p2, s0) = n' in FFlat (k0, p2, s0, rest)
                     | _ -> FSingle (b, n', rest))
                | CY ->
                  (match rest with
                   | FEmpty ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (f, rr) ->
                     (match f with
                      | FFlat (k2, p2, s2, lrest) ->
                        repair_packet_x (FBPairY (n', FHole, rr)) (FNode (k2,
                          p2, s2)) lrest
                      | FSingle (lb, ln, lrest) ->
                        repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                      | _ ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))))
                | CO ->
                  (match rest with
                   | FEmpty ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (ll, f) ->
                     (match f with
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBPairO (n', ll, FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                      | _ ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))))
                | CR ->
                  let FNode (k0, p2, s1) = n' in
                  (match k0 with
                   | KOnly ->
                     if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))) (bsize s1)
                     then repair_front_x KOnly FHole p2 s1 rest
                     else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize p2)
                          then repair_back_x KOnly FHole p2 s1 rest
                          else repair_both_x FHole p2 s1 rest
                   | KLeft -> repair_front_x KLeft FHole p2 s1 rest
                   | KRight -> repair_back_x KRight FHole p2 s1 rest) with
          | Some d'' -> Some (a, d'')
          | None -> None))
       None
   | None ->
     (match bpop s with
      | Some p0 ->
        let (x, s') = p0 in
        let p1 = (x, (FNode (k, p, s'))) in
        let (cell, n') = p1 in
        cell_case_ground cell (fun a ->
          match rest with
          | FEmpty ->
            Some (a,
              (let FNode (k0, p2, s0) = n' in
               if (&&) (bis_empty p2) (bis_empty s0)
               then FEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p2) (bis_empty s0)
                       then FFlat (k0, p2, s0, FEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                            else FFlat (k0, p2, s0, FEmpty)
                     | _ -> FFlat (k0, p2, s0, FEmpty))))
          | _ ->
            (match match if negb (match rest with
                                  | FEmpty -> false
                                  | _ -> true)
                         then CG
                         else let FNode (k0, p2, s0) = n' in
                              let m =
                                match k0 with
                                | KOnly -> Nat.min (bsize p2) (bsize s0)
                                | KLeft -> bsize p2
                                | KRight -> bsize s0
                              in
                              if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   0)))))))) m
                              then CG
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))))))
                                   then CY
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ 0))))))
                                        then CO
                                        else CR with
                   | CG ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | CY ->
                     (match rest with
                      | FEmpty ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (f, rr) ->
                        (match f with
                         | FFlat (k2, p2, s2, lrest) ->
                           repair_packet_x (FBPairY (n', FHole, rr)) (FNode
                             (k2, p2, s2)) lrest
                         | FSingle (lb, ln, lrest) ->
                           repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                         | _ ->
                           Some
                             (let b = FHole in
                              match b with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, rest)
                              | _ -> FSingle (b, n', rest))))
                   | CO ->
                     (match rest with
                      | FEmpty ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (ll, f) ->
                        (match f with
                         | FFlat (k2, p2, s2, rrest) ->
                           repair_packet_x (FBPairO (n', ll, FHole)) (FNode
                             (k2, p2, s2)) rrest
                         | FSingle (rb, rn, rrest) ->
                           repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                         | _ ->
                           Some
                             (let b = FHole in
                              match b with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, rest)
                              | _ -> FSingle (b, n', rest))))
                   | CR ->
                     let FNode (k0, p2, s1) = n' in
                     (match k0 with
                      | KOnly ->
                        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                             (bsize s1)
                        then repair_front_x KOnly FHole p2 s1 rest
                        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize p2)
                             then repair_back_x KOnly FHole p2 s1 rest
                             else repair_both_x FHole p2 s1 rest
                      | KLeft -> repair_front_x KLeft FHole p2 s1 rest
                      | KRight -> repair_back_x KRight FHole p2 s1 rest) with
             | Some d'' -> Some (a, d'')
             | None -> None))
          None
      | None -> None))
| FSingle (b, n, rest) ->
  let (n0, child) = root_and_child_x b n rest in
  let FNode (k, p, s) = n0 in
  (match bpop p with
   | Some p0 ->
     let (x, p') = p0 in
     let p1 = (x, (FNode (k, p', s))) in
     let (cell, n') = p1 in
     cell_case_ground cell (fun a ->
       match child with
       | FEmpty ->
         Some (a,
           (let FNode (k0, p2, s0) = n' in
            if (&&) (bis_empty p2) (bis_empty s0)
            then FEmpty
            else (match k0 with
                  | KOnly ->
                    if (||) (bis_empty p2) (bis_empty s0)
                    then FFlat (k0, p2, s0, FEmpty)
                    else if (||)
                              (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                         then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                         else FFlat (k0, p2, s0, FEmpty)
                  | _ -> FFlat (k0, p2, s0, FEmpty))))
       | _ ->
         (match match if negb (match child with
                               | FEmpty -> false
                               | _ -> true)
                      then CG
                      else let FNode (k0, p2, s0) = n' in
                           let m =
                             match k0 with
                             | KOnly -> Nat.min (bsize p2) (bsize s0)
                             | KLeft -> bsize p2
                             | KRight -> bsize s0
                           in
                           if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                           then CG
                           else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ 0)))))))
                                then CY
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                     then CO
                                     else CR with
                | CG ->
                  Some
                    (let b0 = FHole in
                     match b0 with
                     | FHole ->
                       let FNode (k0, p2, s0) = n' in
                       FFlat (k0, p2, s0, child)
                     | _ -> FSingle (b0, n', child))
                | CY ->
                  (match child with
                   | FEmpty ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (f, rr) ->
                     (match f with
                      | FFlat (k2, p2, s2, lrest) ->
                        repair_packet_x (FBPairY (n', FHole, rr)) (FNode (k2,
                          p2, s2)) lrest
                      | FSingle (lb, ln, lrest) ->
                        repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                      | _ ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))))
                | CO ->
                  (match child with
                   | FEmpty ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (ll, f) ->
                     (match f with
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBPairO (n', ll, FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                      | _ ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))))
                | CR ->
                  let FNode (k0, p2, s1) = n' in
                  (match k0 with
                   | KOnly ->
                     if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))) (bsize s1)
                     then repair_front_x KOnly FHole p2 s1 child
                     else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize p2)
                          then repair_back_x KOnly FHole p2 s1 child
                          else repair_both_x FHole p2 s1 child
                   | KLeft -> repair_front_x KLeft FHole p2 s1 child
                   | KRight -> repair_back_x KRight FHole p2 s1 child) with
          | Some d'' -> Some (a, d'')
          | None -> None))
       None
   | None ->
     (match bpop s with
      | Some p0 ->
        let (x, s') = p0 in
        let p1 = (x, (FNode (k, p, s'))) in
        let (cell, n') = p1 in
        cell_case_ground cell (fun a ->
          match child with
          | FEmpty ->
            Some (a,
              (let FNode (k0, p2, s0) = n' in
               if (&&) (bis_empty p2) (bis_empty s0)
               then FEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p2) (bis_empty s0)
                       then FFlat (k0, p2, s0, FEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                            else FFlat (k0, p2, s0, FEmpty)
                     | _ -> FFlat (k0, p2, s0, FEmpty))))
          | _ ->
            (match match if negb
                              (match child with
                               | FEmpty -> false
                               | _ -> true)
                         then CG
                         else let FNode (k0, p2, s0) = n' in
                              let m =
                                match k0 with
                                | KOnly -> Nat.min (bsize p2) (bsize s0)
                                | KLeft -> bsize p2
                                | KRight -> bsize s0
                              in
                              if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   0)))))))) m
                              then CG
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))))))
                                   then CY
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ 0))))))
                                        then CO
                                        else CR with
                   | CG ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | CY ->
                     (match child with
                      | FEmpty ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (f, rr) ->
                        (match f with
                         | FFlat (k2, p2, s2, lrest) ->
                           repair_packet_x (FBPairY (n', FHole, rr)) (FNode
                             (k2, p2, s2)) lrest
                         | FSingle (lb, ln, lrest) ->
                           repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                         | _ ->
                           Some
                             (let b0 = FHole in
                              match b0 with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, child)
                              | _ -> FSingle (b0, n', child))))
                   | CO ->
                     (match child with
                      | FEmpty ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (ll, f) ->
                        (match f with
                         | FFlat (k2, p2, s2, rrest) ->
                           repair_packet_x (FBPairO (n', ll, FHole)) (FNode
                             (k2, p2, s2)) rrest
                         | FSingle (rb, rn, rrest) ->
                           repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                         | _ ->
                           Some
                             (let b0 = FHole in
                              match b0 with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, child)
                              | _ -> FSingle (b0, n', child))))
                   | CR ->
                     let FNode (k0, p2, s1) = n' in
                     (match k0 with
                      | KOnly ->
                        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                             (bsize s1)
                        then repair_front_x KOnly FHole p2 s1 child
                        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize p2)
                             then repair_back_x KOnly FHole p2 s1 child
                             else repair_both_x FHole p2 s1 child
                      | KLeft -> repair_front_x KLeft FHole p2 s1 child
                      | KRight -> repair_back_x KRight FHole p2 s1 child) with
             | Some d'' -> Some (a, d'')
             | None -> None))
          None
      | None -> None))
| FPair (_, _) ->
  (match pop_raw_x d with
   | Some p ->
     let (cell, d') = p in
     cell_case_ground cell (fun x ->
       match repair_pop_side_x d' with
       | Some d'' -> Some (x, d'')
       | None -> None) None
   | None -> None)

(** val cad_eject_x : 'a1 fchain -> ('a1 fchain * 'a1) option **)

let cad_eject_x d = match d with
| FEmpty -> None
| FFlat (k, p, s, rest) ->
  (match beject s with
   | Some p0 ->
     let (s', x) = p0 in
     let p1 = ((FNode (k, p, s')), x) in
     let (n', cell) = p1 in
     cell_case_ground cell (fun a ->
       match rest with
       | FEmpty ->
         Some
           ((let FNode (k0, p2, s0) = n' in
             if (&&) (bis_empty p2) (bis_empty s0)
             then FEmpty
             else (match k0 with
                   | KOnly ->
                     if (||) (bis_empty p2) (bis_empty s0)
                     then FFlat (k0, p2, s0, FEmpty)
                     else if (||)
                               (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                               (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                          then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                          else FFlat (k0, p2, s0, FEmpty)
                   | _ -> FFlat (k0, p2, s0, FEmpty))),
           a)
       | _ ->
         (match match if negb (match rest with
                               | FEmpty -> false
                               | _ -> true)
                      then CG
                      else let FNode (k0, p2, s0) = n' in
                           let m =
                             match k0 with
                             | KOnly -> Nat.min (bsize p2) (bsize s0)
                             | KLeft -> bsize p2
                             | KRight -> bsize s0
                           in
                           if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                           then CG
                           else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ 0)))))))
                                then CY
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                     then CO
                                     else CR with
                | CG ->
                  Some
                    (let b = FHole in
                     match b with
                     | FHole ->
                       let FNode (k0, p2, s0) = n' in FFlat (k0, p2, s0, rest)
                     | _ -> FSingle (b, n', rest))
                | CY ->
                  (match rest with
                   | FEmpty ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (f, rr) ->
                     (match f with
                      | FFlat (k2, p2, s2, lrest) ->
                        repair_packet_x (FBPairY (n', FHole, rr)) (FNode (k2,
                          p2, s2)) lrest
                      | FSingle (lb, ln, lrest) ->
                        repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                      | _ ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))))
                | CO ->
                  (match rest with
                   | FEmpty ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (ll, f) ->
                     (match f with
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBPairO (n', ll, FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                      | _ ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))))
                | CR ->
                  let FNode (k0, p2, s1) = n' in
                  (match k0 with
                   | KOnly ->
                     if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))) (bsize s1)
                     then repair_front_x KOnly FHole p2 s1 rest
                     else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize p2)
                          then repair_back_x KOnly FHole p2 s1 rest
                          else repair_both_x FHole p2 s1 rest
                   | KLeft -> repair_front_x KLeft FHole p2 s1 rest
                   | KRight -> repair_back_x KRight FHole p2 s1 rest) with
          | Some d'' -> Some (d'', a)
          | None -> None))
       None
   | None ->
     (match beject p with
      | Some p0 ->
        let (p', x) = p0 in
        let p1 = ((FNode (k, p', bempty)), x) in
        let (n', cell) = p1 in
        cell_case_ground cell (fun a ->
          match rest with
          | FEmpty ->
            Some
              ((let FNode (k0, p2, s0) = n' in
                if (&&) (bis_empty p2) (bis_empty s0)
                then FEmpty
                else (match k0 with
                      | KOnly ->
                        if (||) (bis_empty p2) (bis_empty s0)
                        then FFlat (k0, p2, s0, FEmpty)
                        else if (||)
                                  (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                  (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                             else FFlat (k0, p2, s0, FEmpty)
                      | _ -> FFlat (k0, p2, s0, FEmpty))),
              a)
          | _ ->
            (match match if negb (match rest with
                                  | FEmpty -> false
                                  | _ -> true)
                         then CG
                         else let FNode (k0, p2, s0) = n' in
                              let m =
                                match k0 with
                                | KOnly -> Nat.min (bsize p2) (bsize s0)
                                | KLeft -> bsize p2
                                | KRight -> bsize s0
                              in
                              if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   0)))))))) m
                              then CG
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))))))
                                   then CY
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ 0))))))
                                        then CO
                                        else CR with
                   | CG ->
                     Some
                       (let b = FHole in
                        match b with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, rest)
                        | _ -> FSingle (b, n', rest))
                   | CY ->
                     (match rest with
                      | FEmpty ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (f, rr) ->
                        (match f with
                         | FFlat (k2, p2, s2, lrest) ->
                           repair_packet_x (FBPairY (n', FHole, rr)) (FNode
                             (k2, p2, s2)) lrest
                         | FSingle (lb, ln, lrest) ->
                           repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                         | _ ->
                           Some
                             (let b = FHole in
                              match b with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, rest)
                              | _ -> FSingle (b, n', rest))))
                   | CO ->
                     (match rest with
                      | FEmpty ->
                        Some
                          (let b = FHole in
                           match b with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, rest)
                           | _ -> FSingle (b, n', rest))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (ll, f) ->
                        (match f with
                         | FFlat (k2, p2, s2, rrest) ->
                           repair_packet_x (FBPairO (n', ll, FHole)) (FNode
                             (k2, p2, s2)) rrest
                         | FSingle (rb, rn, rrest) ->
                           repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                         | _ ->
                           Some
                             (let b = FHole in
                              match b with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, rest)
                              | _ -> FSingle (b, n', rest))))
                   | CR ->
                     let FNode (k0, p2, s1) = n' in
                     (match k0 with
                      | KOnly ->
                        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                             (bsize s1)
                        then repair_front_x KOnly FHole p2 s1 rest
                        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize p2)
                             then repair_back_x KOnly FHole p2 s1 rest
                             else repair_both_x FHole p2 s1 rest
                      | KLeft -> repair_front_x KLeft FHole p2 s1 rest
                      | KRight -> repair_back_x KRight FHole p2 s1 rest) with
             | Some d'' -> Some (d'', a)
             | None -> None))
          None
      | None -> None))
| FSingle (b, n, rest) ->
  let (n0, child) = root_and_child_x b n rest in
  let FNode (k, p, s) = n0 in
  (match beject s with
   | Some p0 ->
     let (s', x) = p0 in
     let p1 = ((FNode (k, p, s')), x) in
     let (n', cell) = p1 in
     cell_case_ground cell (fun a ->
       match child with
       | FEmpty ->
         Some
           ((let FNode (k0, p2, s0) = n' in
             if (&&) (bis_empty p2) (bis_empty s0)
             then FEmpty
             else (match k0 with
                   | KOnly ->
                     if (||) (bis_empty p2) (bis_empty s0)
                     then FFlat (k0, p2, s0, FEmpty)
                     else if (||)
                               (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                               (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ
                                 (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                          then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                          else FFlat (k0, p2, s0, FEmpty)
                   | _ -> FFlat (k0, p2, s0, FEmpty))),
           a)
       | _ ->
         (match match if negb (match child with
                               | FEmpty -> false
                               | _ -> true)
                      then CG
                      else let FNode (k0, p2, s0) = n' in
                           let m =
                             match k0 with
                             | KOnly -> Nat.min (bsize p2) (bsize s0)
                             | KLeft -> bsize p2
                             | KRight -> bsize s0
                           in
                           if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ
                                (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))) m
                           then CG
                           else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ 0)))))))
                                then CY
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0))))))
                                     then CO
                                     else CR with
                | CG ->
                  Some
                    (let b0 = FHole in
                     match b0 with
                     | FHole ->
                       let FNode (k0, p2, s0) = n' in
                       FFlat (k0, p2, s0, child)
                     | _ -> FSingle (b0, n', child))
                | CY ->
                  (match child with
                   | FEmpty ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (f, rr) ->
                     (match f with
                      | FFlat (k2, p2, s2, lrest) ->
                        repair_packet_x (FBPairY (n', FHole, rr)) (FNode (k2,
                          p2, s2)) lrest
                      | FSingle (lb, ln, lrest) ->
                        repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                      | _ ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))))
                | CO ->
                  (match child with
                   | FEmpty ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | FFlat (k2, p2, s2, rrest) ->
                     repair_packet_x (FBSingle (n', FHole)) (FNode (k2, p2,
                       s2)) rrest
                   | FSingle (rb, rn, rrest) ->
                     repair_packet_x (FBSingle (n', rb)) rn rrest
                   | FPair (ll, f) ->
                     (match f with
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBPairO (n', ll, FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                      | _ ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))))
                | CR ->
                  let FNode (k0, p2, s1) = n' in
                  (match k0 with
                   | KOnly ->
                     if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                          0)))))))) (bsize s1)
                     then repair_front_x KOnly FHole p2 s1 child
                     else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize p2)
                          then repair_back_x KOnly FHole p2 s1 child
                          else repair_both_x FHole p2 s1 child
                   | KLeft -> repair_front_x KLeft FHole p2 s1 child
                   | KRight -> repair_back_x KRight FHole p2 s1 child) with
          | Some d'' -> Some (d'', a)
          | None -> None))
       None
   | None ->
     (match beject p with
      | Some p0 ->
        let (p', x) = p0 in
        let p1 = ((FNode (k, p', bempty)), x) in
        let (n', cell) = p1 in
        cell_case_ground cell (fun a ->
          match child with
          | FEmpty ->
            Some
              ((let FNode (k0, p2, s0) = n' in
                if (&&) (bis_empty p2) (bis_empty s0)
                then FEmpty
                else (match k0 with
                      | KOnly ->
                        if (||) (bis_empty p2) (bis_empty s0)
                        then FFlat (k0, p2, s0, FEmpty)
                        else if (||)
                                  (Nat.ltb (bsize p2) (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                  (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                             then FFlat (KOnly, (bapp p2 s0), bempty, FEmpty)
                             else FFlat (k0, p2, s0, FEmpty)
                      | _ -> FFlat (k0, p2, s0, FEmpty))),
              a)
          | _ ->
            (match match if negb
                              (match child with
                               | FEmpty -> false
                               | _ -> true)
                         then CG
                         else let FNode (k0, p2, s0) = n' in
                              let m =
                                match k0 with
                                | KOnly -> Nat.min (bsize p2) (bsize s0)
                                | KLeft -> bsize p2
                                | KRight -> bsize s0
                              in
                              if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   0)))))))) m
                              then CG
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ 0)))))))
                                   then CY
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ 0))))))
                                        then CO
                                        else CR with
                   | CG ->
                     Some
                       (let b0 = FHole in
                        match b0 with
                        | FHole ->
                          let FNode (k0, p2, s0) = n' in
                          FFlat (k0, p2, s0, child)
                        | _ -> FSingle (b0, n', child))
                   | CY ->
                     (match child with
                      | FEmpty ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (f, rr) ->
                        (match f with
                         | FFlat (k2, p2, s2, lrest) ->
                           repair_packet_x (FBPairY (n', FHole, rr)) (FNode
                             (k2, p2, s2)) lrest
                         | FSingle (lb, ln, lrest) ->
                           repair_packet_x (FBPairY (n', lb, rr)) ln lrest
                         | _ ->
                           Some
                             (let b0 = FHole in
                              match b0 with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, child)
                              | _ -> FSingle (b0, n', child))))
                   | CO ->
                     (match child with
                      | FEmpty ->
                        Some
                          (let b0 = FHole in
                           match b0 with
                           | FHole ->
                             let FNode (k0, p2, s0) = n' in
                             FFlat (k0, p2, s0, child)
                           | _ -> FSingle (b0, n', child))
                      | FFlat (k2, p2, s2, rrest) ->
                        repair_packet_x (FBSingle (n', FHole)) (FNode (k2,
                          p2, s2)) rrest
                      | FSingle (rb, rn, rrest) ->
                        repair_packet_x (FBSingle (n', rb)) rn rrest
                      | FPair (ll, f) ->
                        (match f with
                         | FFlat (k2, p2, s2, rrest) ->
                           repair_packet_x (FBPairO (n', ll, FHole)) (FNode
                             (k2, p2, s2)) rrest
                         | FSingle (rb, rn, rrest) ->
                           repair_packet_x (FBPairO (n', ll, rb)) rn rrest
                         | _ ->
                           Some
                             (let b0 = FHole in
                              match b0 with
                              | FHole ->
                                let FNode (k0, p2, s0) = n' in
                                FFlat (k0, p2, s0, child)
                              | _ -> FSingle (b0, n', child))))
                   | CR ->
                     let FNode (k0, p2, s1) = n' in
                     (match k0 with
                      | KOnly ->
                        if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                             (bsize s1)
                        then repair_front_x KOnly FHole p2 s1 child
                        else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize p2)
                             then repair_back_x KOnly FHole p2 s1 child
                             else repair_both_x FHole p2 s1 child
                      | KLeft -> repair_front_x KLeft FHole p2 s1 child
                      | KRight -> repair_back_x KRight FHole p2 s1 child) with
             | Some d'' -> Some (d'', a)
             | None -> None))
          None
      | None -> None))
| FPair (_, _) ->
  (match eject_raw_x d with
   | Some p ->
     let (d', cell) = p in
     cell_case_ground cell (fun x ->
       match repair_eject_side_x d' with
       | Some d'' -> Some (d'', x)
       | None -> None) None
   | None -> None)

(** val fcad_empty : 'a1 fchain **)

let fcad_empty =
  FEmpty
