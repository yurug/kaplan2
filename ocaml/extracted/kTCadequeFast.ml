
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

type gyor =
| CG
| CY
| CO
| CR

(** val chain_has_node : 'a1 cchain -> bool **)

let chain_has_node = function
| CEmpty -> false
| _ -> true

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

(** val push_chain_f : 'a1 stored -> 'a1 cchain -> 'a1 cchain **)

let rec push_chain_f s = function
| CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, (b1 s), bempty)))), CEmpty)
| CSingle (p, rest) ->
  let Pkt (c0, n) = p in
  (match c0 with
   | BHole ->
     let n0 =
       let Node (k, p0, suf) = n in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb (chain_has_node rest)
            then CG
            else let Node (k, p0, s0) = n0 in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
        (match rest with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (c1, r) ->
           (match c1 with
            | CSingle (c2, lrest) ->
              let Pkt (lb, ln) = c2 in
              CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
            | _ -> CSingle ((Pkt (BHole, n0)), rest)))
      | CO ->
        (match rest with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (l, c1) ->
           (match c1 with
            | CSingle (c2, rrest) ->
              let Pkt (rb, rn) = c2 in
              CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
            | _ -> CSingle ((Pkt (BHole, n0)), rest)))
      | _ -> CSingle ((Pkt (BHole, n0)), rest))
   | BSingle (hn, b') ->
     let child = CSingle ((Pkt (b', n)), rest) in
     let n0 =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb (chain_has_node child)
            then CG
            else let Node (k, p0, s0) = n0 in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (c1, r) ->
           (match c1 with
            | CSingle (c2, lrest) ->
              let Pkt (lb, ln) = c2 in
              CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | CO ->
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (l, c1) ->
           (match c1 with
            | CSingle (c2, rrest) ->
              let Pkt (rb, rn) = c2 in
              CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | _ -> CSingle ((Pkt (BHole, n0)), child))
   | BPairY (hn, b', rc) ->
     let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
     let n0 =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb (chain_has_node child)
            then CG
            else let Node (k, p0, s0) = n0 in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (c1, r) ->
           (match c1 with
            | CSingle (c2, lrest) ->
              let Pkt (lb, ln) = c2 in
              CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | CO ->
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (l, c1) ->
           (match c1 with
            | CSingle (c2, rrest) ->
              let Pkt (rb, rn) = c2 in
              CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | _ -> CSingle ((Pkt (BHole, n0)), child))
   | BPairO (hn, lc, b') ->
     let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
     let n0 =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb (chain_has_node child)
            then CG
            else let Node (k, p0, s0) = n0 in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (c1, r) ->
           (match c1 with
            | CSingle (c2, lrest) ->
              let Pkt (lb, ln) = c2 in
              CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | CO ->
        (match child with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (l, c1) ->
           (match c1 with
            | CSingle (c2, rrest) ->
              let Pkt (rb, rn) = c2 in
              CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
            | _ -> CSingle ((Pkt (BHole, n0)), child)))
      | _ -> CSingle ((Pkt (BHole, n0)), child)))
| CPair (l, r) -> CPair ((push_chain_f s l), r)

(** val inject_chain_f : 'a1 cchain -> 'a1 stored -> 'a1 cchain **)

let rec inject_chain_f c s =
  match c with
  | CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, bempty, (b1 s))))), CEmpty)
  | CSingle (p, rest) ->
    let Pkt (c0, n) = p in
    (match c0 with
     | BHole ->
       let n0 =
         let Node (k, p0, suf) = n in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb (chain_has_node rest)
              then CG
              else let Node (k, p0, s0) = n0 in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
          (match rest with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (c1, r) ->
             (match c1 with
              | CSingle (c2, lrest) ->
                let Pkt (lb, ln) = c2 in
                CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
              | _ -> CSingle ((Pkt (BHole, n0)), rest)))
        | CO ->
          (match rest with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (l, c1) ->
             (match c1 with
              | CSingle (c2, rrest) ->
                let Pkt (rb, rn) = c2 in
                CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
              | _ -> CSingle ((Pkt (BHole, n0)), rest)))
        | _ -> CSingle ((Pkt (BHole, n0)), rest))
     | BSingle (hn, b') ->
       let child = CSingle ((Pkt (b', n)), rest) in
       let n0 =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb (chain_has_node child)
              then CG
              else let Node (k, p0, s0) = n0 in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (c1, r) ->
             (match c1 with
              | CSingle (c2, lrest) ->
                let Pkt (lb, ln) = c2 in
                CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | CO ->
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (l, c1) ->
             (match c1 with
              | CSingle (c2, rrest) ->
                let Pkt (rb, rn) = c2 in
                CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | _ -> CSingle ((Pkt (BHole, n0)), child))
     | BPairY (hn, b', rc) ->
       let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
       let n0 =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb (chain_has_node child)
              then CG
              else let Node (k, p0, s0) = n0 in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (c1, r) ->
             (match c1 with
              | CSingle (c2, lrest) ->
                let Pkt (lb, ln) = c2 in
                CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | CO ->
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (l, c1) ->
             (match c1 with
              | CSingle (c2, rrest) ->
                let Pkt (rb, rn) = c2 in
                CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | _ -> CSingle ((Pkt (BHole, n0)), child))
     | BPairO (hn, lc, b') ->
       let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
       let n0 =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb (chain_has_node child)
              then CG
              else let Node (k, p0, s0) = n0 in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (c1, r) ->
             (match c1 with
              | CSingle (c2, lrest) ->
                let Pkt (lb, ln) = c2 in
                CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | CO ->
          (match child with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (l, c1) ->
             (match c1 with
              | CSingle (c2, rrest) ->
                let Pkt (rb, rn) = c2 in
                CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
              | _ -> CSingle ((Pkt (BHole, n0)), child)))
        | _ -> CSingle ((Pkt (BHole, n0)), child)))
  | CPair (l, r) -> CPair (l, (inject_chain_f r s))

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
            Some
            (let n = Node (KLeft, (bapp p1 s1'), (b2 y z)) in
             let child = CEmpty in
             (match if negb (chain_has_node child)
                    then CG
                    else let Node (k, p2, s) = n in
                         let m =
                           match k with
                           | KOnly -> Nat.min (bsize p2) (bsize s)
                           | KLeft -> bsize p2
                           | KRight -> bsize s
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                 | CSingle (c, rrest) ->
                   let Pkt (rb, rn) = c in
                   CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
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
                   let Pkt (rb, rn) = c in
                   CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                 | CPair (l, c) ->
                   (match c with
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n)), child)))
              | _ -> CSingle ((Pkt (BHole, n)), child)))
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
                     (let n = Node (KLeft, (bapp p1 (b3 a b c)), (b2 y z)) in
                      let child = push_chain_f (SSmall smid) CEmpty in
                      (match if negb (chain_has_node child)
                             then CG
                             else let Node (k, p5, s) = n in
                                  let m =
                                    match k with
                                    | KOnly -> Nat.min (bsize p5) (bsize s)
                                    | KLeft -> bsize p5
                                    | KRight -> bsize s
                                  in
                                  if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) m
                                  then CG
                                  else if (=) m (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                       then CY
                                       else if (=) m (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ 0))))))
                                            then CO
                                            else CR with
                       | CY ->
                         (match child with
                          | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                          | CPair (c0, r) ->
                            (match c0 with
                             | CSingle (c1, lrest) ->
                               let Pkt (lb, ln) = c1 in
                               CSingle ((Pkt ((BPairY (n, lb, r)), ln)),
                               lrest)
                             | _ -> CSingle ((Pkt (BHole, n)), child)))
                       | CO ->
                         (match child with
                          | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                          | CPair (l, c0) ->
                            (match c0 with
                             | CSingle (c1, rrest) ->
                               let Pkt (rb, rn) = c1 in
                               CSingle ((Pkt ((BPairO (n, l, rb)), rn)),
                               rrest)
                             | _ -> CSingle ((Pkt (BHole, n)), child)))
                       | _ -> CSingle ((Pkt (BHole, n)), child)))
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
       (let n = Node (KLeft, p1, (b2 y z)) in
        let child = inject_chain_f d1 (SSmall s1') in
        (match if negb (chain_has_node child)
               then CG
               else let Node (k, p2, s) = n in
                    let m =
                      match k with
                      | KOnly -> Nat.min (bsize p2) (bsize s)
                      | KLeft -> bsize p2
                      | KRight -> bsize s
                    in
                    if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))))) m
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
           (match child with
            | CEmpty -> CSingle ((Pkt (BHole, n)), child)
            | CSingle (c, rrest) ->
              let Pkt (rb, rn) = c in
              CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
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
              let Pkt (rb, rn) = c in
              CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
            | CPair (l, c) ->
              (match c with
               | CSingle (c0, rrest) ->
                 let Pkt (rb, rn) = c0 in
                 CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
               | _ -> CSingle ((Pkt (BHole, n)), child)))
         | _ -> CSingle ((Pkt (BHole, n)), child)))
     | None -> None)

(** val make_left_f : 'a1 cchain -> 'a1 cchain option **)

let make_left_f = function
| CEmpty -> None
| CSingle (p, r) ->
  let Pkt (c, n) = p in
  (match c with
   | BHole -> let Node (_, p1, s1) = n in make_left_only_f p1 r s1
   | BSingle (hn, b') ->
     let d1 = CSingle ((Pkt (b', n)), r) in
     let Node (_, p1, s1) = hn in make_left_only_f p1 d1 s1
   | BPairY (hn, b', rc) ->
     let d1 = CPair ((CSingle ((Pkt (b', n)), r)), rc) in
     let Node (_, p1, s1) = hn in make_left_only_f p1 d1 s1
   | BPairO (hn, lc, b') ->
     let d1 = CPair (lc, (CSingle ((Pkt (b', n)), r))) in
     let Node (_, p1, s1) = hn in make_left_only_f p1 d1 s1)
| CPair (c, c0) ->
  (match c with
   | CSingle (pl, rl) ->
     (match c0 with
      | CSingle (pr, rr) ->
        let Pkt (c1, n) = pl in
        (match c1 with
         | BHole ->
           let Node (_, p1, s1) = n in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match rl with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) rr s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f rl (SBig ((bapp s1 p2), rr, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn, b') ->
              let d2 = CSingle ((Pkt (b', n0)), rr) in
              let Node (_, p2, s2) = hn in
              (match rl with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f rl (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn, b', rc) ->
              let d2 = CPair ((CSingle ((Pkt (b', n0)), rr)), rc) in
              let Node (_, p2, s2) = hn in
              (match rl with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f rl (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn, lc, b') ->
              let d2 = CPair (lc, (CSingle ((Pkt (b', n0)), rr))) in
              let Node (_, p2, s2) = hn in
              (match rl with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f rl (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BSingle (hn, b') ->
           let d1 = CSingle ((Pkt (b', n)), rl) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) rr s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), rr, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc, b'0) ->
              let d2 = CPair (lc, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BPairY (hn, b', rc) ->
           let d1 = CPair ((CSingle ((Pkt (b', n)), rl)), rc) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) rr s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), rr, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc0) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc0) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc, b'0) ->
              let d2 = CPair (lc, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BPairO (hn, lc, b') ->
           let d1 = CPair (lc, (CSingle ((Pkt (b', n)), rl))) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) rr s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), rr, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc0, b'0) ->
              let d2 = CPair (lc0, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d1 with
               | CEmpty -> make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
               | _ ->
                 (match beject2 s2 with
                  | Some p ->
                    let (p0, z) = p in
                    let (s2', y) = p0 in
                    Some
                    (let n1 = Node (KLeft, p1, (b2 y z)) in
                     let child =
                       inject_chain_f d1 (SBig ((bapp s1 p2), d2, s2'))
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))))
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
            Some
            (let n = Node (KRight, (b2 x y), (bapp p1' s1)) in
             let child = CEmpty in
             (match if negb (chain_has_node child)
                    then CG
                    else let Node (k, p2, s) = n in
                         let m =
                           match k with
                           | KOnly -> Nat.min (bsize p2) (bsize s)
                           | KLeft -> bsize p2
                           | KRight -> bsize s
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                 | CSingle (c, rrest) ->
                   let Pkt (rb, rn) = c in
                   CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
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
                   let Pkt (rb, rn) = c in
                   CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                 | CPair (l, c) ->
                   (match c with
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n)), child)))
              | _ -> CSingle ((Pkt (BHole, n)), child)))
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
               (let n = Node (KRight, (b2 x y), (bapp (b3 a b c) s1)) in
                let child = push_chain_f (SSmall pmid) CEmpty in
                (match if negb (chain_has_node child)
                       then CG
                       else let Node (k, p5, s) = n in
                            let m =
                              match k with
                              | KOnly -> Nat.min (bsize p5) (bsize s)
                              | KLeft -> bsize p5
                              | KRight -> bsize s
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
                 | CY ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                    | CPair (c0, r) ->
                      (match c0 with
                       | CSingle (c1, lrest) ->
                         let Pkt (lb, ln) = c1 in
                         CSingle ((Pkt ((BPairY (n, lb, r)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n)), child)))
                 | CO ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n)), child)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
                    | CPair (l, c0) ->
                      (match c0 with
                       | CSingle (c1, rrest) ->
                         let Pkt (rb, rn) = c1 in
                         CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n)), child)))
                 | _ -> CSingle ((Pkt (BHole, n)), child)))
             | None -> None)
          | None -> None)
  | _ ->
    (match bpop2 p1 with
     | Some p ->
       let (p0, p1') = p in
       let (x, y) = p0 in
       Some
       (let n = Node (KRight, (b2 x y), s1) in
        let child = push_chain_f (SSmall p1') d1 in
        (match if negb (chain_has_node child)
               then CG
               else let Node (k, p2, s) = n in
                    let m =
                      match k with
                      | KOnly -> Nat.min (bsize p2) (bsize s)
                      | KLeft -> bsize p2
                      | KRight -> bsize s
                    in
                    if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                         0)))))))) m
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
           (match child with
            | CEmpty -> CSingle ((Pkt (BHole, n)), child)
            | CSingle (c, rrest) ->
              let Pkt (rb, rn) = c in
              CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
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
              let Pkt (rb, rn) = c in
              CSingle ((Pkt ((BSingle (n, rb)), rn)), rrest)
            | CPair (l, c) ->
              (match c with
               | CSingle (c0, rrest) ->
                 let Pkt (rb, rn) = c0 in
                 CSingle ((Pkt ((BPairO (n, l, rb)), rn)), rrest)
               | _ -> CSingle ((Pkt (BHole, n)), child)))
         | _ -> CSingle ((Pkt (BHole, n)), child)))
     | None -> None)

(** val make_right_f : 'a1 cchain -> 'a1 cchain option **)

let make_right_f = function
| CEmpty -> None
| CSingle (p, r) ->
  let Pkt (c, n) = p in
  (match c with
   | BHole -> let Node (_, p1, s1) = n in make_right_only_f p1 r s1
   | BSingle (hn, b') ->
     let d1 = CSingle ((Pkt (b', n)), r) in
     let Node (_, p1, s1) = hn in make_right_only_f p1 d1 s1
   | BPairY (hn, b', rc) ->
     let d1 = CPair ((CSingle ((Pkt (b', n)), r)), rc) in
     let Node (_, p1, s1) = hn in make_right_only_f p1 d1 s1
   | BPairO (hn, lc, b') ->
     let d1 = CPair (lc, (CSingle ((Pkt (b', n)), r))) in
     let Node (_, p1, s1) = hn in make_right_only_f p1 d1 s1)
| CPair (c, c0) ->
  (match c with
   | CSingle (pl, rl) ->
     (match c0 with
      | CSingle (pr, rr) ->
        let Pkt (c1, n) = pl in
        (match c1 with
         | BHole ->
           let Node (_, p1, s1) = n in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match rr with
               | CEmpty -> make_right_only_f p1 rl (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', rl, (bapp s1 p2))) rr
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn, b') ->
              let d2 = CSingle ((Pkt (b', n0)), rr) in
              let Node (_, p2, s2) = hn in
              (match d2 with
               | CEmpty -> make_right_only_f p1 rl (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', rl, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn, b', rc) ->
              let d2 = CPair ((CSingle ((Pkt (b', n0)), rr)), rc) in
              let Node (_, p2, s2) = hn in
              (match d2 with
               | CEmpty -> make_right_only_f p1 rl (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', rl, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn, lc, b') ->
              let d2 = CPair (lc, (CSingle ((Pkt (b', n0)), rr))) in
              let Node (_, p2, s2) = hn in
              (match d2 with
               | CEmpty -> make_right_only_f p1 rl (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', rl, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BSingle (hn, b') ->
           let d1 = CSingle ((Pkt (b', n)), rl) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match rr with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) rr
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc, b'0) ->
              let d2 = CPair (lc, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BPairY (hn, b', rc) ->
           let d1 = CPair ((CSingle ((Pkt (b', n)), rl)), rc) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match rr with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) rr
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc0) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc0) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc, b'0) ->
              let d2 = CPair (lc, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None)))
         | BPairO (hn, lc, b') ->
           let d1 = CPair (lc, (CSingle ((Pkt (b', n)), rl))) in
           let Node (_, p1, s1) = hn in
           let Pkt (c2, n0) = pr in
           (match c2 with
            | BHole ->
              let Node (_, p2, s2) = n0 in
              (match rr with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) rr
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BSingle (hn0, b'0) ->
              let d2 = CSingle ((Pkt (b'0, n0)), rr) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairY (hn0, b'0, rc) ->
              let d2 = CPair ((CSingle ((Pkt (b'0, n0)), rr)), rc) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))
            | BPairO (hn0, lc0, b'0) ->
              let d2 = CPair (lc0, (CSingle ((Pkt (b'0, n0)), rr))) in
              let Node (_, p2, s2) = hn0 in
              (match d2 with
               | CEmpty -> make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
               | _ ->
                 (match bpop2 p1 with
                  | Some p ->
                    let (p0, p1') = p in
                    let (x, y) = p0 in
                    Some
                    (let n1 = Node (KRight, (b2 x y), s2) in
                     let child =
                       push_chain_f (SBig (p1', d1, (bapp s1 p2))) d2
                     in
                     (match if negb (chain_has_node child)
                            then CG
                            else let Node (k, p3, s) = n1 in
                                 let m =
                                   match k with
                                   | KOnly -> Nat.min (bsize p3) (bsize s)
                                   | KLeft -> bsize p3
                                   | KRight -> bsize s
                                 in
                                 if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0)))))))) m
                                 then CG
                                 else if (=) m (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0)))))))
                                      then CY
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0))))))
                                           then CO
                                           else CR with
                      | CY ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (c3, r) ->
                           (match c3 with
                            | CSingle (c4, lrest) ->
                              let Pkt (lb, ln) = c4 in
                              CSingle ((Pkt ((BPairY (n1, lb, r)), ln)),
                              lrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | CO ->
                        (match child with
                         | CEmpty -> CSingle ((Pkt (BHole, n1)), child)
                         | CSingle (c3, rrest) ->
                           let Pkt (rb, rn) = c3 in
                           CSingle ((Pkt ((BSingle (n1, rb)), rn)), rrest)
                         | CPair (l, c3) ->
                           (match c3 with
                            | CSingle (c4, rrest) ->
                              let Pkt (rb, rn) = c4 in
                              CSingle ((Pkt ((BPairO (n1, l, rb)), rn)),
                              rrest)
                            | _ -> CSingle ((Pkt (BHole, n1)), child)))
                      | _ -> CSingle ((Pkt (BHole, n1)), child)))
                  | None -> None))))
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
          let Pkt (c, n) = p in
          (match c with
           | BHole ->
             let Node (_, p2, s2) = n in
             (match r with
              | CEmpty ->
                (match beject2 p2 with
                 | Some p0 ->
                   let (p1, z) = p0 in
                   let (p2', y) = p1 in
                   Some
                   (let n0 = Node (KOnly, p3, (bpush y (bpush z s2))) in
                    let child = push_chain_f (SSmall p2') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p4, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p4) (bsize s)
                                  | KLeft -> bsize p4
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p3, s2) in
                   let child = push_chain_f (SSmall p2) r in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BSingle (hn, b') ->
             let d2 = CSingle ((Pkt (b', n)), r) in
             let Node (_, p2, s2) = hn in
             (match d2 with
              | CEmpty ->
                (match beject2 p2 with
                 | Some p0 ->
                   let (p1, z) = p0 in
                   let (p2', y) = p1 in
                   Some
                   (let n0 = Node (KOnly, p3, (bpush y (bpush z s2))) in
                    let child = push_chain_f (SSmall p2') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p4, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p4) (bsize s)
                                  | KLeft -> bsize p4
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p3, s2) in
                   let child = push_chain_f (SSmall p2) d2 in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BPairY (hn, b', rc) ->
             let d2 = CPair ((CSingle ((Pkt (b', n)), r)), rc) in
             let Node (_, p2, s2) = hn in
             (match d2 with
              | CEmpty ->
                (match beject2 p2 with
                 | Some p0 ->
                   let (p1, z) = p0 in
                   let (p2', y) = p1 in
                   Some
                   (let n0 = Node (KOnly, p3, (bpush y (bpush z s2))) in
                    let child = push_chain_f (SSmall p2') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p4, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p4) (bsize s)
                                  | KLeft -> bsize p4
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p3, s2) in
                   let child = push_chain_f (SSmall p2) d2 in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BPairO (hn, lc, b') ->
             let d2 = CPair (lc, (CSingle ((Pkt (b', n)), r))) in
             let Node (_, p2, s2) = hn in
             (match d2 with
              | CEmpty ->
                (match beject2 p2 with
                 | Some p0 ->
                   let (p1, z) = p0 in
                   let (p2', y) = p1 in
                   Some
                   (let n0 = Node (KOnly, p3, (bpush y (bpush z s2))) in
                    let child = push_chain_f (SSmall p2') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p4, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p4) (bsize s)
                                  | KLeft -> bsize p4
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p3, s2) in
                   let child = push_chain_f (SSmall p2) d2 in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child)))))
        | CPair (c, rt) ->
          (match c with
           | CSingle (pl, rl) ->
             let Pkt (c0, n) = pl in
             (match c0 with
              | BHole ->
                let Node (_, p2, s2) = n in
                Some (CPair
                ((let n0 = Node (KLeft, p3, s2) in
                  let child = push_chain_f (SSmall p2) rl in
                  (match if negb (chain_has_node child)
                         then CG
                         else let Node (k, p, s) = n0 in
                              let m =
                                match k with
                                | KOnly -> Nat.min (bsize p) (bsize s)
                                | KLeft -> bsize p
                                | KRight -> bsize s
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
                   | CY ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (c1, r) ->
                        (match c1 with
                         | CSingle (c2, lrest) ->
                           let Pkt (lb, ln) = c2 in
                           CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | CO ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (l, c1) ->
                        (match c1 with
                         | CSingle (c2, rrest) ->
                           let Pkt (rb, rn) = c2 in
                           CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | _ -> CSingle ((Pkt (BHole, n0)), child))),
                rt))
              | BSingle (hn, b') ->
                let d2 = CSingle ((Pkt (b', n)), rl) in
                let Node (_, p2, s2) = hn in
                Some (CPair
                ((let n0 = Node (KLeft, p3, s2) in
                  let child = push_chain_f (SSmall p2) d2 in
                  (match if negb (chain_has_node child)
                         then CG
                         else let Node (k, p, s) = n0 in
                              let m =
                                match k with
                                | KOnly -> Nat.min (bsize p) (bsize s)
                                | KLeft -> bsize p
                                | KRight -> bsize s
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
                   | CY ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (c1, r) ->
                        (match c1 with
                         | CSingle (c2, lrest) ->
                           let Pkt (lb, ln) = c2 in
                           CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | CO ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (l, c1) ->
                        (match c1 with
                         | CSingle (c2, rrest) ->
                           let Pkt (rb, rn) = c2 in
                           CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | _ -> CSingle ((Pkt (BHole, n0)), child))),
                rt))
              | BPairY (hn, b', rc) ->
                let d2 = CPair ((CSingle ((Pkt (b', n)), rl)), rc) in
                let Node (_, p2, s2) = hn in
                Some (CPair
                ((let n0 = Node (KLeft, p3, s2) in
                  let child = push_chain_f (SSmall p2) d2 in
                  (match if negb (chain_has_node child)
                         then CG
                         else let Node (k, p, s) = n0 in
                              let m =
                                match k with
                                | KOnly -> Nat.min (bsize p) (bsize s)
                                | KLeft -> bsize p
                                | KRight -> bsize s
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
                   | CY ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (c1, r) ->
                        (match c1 with
                         | CSingle (c2, lrest) ->
                           let Pkt (lb, ln) = c2 in
                           CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | CO ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (l, c1) ->
                        (match c1 with
                         | CSingle (c2, rrest) ->
                           let Pkt (rb, rn) = c2 in
                           CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | _ -> CSingle ((Pkt (BHole, n0)), child))),
                rt))
              | BPairO (hn, lc, b') ->
                let d2 = CPair (lc, (CSingle ((Pkt (b', n)), rl))) in
                let Node (_, p2, s2) = hn in
                Some (CPair
                ((let n0 = Node (KLeft, p3, s2) in
                  let child = push_chain_f (SSmall p2) d2 in
                  (match if negb (chain_has_node child)
                         then CG
                         else let Node (k, p, s) = n0 in
                              let m =
                                match k with
                                | KOnly -> Nat.min (bsize p) (bsize s)
                                | KLeft -> bsize p
                                | KRight -> bsize s
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
                   | CY ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (c1, r) ->
                        (match c1 with
                         | CSingle (c2, lrest) ->
                           let Pkt (lb, ln) = c2 in
                           CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | CO ->
                     (match child with
                      | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                      | CSingle (c1, rrest) ->
                        let Pkt (rb, rn) = c1 in
                        CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                      | CPair (l, c1) ->
                        (match c1 with
                         | CSingle (c2, rrest) ->
                           let Pkt (rb, rn) = c2 in
                           CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                         | _ -> CSingle ((Pkt (BHole, n0)), child)))
                   | _ -> CSingle ((Pkt (BHole, n0)), child))),
                rt)))
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
          let Pkt (c, n) = p in
          (match c with
           | BHole ->
             let Node (_, p1, s1) = n in
             (match r with
              | CEmpty ->
                (match bpop2 s1 with
                 | Some p0 ->
                   let (p2, s1') = p0 in
                   let (x, y) = p2 in
                   Some
                   (let n0 = Node (KOnly, (binject (binject p1 x) y), s3) in
                    let child = push_chain_f (SSmall s1') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p3, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p3) (bsize s)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p1, s3) in
                   let child = inject_chain_f r (SSmall s1) in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BSingle (hn, b') ->
             let d1 = CSingle ((Pkt (b', n)), r) in
             let Node (_, p1, s1) = hn in
             (match d1 with
              | CEmpty ->
                (match bpop2 s1 with
                 | Some p0 ->
                   let (p2, s1') = p0 in
                   let (x, y) = p2 in
                   Some
                   (let n0 = Node (KOnly, (binject (binject p1 x) y), s3) in
                    let child = push_chain_f (SSmall s1') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p3, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p3) (bsize s)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p1, s3) in
                   let child = inject_chain_f d1 (SSmall s1) in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BPairY (hn, b', rc) ->
             let d1 = CPair ((CSingle ((Pkt (b', n)), r)), rc) in
             let Node (_, p1, s1) = hn in
             (match d1 with
              | CEmpty ->
                (match bpop2 s1 with
                 | Some p0 ->
                   let (p2, s1') = p0 in
                   let (x, y) = p2 in
                   Some
                   (let n0 = Node (KOnly, (binject (binject p1 x) y), s3) in
                    let child = push_chain_f (SSmall s1') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p3, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p3) (bsize s)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p1, s3) in
                   let child = inject_chain_f d1 (SSmall s1) in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child))))
           | BPairO (hn, lc, b') ->
             let d1 = CPair (lc, (CSingle ((Pkt (b', n)), r))) in
             let Node (_, p1, s1) = hn in
             (match d1 with
              | CEmpty ->
                (match bpop2 s1 with
                 | Some p0 ->
                   let (p2, s1') = p0 in
                   let (x, y) = p2 in
                   Some
                   (let n0 = Node (KOnly, (binject (binject p1 x) y), s3) in
                    let child = push_chain_f (SSmall s1') CEmpty in
                    (match if negb (chain_has_node child)
                           then CG
                           else let Node (k, p3, s) = n0 in
                                let m =
                                  match k with
                                  | KOnly -> Nat.min (bsize p3) (bsize s)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CY ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (c0, r0) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                             lrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | CO ->
                       (match child with
                        | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                           | _ -> CSingle ((Pkt (BHole, n0)), child)))
                     | _ -> CSingle ((Pkt (BHole, n0)), child)))
                 | None -> None)
              | _ ->
                Some
                  (let n0 = Node (KOnly, p1, s3) in
                   let child = inject_chain_f d1 (SSmall s1) in
                   (match if negb (chain_has_node child)
                          then CG
                          else let Node (k, p0, s) = n0 in
                               let m =
                                 match k with
                                 | KOnly -> Nat.min (bsize p0) (bsize s)
                                 | KLeft -> bsize p0
                                 | KRight -> bsize s
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | CO ->
                      (match child with
                       | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n0)), child)))
                    | _ -> CSingle ((Pkt (BHole, n0)), child)))))
        | CPair (lt, c) ->
          (match c with
           | CSingle (pr, rr) ->
             let Pkt (c0, n) = pr in
             (match c0 with
              | BHole ->
                let Node (_, p1, s1) = n in
                Some (CPair (lt,
                (let n0 = Node (KRight, p1, s3) in
                 let child = inject_chain_f rr (SSmall s1) in
                 (match if negb (chain_has_node child)
                        then CG
                        else let Node (k, p, s) = n0 in
                             let m =
                               match k with
                               | KOnly -> Nat.min (bsize p) (bsize s)
                               | KLeft -> bsize p
                               | KRight -> bsize s
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | _ -> CSingle ((Pkt (BHole, n0)), child)))))
              | BSingle (hn, b') ->
                let d1 = CSingle ((Pkt (b', n)), rr) in
                let Node (_, p1, s1) = hn in
                Some (CPair (lt,
                (let n0 = Node (KRight, p1, s3) in
                 let child = inject_chain_f d1 (SSmall s1) in
                 (match if negb (chain_has_node child)
                        then CG
                        else let Node (k, p, s) = n0 in
                             let m =
                               match k with
                               | KOnly -> Nat.min (bsize p) (bsize s)
                               | KLeft -> bsize p
                               | KRight -> bsize s
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | _ -> CSingle ((Pkt (BHole, n0)), child)))))
              | BPairY (hn, b', rc) ->
                let d1 = CPair ((CSingle ((Pkt (b', n)), rr)), rc) in
                let Node (_, p1, s1) = hn in
                Some (CPair (lt,
                (let n0 = Node (KRight, p1, s3) in
                 let child = inject_chain_f d1 (SSmall s1) in
                 (match if negb (chain_has_node child)
                        then CG
                        else let Node (k, p, s) = n0 in
                             let m =
                               match k with
                               | KOnly -> Nat.min (bsize p) (bsize s)
                               | KLeft -> bsize p
                               | KRight -> bsize s
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | _ -> CSingle ((Pkt (BHole, n0)), child)))))
              | BPairO (hn, lc, b') ->
                let d1 = CPair (lc, (CSingle ((Pkt (b', n)), rr))) in
                let Node (_, p1, s1) = hn in
                Some (CPair (lt,
                (let n0 = Node (KRight, p1, s3) in
                 let child = inject_chain_f d1 (SSmall s1) in
                 (match if negb (chain_has_node child)
                        then CG
                        else let Node (k, p, s) = n0 in
                             let m =
                               match k with
                               | KOnly -> Nat.min (bsize p) (bsize s)
                               | KLeft -> bsize p
                               | KRight -> bsize s
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n0)), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n0)), child)))
                  | _ -> CSingle ((Pkt (BHole, n0)), child))))))
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

(** val pop_raw_f : 'a1 cchain -> ('a1 stored * 'a1 cchain) option **)

let rec pop_raw_f = function
| CEmpty -> None
| CSingle (p, rest) ->
  let Pkt (c0, n) = p in
  (match c0 with
   | BHole ->
     let Node (k, p0, s) = n in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (x0, n') = p2 in
        (match rest with
         | CEmpty ->
           Some (x0,
             (let Node (k0, p3, s0) = n' in
              if (&&) (bis_empty p3) (bis_empty s0)
              then CEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p3) (bis_empty s0)
                      then CSingle ((Pkt (BHole, n')), CEmpty)
                      else if (||)
                                (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CSingle ((Pkt (BHole, (Node (KOnly,
                                  (bapp p3 s0), bempty)))), CEmpty)
                           else CSingle ((Pkt (BHole, n')), CEmpty)
                    | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
         | _ ->
           Some (x0,
             (match if negb (chain_has_node rest)
                    then CG
                    else let Node (k0, p3, s0) = n' in
                         let m =
                           match k0 with
                           | KOnly -> Nat.min (bsize p3) (bsize s0)
                           | KLeft -> bsize p3
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match rest with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (c1, r) ->
                   (match c1 with
                    | CSingle (c2, lrest) ->
                      let Pkt (lb, ln) = c2 in
                      CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                    | _ -> CSingle ((Pkt (BHole, n')), rest)))
              | CO ->
                (match rest with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (l, c1) ->
                   (match c1 with
                    | CSingle (c2, rrest) ->
                      let Pkt (rb, rn) = c2 in
                      CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n')), rest)))
              | _ -> CSingle ((Pkt (BHole, n')), rest))))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (x0, n') = p2 in
           (match rest with
            | CEmpty ->
              Some (x0,
                (let Node (k0, p3, s0) = n' in
                 if (&&) (bis_empty p3) (bis_empty s0)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s0)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s0), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              Some (x0,
                (match if negb (chain_has_node rest)
                       then CG
                       else let Node (k0, p3, s0) = n' in
                            let m =
                              match k0 with
                              | KOnly -> Nat.min (bsize p3) (bsize s0)
                              | KLeft -> bsize p3
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
                 | CY ->
                   (match rest with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (c1, r) ->
                      (match c1 with
                       | CSingle (c2, lrest) ->
                         let Pkt (lb, ln) = c2 in
                         CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n')), rest)))
                 | CO ->
                   (match rest with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (l, c1) ->
                      (match c1 with
                       | CSingle (c2, rrest) ->
                         let Pkt (rb, rn) = c2 in
                         CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n')), rest)))
                 | _ -> CSingle ((Pkt (BHole, n')), rest))))
         | None -> None))
   | BSingle (hn, b') ->
     let child = CSingle ((Pkt (b', n)), rest) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (x0, n') = p2 in
        (match child with
         | CEmpty ->
           Some (x0,
             (let Node (k0, p3, s0) = n' in
              if (&&) (bis_empty p3) (bis_empty s0)
              then CEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p3) (bis_empty s0)
                      then CSingle ((Pkt (BHole, n')), CEmpty)
                      else if (||)
                                (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CSingle ((Pkt (BHole, (Node (KOnly,
                                  (bapp p3 s0), bempty)))), CEmpty)
                           else CSingle ((Pkt (BHole, n')), CEmpty)
                    | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
         | _ ->
           Some (x0,
             (match if negb (chain_has_node child)
                    then CG
                    else let Node (k0, p3, s0) = n' in
                         let m =
                           match k0 with
                           | KOnly -> Nat.min (bsize p3) (bsize s0)
                           | KLeft -> bsize p3
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (c1, r) ->
                   (match c1 with
                    | CSingle (c2, lrest) ->
                      let Pkt (lb, ln) = c2 in
                      CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | CO ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (l, c1) ->
                   (match c1 with
                    | CSingle (c2, rrest) ->
                      let Pkt (rb, rn) = c2 in
                      CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | _ -> CSingle ((Pkt (BHole, n')), child))))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (x0, n') = p2 in
           (match child with
            | CEmpty ->
              Some (x0,
                (let Node (k0, p3, s0) = n' in
                 if (&&) (bis_empty p3) (bis_empty s0)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s0)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s0), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              Some (x0,
                (match if negb (chain_has_node child)
                       then CG
                       else let Node (k0, p3, s0) = n' in
                            let m =
                              match k0 with
                              | KOnly -> Nat.min (bsize p3) (bsize s0)
                              | KLeft -> bsize p3
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
                 | CY ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (c1, r) ->
                      (match c1 with
                       | CSingle (c2, lrest) ->
                         let Pkt (lb, ln) = c2 in
                         CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | CO ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (l, c1) ->
                      (match c1 with
                       | CSingle (c2, rrest) ->
                         let Pkt (rb, rn) = c2 in
                         CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | _ -> CSingle ((Pkt (BHole, n')), child))))
         | None -> None))
   | BPairY (hn, b', rc) ->
     let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (x0, n') = p2 in
        (match child with
         | CEmpty ->
           Some (x0,
             (let Node (k0, p3, s0) = n' in
              if (&&) (bis_empty p3) (bis_empty s0)
              then CEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p3) (bis_empty s0)
                      then CSingle ((Pkt (BHole, n')), CEmpty)
                      else if (||)
                                (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CSingle ((Pkt (BHole, (Node (KOnly,
                                  (bapp p3 s0), bempty)))), CEmpty)
                           else CSingle ((Pkt (BHole, n')), CEmpty)
                    | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
         | _ ->
           Some (x0,
             (match if negb (chain_has_node child)
                    then CG
                    else let Node (k0, p3, s0) = n' in
                         let m =
                           match k0 with
                           | KOnly -> Nat.min (bsize p3) (bsize s0)
                           | KLeft -> bsize p3
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (c1, r) ->
                   (match c1 with
                    | CSingle (c2, lrest) ->
                      let Pkt (lb, ln) = c2 in
                      CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | CO ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (l, c1) ->
                   (match c1 with
                    | CSingle (c2, rrest) ->
                      let Pkt (rb, rn) = c2 in
                      CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | _ -> CSingle ((Pkt (BHole, n')), child))))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (x0, n') = p2 in
           (match child with
            | CEmpty ->
              Some (x0,
                (let Node (k0, p3, s0) = n' in
                 if (&&) (bis_empty p3) (bis_empty s0)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s0)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s0), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              Some (x0,
                (match if negb (chain_has_node child)
                       then CG
                       else let Node (k0, p3, s0) = n' in
                            let m =
                              match k0 with
                              | KOnly -> Nat.min (bsize p3) (bsize s0)
                              | KLeft -> bsize p3
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
                 | CY ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (c1, r) ->
                      (match c1 with
                       | CSingle (c2, lrest) ->
                         let Pkt (lb, ln) = c2 in
                         CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | CO ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (l, c1) ->
                      (match c1 with
                       | CSingle (c2, rrest) ->
                         let Pkt (rb, rn) = c2 in
                         CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | _ -> CSingle ((Pkt (BHole, n')), child))))
         | None -> None))
   | BPairO (hn, lc, b') ->
     let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (x0, n') = p2 in
        (match child with
         | CEmpty ->
           Some (x0,
             (let Node (k0, p3, s0) = n' in
              if (&&) (bis_empty p3) (bis_empty s0)
              then CEmpty
              else (match k0 with
                    | KOnly ->
                      if (||) (bis_empty p3) (bis_empty s0)
                      then CSingle ((Pkt (BHole, n')), CEmpty)
                      else if (||)
                                (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                           then CSingle ((Pkt (BHole, (Node (KOnly,
                                  (bapp p3 s0), bempty)))), CEmpty)
                           else CSingle ((Pkt (BHole, n')), CEmpty)
                    | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
         | _ ->
           Some (x0,
             (match if negb (chain_has_node child)
                    then CG
                    else let Node (k0, p3, s0) = n' in
                         let m =
                           match k0 with
                           | KOnly -> Nat.min (bsize p3) (bsize s0)
                           | KLeft -> bsize p3
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
                              else if (=) m (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                   then CO
                                   else CR with
              | CY ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (c1, r) ->
                   (match c1 with
                    | CSingle (c2, lrest) ->
                      let Pkt (lb, ln) = c2 in
                      CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | CO ->
                (match child with
                 | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                 | CSingle (c1, rrest) ->
                   let Pkt (rb, rn) = c1 in
                   CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                 | CPair (l, c1) ->
                   (match c1 with
                    | CSingle (c2, rrest) ->
                      let Pkt (rb, rn) = c2 in
                      CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                    | _ -> CSingle ((Pkt (BHole, n')), child)))
              | _ -> CSingle ((Pkt (BHole, n')), child))))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (x0, n') = p2 in
           (match child with
            | CEmpty ->
              Some (x0,
                (let Node (k0, p3, s0) = n' in
                 if (&&) (bis_empty p3) (bis_empty s0)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s0)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s0), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              Some (x0,
                (match if negb (chain_has_node child)
                       then CG
                       else let Node (k0, p3, s0) = n' in
                            let m =
                              match k0 with
                              | KOnly -> Nat.min (bsize p3) (bsize s0)
                              | KLeft -> bsize p3
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
                 | CY ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (c1, r) ->
                      (match c1 with
                       | CSingle (c2, lrest) ->
                         let Pkt (lb, ln) = c2 in
                         CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | CO ->
                   (match child with
                    | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                    | CSingle (c1, rrest) ->
                      let Pkt (rb, rn) = c1 in
                      CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                    | CPair (l, c1) ->
                      (match c1 with
                       | CSingle (c2, rrest) ->
                         let Pkt (rb, rn) = c2 in
                         CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n')), child)))
                 | _ -> CSingle ((Pkt (BHole, n')), child))))
         | None -> None)))
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
                      let Pkt (c4, n) = pr in
                      (match c4 with
                       | BHole ->
                         let Node (_, p2, s2) = n in
                         Some (x,
                         (let n0 = Node (KOnly, (bapp lp (bapp ls p2)), s2) in
                          match if negb (chain_has_node rr)
                                then CG
                                else let Node (k, p0, s) = n0 in
                                     let m =
                                       match k with
                                       | KOnly -> Nat.min (bsize p0) (bsize s)
                                       | KLeft -> bsize p0
                                       | KRight -> bsize s
                                     in
                                     if (<=) (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))))) m
                                     then CG
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
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
                          | CY ->
                            (match rr with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), rr)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (c5, r0) ->
                               (match c5 with
                                | CSingle (c6, lrest) ->
                                  let Pkt (lb, ln) = c6 in
                                  CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                                  lrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), rr)))
                          | CO ->
                            (match rr with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), rr)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (l0, c5) ->
                               (match c5 with
                                | CSingle (c6, rrest) ->
                                  let Pkt (rb, rn) = c6 in
                                  CSingle ((Pkt ((BPairO (n0, l0, rb)), rn)),
                                  rrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), rr)))
                          | _ -> CSingle ((Pkt (BHole, n0)), rr)))
                       | BSingle (hn, b') ->
                         let d2 = CSingle ((Pkt (b', n)), rr) in
                         let Node (_, p2, s2) = hn in
                         Some (x,
                         (let n0 = Node (KOnly, (bapp lp (bapp ls p2)), s2) in
                          match if negb (chain_has_node d2)
                                then CG
                                else let Node (k, p0, s) = n0 in
                                     let m =
                                       match k with
                                       | KOnly -> Nat.min (bsize p0) (bsize s)
                                       | KLeft -> bsize p0
                                       | KRight -> bsize s
                                     in
                                     if (<=) (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))))) m
                                     then CG
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
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
                          | CY ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (c5, r0) ->
                               (match c5 with
                                | CSingle (c6, lrest) ->
                                  let Pkt (lb, ln) = c6 in
                                  CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                                  lrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | CO ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (l0, c5) ->
                               (match c5 with
                                | CSingle (c6, rrest) ->
                                  let Pkt (rb, rn) = c6 in
                                  CSingle ((Pkt ((BPairO (n0, l0, rb)), rn)),
                                  rrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                       | BPairY (hn, b', rc) ->
                         let d2 = CPair ((CSingle ((Pkt (b', n)), rr)), rc) in
                         let Node (_, p2, s2) = hn in
                         Some (x,
                         (let n0 = Node (KOnly, (bapp lp (bapp ls p2)), s2) in
                          match if negb (chain_has_node d2)
                                then CG
                                else let Node (k, p0, s) = n0 in
                                     let m =
                                       match k with
                                       | KOnly -> Nat.min (bsize p0) (bsize s)
                                       | KLeft -> bsize p0
                                       | KRight -> bsize s
                                     in
                                     if (<=) (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))))) m
                                     then CG
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
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
                          | CY ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (c5, r0) ->
                               (match c5 with
                                | CSingle (c6, lrest) ->
                                  let Pkt (lb, ln) = c6 in
                                  CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                                  lrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | CO ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (l0, c5) ->
                               (match c5 with
                                | CSingle (c6, rrest) ->
                                  let Pkt (rb, rn) = c6 in
                                  CSingle ((Pkt ((BPairO (n0, l0, rb)), rn)),
                                  rrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                       | BPairO (hn, lc, b') ->
                         let d2 = CPair (lc, (CSingle ((Pkt (b', n)), rr))) in
                         let Node (_, p2, s2) = hn in
                         Some (x,
                         (let n0 = Node (KOnly, (bapp lp (bapp ls p2)), s2) in
                          match if negb (chain_has_node d2)
                                then CG
                                else let Node (k, p0, s) = n0 in
                                     let m =
                                       match k with
                                       | KOnly -> Nat.min (bsize p0) (bsize s)
                                       | KLeft -> bsize p0
                                       | KRight -> bsize s
                                     in
                                     if (<=) (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ 0)))))))) m
                                     then CG
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
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
                          | CY ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (c5, r0) ->
                               (match c5 with
                                | CSingle (c6, lrest) ->
                                  let Pkt (lb, ln) = c6 in
                                  CSingle ((Pkt ((BPairY (n0, lb, r0)), ln)),
                                  lrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | CO ->
                            (match d2 with
                             | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                             | CSingle (c5, rrest) ->
                               let Pkt (rb, rn) = c5 in
                               CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
                             | CPair (l0, c5) ->
                               (match c5 with
                                | CSingle (c6, rrest) ->
                                  let Pkt (rb, rn) = c6 in
                                  CSingle ((Pkt ((BPairO (n0, l0, rb)), rn)),
                                  rrest)
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                          | _ -> CSingle ((Pkt (BHole, n0)), d2))))
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
  let Pkt (c0, n) = p in
  (match c0 with
   | BHole ->
     let Node (k, p0, s) = n in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', x0) = p2 in
        (match rest with
         | CEmpty ->
           Some
             ((let Node (k0, p3, s0) = n' in
               if (&&) (bis_empty p3) (bis_empty s0)
               then CEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p3) (bis_empty s0)
                       then CSingle ((Pkt (BHole, n')), CEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then CSingle ((Pkt (BHole, (Node (KOnly,
                                   (bapp p3 s0), bempty)))), CEmpty)
                            else CSingle ((Pkt (BHole, n')), CEmpty)
                     | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
             x0)
         | _ ->
           Some
             ((match if negb (chain_has_node rest)
                     then CG
                     else let Node (k0, p3, s0) = n' in
                          let m =
                            match k0 with
                            | KOnly -> Nat.min (bsize p3) (bsize s0)
                            | KLeft -> bsize p3
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
               | CY ->
                 (match rest with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (c1, r) ->
                    (match c1 with
                     | CSingle (c2, lrest) ->
                       let Pkt (lb, ln) = c2 in
                       CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                     | _ -> CSingle ((Pkt (BHole, n')), rest)))
               | CO ->
                 (match rest with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (l, c1) ->
                    (match c1 with
                     | CSingle (c2, rrest) ->
                       let Pkt (rb, rn) = c2 in
                       CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                     | _ -> CSingle ((Pkt (BHole, n')), rest)))
               | _ -> CSingle ((Pkt (BHole, n')), rest)),
             x0))
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', x0) = p2 in
           (match rest with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s0) = n' in
                  if (&&) (bis_empty p3) (bis_empty s0)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s0)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s0), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                x0)
            | _ ->
              Some
                ((match if negb (chain_has_node rest)
                        then CG
                        else let Node (k0, p3, s0) = n' in
                             let m =
                               match k0 with
                               | KOnly -> Nat.min (bsize p3) (bsize s0)
                               | KLeft -> bsize p3
                               | KRight -> bsize s0
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match rest with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n')), rest)))
                  | CO ->
                    (match rest with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), rest)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n')), rest)))
                  | _ -> CSingle ((Pkt (BHole, n')), rest)),
                x0))
         | None -> None))
   | BSingle (hn, b') ->
     let child = CSingle ((Pkt (b', n)), rest) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', x0) = p2 in
        (match child with
         | CEmpty ->
           Some
             ((let Node (k0, p3, s0) = n' in
               if (&&) (bis_empty p3) (bis_empty s0)
               then CEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p3) (bis_empty s0)
                       then CSingle ((Pkt (BHole, n')), CEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then CSingle ((Pkt (BHole, (Node (KOnly,
                                   (bapp p3 s0), bempty)))), CEmpty)
                            else CSingle ((Pkt (BHole, n')), CEmpty)
                     | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
             x0)
         | _ ->
           Some
             ((match if negb (chain_has_node child)
                     then CG
                     else let Node (k0, p3, s0) = n' in
                          let m =
                            match k0 with
                            | KOnly -> Nat.min (bsize p3) (bsize s0)
                            | KLeft -> bsize p3
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
               | CY ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (c1, r) ->
                    (match c1 with
                     | CSingle (c2, lrest) ->
                       let Pkt (lb, ln) = c2 in
                       CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | CO ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (l, c1) ->
                    (match c1 with
                     | CSingle (c2, rrest) ->
                       let Pkt (rb, rn) = c2 in
                       CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | _ -> CSingle ((Pkt (BHole, n')), child)),
             x0))
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', x0) = p2 in
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s0) = n' in
                  if (&&) (bis_empty p3) (bis_empty s0)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s0)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s0), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                x0)
            | _ ->
              Some
                ((match if negb (chain_has_node child)
                        then CG
                        else let Node (k0, p3, s0) = n' in
                             let m =
                               match k0 with
                               | KOnly -> Nat.min (bsize p3) (bsize s0)
                               | KLeft -> bsize p3
                               | KRight -> bsize s0
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | _ -> CSingle ((Pkt (BHole, n')), child)),
                x0))
         | None -> None))
   | BPairY (hn, b', rc) ->
     let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', x0) = p2 in
        (match child with
         | CEmpty ->
           Some
             ((let Node (k0, p3, s0) = n' in
               if (&&) (bis_empty p3) (bis_empty s0)
               then CEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p3) (bis_empty s0)
                       then CSingle ((Pkt (BHole, n')), CEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then CSingle ((Pkt (BHole, (Node (KOnly,
                                   (bapp p3 s0), bempty)))), CEmpty)
                            else CSingle ((Pkt (BHole, n')), CEmpty)
                     | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
             x0)
         | _ ->
           Some
             ((match if negb (chain_has_node child)
                     then CG
                     else let Node (k0, p3, s0) = n' in
                          let m =
                            match k0 with
                            | KOnly -> Nat.min (bsize p3) (bsize s0)
                            | KLeft -> bsize p3
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
               | CY ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (c1, r) ->
                    (match c1 with
                     | CSingle (c2, lrest) ->
                       let Pkt (lb, ln) = c2 in
                       CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | CO ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (l, c1) ->
                    (match c1 with
                     | CSingle (c2, rrest) ->
                       let Pkt (rb, rn) = c2 in
                       CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | _ -> CSingle ((Pkt (BHole, n')), child)),
             x0))
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', x0) = p2 in
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s0) = n' in
                  if (&&) (bis_empty p3) (bis_empty s0)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s0)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s0), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                x0)
            | _ ->
              Some
                ((match if negb (chain_has_node child)
                        then CG
                        else let Node (k0, p3, s0) = n' in
                             let m =
                               match k0 with
                               | KOnly -> Nat.min (bsize p3) (bsize s0)
                               | KLeft -> bsize p3
                               | KRight -> bsize s0
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | _ -> CSingle ((Pkt (BHole, n')), child)),
                x0))
         | None -> None))
   | BPairO (hn, lc, b') ->
     let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', x0) = p2 in
        (match child with
         | CEmpty ->
           Some
             ((let Node (k0, p3, s0) = n' in
               if (&&) (bis_empty p3) (bis_empty s0)
               then CEmpty
               else (match k0 with
                     | KOnly ->
                       if (||) (bis_empty p3) (bis_empty s0)
                       then CSingle ((Pkt (BHole, n')), CEmpty)
                       else if (||)
                                 (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                 (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ
                                   (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                            then CSingle ((Pkt (BHole, (Node (KOnly,
                                   (bapp p3 s0), bempty)))), CEmpty)
                            else CSingle ((Pkt (BHole, n')), CEmpty)
                     | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
             x0)
         | _ ->
           Some
             ((match if negb (chain_has_node child)
                     then CG
                     else let Node (k0, p3, s0) = n' in
                          let m =
                            match k0 with
                            | KOnly -> Nat.min (bsize p3) (bsize s0)
                            | KLeft -> bsize p3
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
               | CY ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (c1, r) ->
                    (match c1 with
                     | CSingle (c2, lrest) ->
                       let Pkt (lb, ln) = c2 in
                       CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | CO ->
                 (match child with
                  | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                  | CSingle (c1, rrest) ->
                    let Pkt (rb, rn) = c1 in
                    CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                  | CPair (l, c1) ->
                    (match c1 with
                     | CSingle (c2, rrest) ->
                       let Pkt (rb, rn) = c2 in
                       CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                     | _ -> CSingle ((Pkt (BHole, n')), child)))
               | _ -> CSingle ((Pkt (BHole, n')), child)),
             x0))
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', x0) = p2 in
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s0) = n' in
                  if (&&) (bis_empty p3) (bis_empty s0)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s0)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s0) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s0), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                x0)
            | _ ->
              Some
                ((match if negb (chain_has_node child)
                        then CG
                        else let Node (k0, p3, s0) = n' in
                             let m =
                               match k0 with
                               | KOnly -> Nat.min (bsize p3) (bsize s0)
                               | KLeft -> bsize p3
                               | KRight -> bsize s0
                             in
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  m
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
                  | CY ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (c1, r) ->
                       (match c1 with
                        | CSingle (c2, lrest) ->
                          let Pkt (lb, ln) = c2 in
                          CSingle ((Pkt ((BPairY (n', lb, r)), ln)), lrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | CO ->
                    (match child with
                     | CEmpty -> CSingle ((Pkt (BHole, n')), child)
                     | CSingle (c1, rrest) ->
                       let Pkt (rb, rn) = c1 in
                       CSingle ((Pkt ((BSingle (n', rb)), rn)), rrest)
                     | CPair (l, c1) ->
                       (match c1 with
                        | CSingle (c2, rrest) ->
                          let Pkt (rb, rn) = c2 in
                          CSingle ((Pkt ((BPairO (n', l, rb)), rn)), rrest)
                        | _ -> CSingle ((Pkt (BHole, n')), child)))
                  | _ -> CSingle ((Pkt (BHole, n')), child)),
                x0))
         | None -> None)))
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
                      let Pkt (c4, n) = pl in
                      (match c4 with
                       | BHole ->
                         let Node (_, p1, s1) = n in
                         Some
                         ((let n0 = Node (KOnly, p1, (bapp s1 (bapp rp rs)))
                           in
                           match if negb (chain_has_node rl)
                                 then CG
                                 else let Node (k, p0, s) = n0 in
                                      let m =
                                        match k with
                                        | KOnly ->
                                          Nat.min (bsize p0) (bsize s)
                                        | KLeft -> bsize p0
                                        | KRight -> bsize s
                                      in
                                      if (<=) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ 0)))))))) m
                                      then CG
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
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
                           | CY ->
                             (match rl with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), rl)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (c5, r0) ->
                                (match c5 with
                                 | CSingle (c6, lrest) ->
                                   let Pkt (lb, ln) = c6 in
                                   CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                   ln)), lrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), rl)))
                           | CO ->
                             (match rl with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), rl)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (l0, c5) ->
                                (match c5 with
                                 | CSingle (c6, rrest) ->
                                   let Pkt (rb, rn) = c6 in
                                   CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                   rn)), rrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), rl)))
                           | _ -> CSingle ((Pkt (BHole, n0)), rl)),
                         x)
                       | BSingle (hn, b') ->
                         let d1 = CSingle ((Pkt (b', n)), rl) in
                         let Node (_, p1, s1) = hn in
                         Some
                         ((let n0 = Node (KOnly, p1, (bapp s1 (bapp rp rs)))
                           in
                           match if negb (chain_has_node d1)
                                 then CG
                                 else let Node (k, p0, s) = n0 in
                                      let m =
                                        match k with
                                        | KOnly ->
                                          Nat.min (bsize p0) (bsize s)
                                        | KLeft -> bsize p0
                                        | KRight -> bsize s
                                      in
                                      if (<=) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ 0)))))))) m
                                      then CG
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
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
                           | CY ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (c5, r0) ->
                                (match c5 with
                                 | CSingle (c6, lrest) ->
                                   let Pkt (lb, ln) = c6 in
                                   CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                   ln)), lrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | CO ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (l0, c5) ->
                                (match c5 with
                                 | CSingle (c6, rrest) ->
                                   let Pkt (rb, rn) = c6 in
                                   CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                   rn)), rrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | _ -> CSingle ((Pkt (BHole, n0)), d1)),
                         x)
                       | BPairY (hn, b', rc) ->
                         let d1 = CPair ((CSingle ((Pkt (b', n)), rl)), rc) in
                         let Node (_, p1, s1) = hn in
                         Some
                         ((let n0 = Node (KOnly, p1, (bapp s1 (bapp rp rs)))
                           in
                           match if negb (chain_has_node d1)
                                 then CG
                                 else let Node (k, p0, s) = n0 in
                                      let m =
                                        match k with
                                        | KOnly ->
                                          Nat.min (bsize p0) (bsize s)
                                        | KLeft -> bsize p0
                                        | KRight -> bsize s
                                      in
                                      if (<=) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ 0)))))))) m
                                      then CG
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
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
                           | CY ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (c5, r0) ->
                                (match c5 with
                                 | CSingle (c6, lrest) ->
                                   let Pkt (lb, ln) = c6 in
                                   CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                   ln)), lrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | CO ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (l0, c5) ->
                                (match c5 with
                                 | CSingle (c6, rrest) ->
                                   let Pkt (rb, rn) = c6 in
                                   CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                   rn)), rrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | _ -> CSingle ((Pkt (BHole, n0)), d1)),
                         x)
                       | BPairO (hn, lc, b') ->
                         let d1 = CPair (lc, (CSingle ((Pkt (b', n)), rl))) in
                         let Node (_, p1, s1) = hn in
                         Some
                         ((let n0 = Node (KOnly, p1, (bapp s1 (bapp rp rs)))
                           in
                           match if negb (chain_has_node d1)
                                 then CG
                                 else let Node (k, p0, s) = n0 in
                                      let m =
                                        match k with
                                        | KOnly ->
                                          Nat.min (bsize p0) (bsize s)
                                        | KLeft -> bsize p0
                                        | KRight -> bsize s
                                      in
                                      if (<=) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ 0)))))))) m
                                      then CG
                                      else if (=) m (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
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
                           | CY ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (c5, r0) ->
                                (match c5 with
                                 | CSingle (c6, lrest) ->
                                   let Pkt (lb, ln) = c6 in
                                   CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                   ln)), lrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | CO ->
                             (match d1 with
                              | CEmpty -> CSingle ((Pkt (BHole, n0)), d1)
                              | CSingle (c5, rrest) ->
                                let Pkt (rb, rn) = c5 in
                                CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                rrest)
                              | CPair (l0, c5) ->
                                (match c5 with
                                 | CSingle (c6, rrest) ->
                                   let Pkt (rb, rn) = c6 in
                                   CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                   rn)), rrest)
                                 | _ -> CSingle ((Pkt (BHole, n0)), d1)))
                           | _ -> CSingle ((Pkt (BHole, n0)), d1)),
                         x))
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
  let Pkt (c, n) = p in
  (match c with
   | BHole ->
     let Node (k, p0, s) = n in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (cellF, n1) = p2 in
        let Node (k0, p3, s0) = n1 in
        (match beject s0 with
         | Some p4 ->
           let (s', x0) = p4 in
           let p5 = ((Node (k0, p3, s')), x0) in
           let (n2, cellB) = p5 in
           (match r with
            | CEmpty ->
              Some ((cellF, (Some cellB)),
                (let Node (k1, p6, s1) = n2 in
                 if (&&) (bis_empty p6) (bis_empty s1)
                 then CEmpty
                 else (match k1 with
                       | KOnly ->
                         if (||) (bis_empty p6) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n2)), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p6 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n2)), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
            | _ ->
              Some ((cellF, (Some cellB)),
                (match if negb (chain_has_node r)
                       then CG
                       else let Node (k1, p6, s1) = n2 in
                            let m =
                              match k1 with
                              | KOnly -> Nat.min (bsize p6) (bsize s1)
                              | KLeft -> bsize p6
                              | KRight -> bsize s1
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
                 | CY ->
                   (match r with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (c0, r0) ->
                      (match c0 with
                       | CSingle (c1, lrest) ->
                         let Pkt (lb, ln) = c1 in
                         CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), r)))
                 | CO ->
                   (match r with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (l, c0) ->
                      (match c0 with
                       | CSingle (c1, rrest) ->
                         let Pkt (rb, rn) = c1 in
                         CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), r)))
                 | _ -> CSingle ((Pkt (BHole, n2)), r))))
         | None ->
           (match beject p3 with
            | Some p4 ->
              let (p'0, x0) = p4 in
              let p5 = ((Node (k0, p'0, bempty)), x0) in
              let (n2, cellB) = p5 in
              (match r with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node r)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match r with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), r)))
                    | CO ->
                      (match r with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), r)))
                    | _ -> CSingle ((Pkt (BHole, n2)), r))))
            | None ->
              (match r with
               | CEmpty -> Some ((cellF, None), CEmpty)
               | _ -> None)))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (cellF, n1) = p2 in
           let Node (k0, p3, s0) = n1 in
           (match beject s0 with
            | Some p4 ->
              let (s'0, x0) = p4 in
              let p5 = ((Node (k0, p3, s'0)), x0) in
              let (n2, cellB) = p5 in
              (match r with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node r)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match r with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), r)))
                    | CO ->
                      (match r with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), r)))
                    | _ -> CSingle ((Pkt (BHole, n2)), r))))
            | None ->
              (match beject p3 with
               | Some p4 ->
                 let (p', x0) = p4 in
                 let p5 = ((Node (k0, p', bempty)), x0) in
                 let (n2, cellB) = p5 in
                 (match r with
                  | CEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let Node (k1, p6, s1) = n2 in
                       if (&&) (bis_empty p6) (bis_empty s1)
                       then CEmpty
                       else (match k1 with
                             | KOnly ->
                               if (||) (bis_empty p6) (bis_empty s1)
                               then CSingle ((Pkt (BHole, n2)), CEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then CSingle ((Pkt (BHole, (Node (KOnly,
                                           (bapp p6 s1), bempty)))), CEmpty)
                                    else CSingle ((Pkt (BHole, n2)), CEmpty)
                             | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
                  | _ ->
                    Some ((cellF, (Some cellB)),
                      (match if negb (chain_has_node r)
                             then CG
                             else let Node (k1, p6, s1) = n2 in
                                  let m =
                                    match k1 with
                                    | KOnly -> Nat.min (bsize p6) (bsize s1)
                                    | KLeft -> bsize p6
                                    | KRight -> bsize s1
                                  in
                                  if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) m
                                  then CG
                                  else if (=) m (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                       then CY
                                       else if (=) m (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ 0))))))
                                            then CO
                                            else CR with
                       | CY ->
                         (match r with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (c0, r0) ->
                            (match c0 with
                             | CSingle (c1, lrest) ->
                               let Pkt (lb, ln) = c1 in
                               CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)),
                               lrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), r)))
                       | CO ->
                         (match r with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), r)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (l, c0) ->
                            (match c0 with
                             | CSingle (c1, rrest) ->
                               let Pkt (rb, rn) = c1 in
                               CSingle ((Pkt ((BPairO (n2, l, rb)), rn)),
                               rrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), r)))
                       | _ -> CSingle ((Pkt (BHole, n2)), r))))
               | None ->
                 (match r with
                  | CEmpty -> Some ((cellF, None), CEmpty)
                  | _ -> None)))
         | None -> None))
   | BSingle (hn, b') ->
     let dd = CSingle ((Pkt (b', n)), r) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (cellF, n1) = p2 in
        let Node (k0, p3, s0) = n1 in
        (match beject s0 with
         | Some p4 ->
           let (s', x0) = p4 in
           let p5 = ((Node (k0, p3, s')), x0) in
           let (n2, cellB) = p5 in
           (match dd with
            | CEmpty ->
              Some ((cellF, (Some cellB)),
                (let Node (k1, p6, s1) = n2 in
                 if (&&) (bis_empty p6) (bis_empty s1)
                 then CEmpty
                 else (match k1 with
                       | KOnly ->
                         if (||) (bis_empty p6) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n2)), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p6 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n2)), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
            | _ ->
              Some ((cellF, (Some cellB)),
                (match if negb (chain_has_node dd)
                       then CG
                       else let Node (k1, p6, s1) = n2 in
                            let m =
                              match k1 with
                              | KOnly -> Nat.min (bsize p6) (bsize s1)
                              | KLeft -> bsize p6
                              | KRight -> bsize s1
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
                 | CY ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (c0, r0) ->
                      (match c0 with
                       | CSingle (c1, lrest) ->
                         let Pkt (lb, ln) = c1 in
                         CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | CO ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (l, c0) ->
                      (match c0 with
                       | CSingle (c1, rrest) ->
                         let Pkt (rb, rn) = c1 in
                         CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | _ -> CSingle ((Pkt (BHole, n2)), dd))))
         | None ->
           (match beject p3 with
            | Some p4 ->
              let (p'0, x0) = p4 in
              let p5 = ((Node (k0, p'0, bempty)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match dd with
               | CEmpty -> Some ((cellF, None), CEmpty)
               | _ -> None)))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (cellF, n1) = p2 in
           let Node (k0, p3, s0) = n1 in
           (match beject s0 with
            | Some p4 ->
              let (s'0, x0) = p4 in
              let p5 = ((Node (k0, p3, s'0)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match beject p3 with
               | Some p4 ->
                 let (p', x0) = p4 in
                 let p5 = ((Node (k0, p', bempty)), x0) in
                 let (n2, cellB) = p5 in
                 (match dd with
                  | CEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let Node (k1, p6, s1) = n2 in
                       if (&&) (bis_empty p6) (bis_empty s1)
                       then CEmpty
                       else (match k1 with
                             | KOnly ->
                               if (||) (bis_empty p6) (bis_empty s1)
                               then CSingle ((Pkt (BHole, n2)), CEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then CSingle ((Pkt (BHole, (Node (KOnly,
                                           (bapp p6 s1), bempty)))), CEmpty)
                                    else CSingle ((Pkt (BHole, n2)), CEmpty)
                             | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
                  | _ ->
                    Some ((cellF, (Some cellB)),
                      (match if negb (chain_has_node dd)
                             then CG
                             else let Node (k1, p6, s1) = n2 in
                                  let m =
                                    match k1 with
                                    | KOnly -> Nat.min (bsize p6) (bsize s1)
                                    | KLeft -> bsize p6
                                    | KRight -> bsize s1
                                  in
                                  if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) m
                                  then CG
                                  else if (=) m (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                       then CY
                                       else if (=) m (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ 0))))))
                                            then CO
                                            else CR with
                       | CY ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (c0, r0) ->
                            (match c0 with
                             | CSingle (c1, lrest) ->
                               let Pkt (lb, ln) = c1 in
                               CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)),
                               lrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | CO ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (l, c0) ->
                            (match c0 with
                             | CSingle (c1, rrest) ->
                               let Pkt (rb, rn) = c1 in
                               CSingle ((Pkt ((BPairO (n2, l, rb)), rn)),
                               rrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | _ -> CSingle ((Pkt (BHole, n2)), dd))))
               | None ->
                 (match dd with
                  | CEmpty -> Some ((cellF, None), CEmpty)
                  | _ -> None)))
         | None -> None))
   | BPairY (hn, b', rc) ->
     let dd = CPair ((CSingle ((Pkt (b', n)), r)), rc) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (cellF, n1) = p2 in
        let Node (k0, p3, s0) = n1 in
        (match beject s0 with
         | Some p4 ->
           let (s', x0) = p4 in
           let p5 = ((Node (k0, p3, s')), x0) in
           let (n2, cellB) = p5 in
           (match dd with
            | CEmpty ->
              Some ((cellF, (Some cellB)),
                (let Node (k1, p6, s1) = n2 in
                 if (&&) (bis_empty p6) (bis_empty s1)
                 then CEmpty
                 else (match k1 with
                       | KOnly ->
                         if (||) (bis_empty p6) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n2)), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p6 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n2)), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
            | _ ->
              Some ((cellF, (Some cellB)),
                (match if negb (chain_has_node dd)
                       then CG
                       else let Node (k1, p6, s1) = n2 in
                            let m =
                              match k1 with
                              | KOnly -> Nat.min (bsize p6) (bsize s1)
                              | KLeft -> bsize p6
                              | KRight -> bsize s1
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
                 | CY ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (c0, r0) ->
                      (match c0 with
                       | CSingle (c1, lrest) ->
                         let Pkt (lb, ln) = c1 in
                         CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | CO ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (l, c0) ->
                      (match c0 with
                       | CSingle (c1, rrest) ->
                         let Pkt (rb, rn) = c1 in
                         CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | _ -> CSingle ((Pkt (BHole, n2)), dd))))
         | None ->
           (match beject p3 with
            | Some p4 ->
              let (p'0, x0) = p4 in
              let p5 = ((Node (k0, p'0, bempty)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match dd with
               | CEmpty -> Some ((cellF, None), CEmpty)
               | _ -> None)))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (cellF, n1) = p2 in
           let Node (k0, p3, s0) = n1 in
           (match beject s0 with
            | Some p4 ->
              let (s'0, x0) = p4 in
              let p5 = ((Node (k0, p3, s'0)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match beject p3 with
               | Some p4 ->
                 let (p', x0) = p4 in
                 let p5 = ((Node (k0, p', bempty)), x0) in
                 let (n2, cellB) = p5 in
                 (match dd with
                  | CEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let Node (k1, p6, s1) = n2 in
                       if (&&) (bis_empty p6) (bis_empty s1)
                       then CEmpty
                       else (match k1 with
                             | KOnly ->
                               if (||) (bis_empty p6) (bis_empty s1)
                               then CSingle ((Pkt (BHole, n2)), CEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then CSingle ((Pkt (BHole, (Node (KOnly,
                                           (bapp p6 s1), bempty)))), CEmpty)
                                    else CSingle ((Pkt (BHole, n2)), CEmpty)
                             | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
                  | _ ->
                    Some ((cellF, (Some cellB)),
                      (match if negb (chain_has_node dd)
                             then CG
                             else let Node (k1, p6, s1) = n2 in
                                  let m =
                                    match k1 with
                                    | KOnly -> Nat.min (bsize p6) (bsize s1)
                                    | KLeft -> bsize p6
                                    | KRight -> bsize s1
                                  in
                                  if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) m
                                  then CG
                                  else if (=) m (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                       then CY
                                       else if (=) m (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ 0))))))
                                            then CO
                                            else CR with
                       | CY ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (c0, r0) ->
                            (match c0 with
                             | CSingle (c1, lrest) ->
                               let Pkt (lb, ln) = c1 in
                               CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)),
                               lrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | CO ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (l, c0) ->
                            (match c0 with
                             | CSingle (c1, rrest) ->
                               let Pkt (rb, rn) = c1 in
                               CSingle ((Pkt ((BPairO (n2, l, rb)), rn)),
                               rrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | _ -> CSingle ((Pkt (BHole, n2)), dd))))
               | None ->
                 (match dd with
                  | CEmpty -> Some ((cellF, None), CEmpty)
                  | _ -> None)))
         | None -> None))
   | BPairO (hn, lc, b') ->
     let dd = CPair (lc, (CSingle ((Pkt (b', n)), r))) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (cellF, n1) = p2 in
        let Node (k0, p3, s0) = n1 in
        (match beject s0 with
         | Some p4 ->
           let (s', x0) = p4 in
           let p5 = ((Node (k0, p3, s')), x0) in
           let (n2, cellB) = p5 in
           (match dd with
            | CEmpty ->
              Some ((cellF, (Some cellB)),
                (let Node (k1, p6, s1) = n2 in
                 if (&&) (bis_empty p6) (bis_empty s1)
                 then CEmpty
                 else (match k1 with
                       | KOnly ->
                         if (||) (bis_empty p6) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n2)), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p6 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n2)), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
            | _ ->
              Some ((cellF, (Some cellB)),
                (match if negb (chain_has_node dd)
                       then CG
                       else let Node (k1, p6, s1) = n2 in
                            let m =
                              match k1 with
                              | KOnly -> Nat.min (bsize p6) (bsize s1)
                              | KLeft -> bsize p6
                              | KRight -> bsize s1
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
                 | CY ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (c0, r0) ->
                      (match c0 with
                       | CSingle (c1, lrest) ->
                         let Pkt (lb, ln) = c1 in
                         CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | CO ->
                   (match dd with
                    | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                    | CSingle (c0, rrest) ->
                      let Pkt (rb, rn) = c0 in
                      CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                    | CPair (l, c0) ->
                      (match c0 with
                       | CSingle (c1, rrest) ->
                         let Pkt (rb, rn) = c1 in
                         CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                       | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                 | _ -> CSingle ((Pkt (BHole, n2)), dd))))
         | None ->
           (match beject p3 with
            | Some p4 ->
              let (p'0, x0) = p4 in
              let p5 = ((Node (k0, p'0, bempty)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match dd with
               | CEmpty -> Some ((cellF, None), CEmpty)
               | _ -> None)))
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (cellF, n1) = p2 in
           let Node (k0, p3, s0) = n1 in
           (match beject s0 with
            | Some p4 ->
              let (s'0, x0) = p4 in
              let p5 = ((Node (k0, p3, s'0)), x0) in
              let (n2, cellB) = p5 in
              (match dd with
               | CEmpty ->
                 Some ((cellF, (Some cellB)),
                   (let Node (k1, p6, s1) = n2 in
                    if (&&) (bis_empty p6) (bis_empty s1)
                    then CEmpty
                    else (match k1 with
                          | KOnly ->
                            if (||) (bis_empty p6) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n2)), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p6 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n2)), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
               | _ ->
                 Some ((cellF, (Some cellB)),
                   (match if negb (chain_has_node dd)
                          then CG
                          else let Node (k1, p6, s1) = n2 in
                               let m =
                                 match k1 with
                                 | KOnly -> Nat.min (bsize p6) (bsize s1)
                                 | KLeft -> bsize p6
                                 | KRight -> bsize s1
                               in
                               if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) m
                               then CG
                               else if (=) m (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0)))))))
                                    then CY
                                    else if (=) m (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ
                                              (Stdlib.Int.succ 0))))))
                                         then CO
                                         else CR with
                    | CY ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (c0, r0) ->
                         (match c0 with
                          | CSingle (c1, lrest) ->
                            let Pkt (lb, ln) = c1 in
                            CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)), lrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | CO ->
                      (match dd with
                       | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                       | CSingle (c0, rrest) ->
                         let Pkt (rb, rn) = c0 in
                         CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                       | CPair (l, c0) ->
                         (match c0 with
                          | CSingle (c1, rrest) ->
                            let Pkt (rb, rn) = c1 in
                            CSingle ((Pkt ((BPairO (n2, l, rb)), rn)), rrest)
                          | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                    | _ -> CSingle ((Pkt (BHole, n2)), dd))))
            | None ->
              (match beject p3 with
               | Some p4 ->
                 let (p', x0) = p4 in
                 let p5 = ((Node (k0, p', bempty)), x0) in
                 let (n2, cellB) = p5 in
                 (match dd with
                  | CEmpty ->
                    Some ((cellF, (Some cellB)),
                      (let Node (k1, p6, s1) = n2 in
                       if (&&) (bis_empty p6) (bis_empty s1)
                       then CEmpty
                       else (match k1 with
                             | KOnly ->
                               if (||) (bis_empty p6) (bis_empty s1)
                               then CSingle ((Pkt (BHole, n2)), CEmpty)
                               else if (||)
                                         (Nat.ltb (bsize p6) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                         (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           (Stdlib.Int.succ (Stdlib.Int.succ
                                           0))))))
                                    then CSingle ((Pkt (BHole, (Node (KOnly,
                                           (bapp p6 s1), bempty)))), CEmpty)
                                    else CSingle ((Pkt (BHole, n2)), CEmpty)
                             | _ -> CSingle ((Pkt (BHole, n2)), CEmpty))))
                  | _ ->
                    Some ((cellF, (Some cellB)),
                      (match if negb (chain_has_node dd)
                             then CG
                             else let Node (k1, p6, s1) = n2 in
                                  let m =
                                    match k1 with
                                    | KOnly -> Nat.min (bsize p6) (bsize s1)
                                    | KLeft -> bsize p6
                                    | KRight -> bsize s1
                                  in
                                  if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) m
                                  then CG
                                  else if (=) m (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                       then CY
                                       else if (=) m (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ
                                                 (Stdlib.Int.succ 0))))))
                                            then CO
                                            else CR with
                       | CY ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (c0, r0) ->
                            (match c0 with
                             | CSingle (c1, lrest) ->
                               let Pkt (lb, ln) = c1 in
                               CSingle ((Pkt ((BPairY (n2, lb, r0)), ln)),
                               lrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | CO ->
                         (match dd with
                          | CEmpty -> CSingle ((Pkt (BHole, n2)), dd)
                          | CSingle (c0, rrest) ->
                            let Pkt (rb, rn) = c0 in
                            CSingle ((Pkt ((BSingle (n2, rb)), rn)), rrest)
                          | CPair (l, c0) ->
                            (match c0 with
                             | CSingle (c1, rrest) ->
                               let Pkt (rb, rn) = c1 in
                               CSingle ((Pkt ((BPairO (n2, l, rb)), rn)),
                               rrest)
                             | _ -> CSingle ((Pkt (BHole, n2)), dd)))
                       | _ -> CSingle ((Pkt (BHole, n2)), dd))))
               | None ->
                 (match dd with
                  | CEmpty -> Some ((cellF, None), CEmpty)
                  | _ -> None)))
         | None -> None)))
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
                          then let Pkt (c3, n) = pr' in
                               (match c3 with
                                | BHole ->
                                  let Node (_, p2, s2) = n in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly,
                                     (bapp lp (bapp ls p2)), s2)
                                   in
                                   match if negb (chain_has_node rr')
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match rr' with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), rr')
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c4, r0) ->
                                        (match c4 with
                                         | CSingle (c5, lrest) ->
                                           let Pkt (lb, ln) = c5 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), rr')))
                                   | CO ->
                                     (match rr' with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), rr')
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c4) ->
                                        (match c4 with
                                         | CSingle (c5, rrest) ->
                                           let Pkt (rb, rn) = c5 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), rr')))
                                   | _ -> CSingle ((Pkt (BHole, n0)), rr')))
                                | BSingle (hn, b') ->
                                  let d2 = CSingle ((Pkt (b', n)), rr') in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly,
                                     (bapp lp (bapp ls p2)), s2)
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c4, r0) ->
                                        (match c4 with
                                         | CSingle (c5, lrest) ->
                                           let Pkt (lb, ln) = c5 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c4) ->
                                        (match c4 with
                                         | CSingle (c5, rrest) ->
                                           let Pkt (rb, rn) = c5 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | BPairY (hn, b', rc) ->
                                  let d2 = CPair ((CSingle ((Pkt (b', n)),
                                    rr')), rc)
                                  in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly,
                                     (bapp lp (bapp ls p2)), s2)
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c4, r0) ->
                                        (match c4 with
                                         | CSingle (c5, lrest) ->
                                           let Pkt (lb, ln) = c5 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c4) ->
                                        (match c4 with
                                         | CSingle (c5, rrest) ->
                                           let Pkt (rb, rn) = c5 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | BPairO (hn, lc, b') ->
                                  let d2 = CPair (lc, (CSingle ((Pkt (b',
                                    n)), rr')))
                                  in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly,
                                     (bapp lp (bapp ls p2)), s2)
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c4, r0) ->
                                        (match c4 with
                                         | CSingle (c5, lrest) ->
                                           let Pkt (lb, ln) = c5 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c4, rrest) ->
                                        let Pkt (rb, rn) = c4 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c4) ->
                                        (match c4 with
                                         | CSingle (c5, rrest) ->
                                           let Pkt (rb, rn) = c5 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2))))
                          else Some ((cellF, (Some cellB)), (CPair (l', r'))))
                     | _ ->
                       if Nat.ltb (bsize lp) (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))))
                       then let Pkt (c3, n) = pr' in
                            (match c3 with
                             | BHole ->
                               let Node (_, p2, s2) = n in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, (bapp lp (bapp ls p2)),
                                  s2)
                                in
                                match if negb (chain_has_node rr')
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match rr' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rr')
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c4, r0) ->
                                     (match c4 with
                                      | CSingle (c5, lrest) ->
                                        let Pkt (lb, ln) = c5 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rr')))
                                | CO ->
                                  (match rr' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rr')
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c4) ->
                                     (match c4 with
                                      | CSingle (c5, rrest) ->
                                        let Pkt (rb, rn) = c5 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rr')))
                                | _ -> CSingle ((Pkt (BHole, n0)), rr')))
                             | BSingle (hn, b') ->
                               let d2 = CSingle ((Pkt (b', n)), rr') in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, (bapp lp (bapp ls p2)),
                                  s2)
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c4, r0) ->
                                     (match c4 with
                                      | CSingle (c5, lrest) ->
                                        let Pkt (lb, ln) = c5 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c4) ->
                                     (match c4 with
                                      | CSingle (c5, rrest) ->
                                        let Pkt (rb, rn) = c5 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairY (hn, b', rc) ->
                               let d2 = CPair ((CSingle ((Pkt (b', n)),
                                 rr')), rc)
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, (bapp lp (bapp ls p2)),
                                  s2)
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c4, r0) ->
                                     (match c4 with
                                      | CSingle (c5, lrest) ->
                                        let Pkt (lb, ln) = c5 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c4) ->
                                     (match c4 with
                                      | CSingle (c5, rrest) ->
                                        let Pkt (rb, rn) = c5 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairO (hn, lc, b') ->
                               let d2 = CPair (lc, (CSingle ((Pkt (b', n)),
                                 rr')))
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, (bapp lp (bapp ls p2)),
                                  s2)
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c4, r0) ->
                                     (match c4 with
                                      | CSingle (c5, lrest) ->
                                        let Pkt (lb, ln) = c5 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c4, rrest) ->
                                     let Pkt (rb, rn) = c4 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c4) ->
                                     (match c4 with
                                      | CSingle (c5, rrest) ->
                                        let Pkt (rb, rn) = c5 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2))))
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
                          then let Pkt (c1, n) = pl' in
                               (match c1 with
                                | BHole ->
                                  let Node (_, p2, s2) = n in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly, p2,
                                     (bapp s2 (bapp rp rs)))
                                   in
                                   match if negb (chain_has_node rl')
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match rl' with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), rl')
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c2, r0) ->
                                        (match c2 with
                                         | CSingle (c7, lrest) ->
                                           let Pkt (lb, ln) = c7 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), rl')))
                                   | CO ->
                                     (match rl' with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), rl')
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c2) ->
                                        (match c2 with
                                         | CSingle (c7, rrest) ->
                                           let Pkt (rb, rn) = c7 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), rl')))
                                   | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                                | BSingle (hn, b') ->
                                  let d2 = CSingle ((Pkt (b', n)), rl') in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly, p2,
                                     (bapp s2 (bapp rp rs)))
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c2, r0) ->
                                        (match c2 with
                                         | CSingle (c7, lrest) ->
                                           let Pkt (lb, ln) = c7 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c2) ->
                                        (match c2 with
                                         | CSingle (c7, rrest) ->
                                           let Pkt (rb, rn) = c7 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | BPairY (hn, b', rc) ->
                                  let d2 = CPair ((CSingle ((Pkt (b', n)),
                                    rl')), rc)
                                  in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly, p2,
                                     (bapp s2 (bapp rp rs)))
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c2, r0) ->
                                        (match c2 with
                                         | CSingle (c7, lrest) ->
                                           let Pkt (lb, ln) = c7 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c2) ->
                                        (match c2 with
                                         | CSingle (c7, rrest) ->
                                           let Pkt (rb, rn) = c7 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | BPairO (hn, lc, b') ->
                                  let d2 = CPair (lc, (CSingle ((Pkt (b',
                                    n)), rl')))
                                  in
                                  let Node (_, p2, s2) = hn in
                                  Some ((cellF, (Some cellB)),
                                  (let n0 = Node (KOnly, p2,
                                     (bapp s2 (bapp rp rs)))
                                   in
                                   match if negb (chain_has_node d2)
                                         then CG
                                         else let Node (k, p1, s) = n0 in
                                              let m =
                                                match k with
                                                | KOnly ->
                                                  Nat.min (bsize p1) (bsize s)
                                                | KLeft -> bsize p1
                                                | KRight -> bsize s
                                              in
                                              if (<=) (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ
                                                   (Stdlib.Int.succ 0))))))))
                                                   m
                                              then CG
                                              else if (=) m (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        (Stdlib.Int.succ
                                                        0)))))))
                                                   then CY
                                                   else if (=) m
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             (Stdlib.Int.succ
                                                             0))))))
                                                        then CO
                                                        else CR with
                                   | CY ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (c2, r0) ->
                                        (match c2 with
                                         | CSingle (c7, lrest) ->
                                           let Pkt (lb, ln) = c7 in
                                           CSingle ((Pkt ((BPairY (n0, lb,
                                           r0)), ln)), lrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | CO ->
                                     (match d2 with
                                      | CEmpty ->
                                        CSingle ((Pkt (BHole, n0)), d2)
                                      | CSingle (c2, rrest) ->
                                        let Pkt (rb, rn) = c2 in
                                        CSingle ((Pkt ((BSingle (n0, rb)),
                                        rn)), rrest)
                                      | CPair (l0, c2) ->
                                        (match c2 with
                                         | CSingle (c7, rrest) ->
                                           let Pkt (rb, rn) = c7 in
                                           CSingle ((Pkt ((BPairO (n0, l0,
                                           rb)), rn)), rrest)
                                         | _ ->
                                           CSingle ((Pkt (BHole, n0)), d2)))
                                   | _ -> CSingle ((Pkt (BHole, n0)), d2))))
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
                       then let Pkt (c1, n) = pl' in
                            (match c1 with
                             | BHole ->
                               let Node (_, p2, s2) = n in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node rl')
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match rl' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rl')
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c7, lrest) ->
                                        let Pkt (lb, ln) = c7 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                                | CO ->
                                  (match rl' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rl')
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c7, rrest) ->
                                        let Pkt (rb, rn) = c7 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                                | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                             | BSingle (hn, b') ->
                               let d2 = CSingle ((Pkt (b', n)), rl') in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c7, lrest) ->
                                        let Pkt (lb, ln) = c7 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c7, rrest) ->
                                        let Pkt (rb, rn) = c7 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairY (hn, b', rc) ->
                               let d2 = CPair ((CSingle ((Pkt (b', n)),
                                 rl')), rc)
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c7, lrest) ->
                                        let Pkt (lb, ln) = c7 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c7, rrest) ->
                                        let Pkt (rb, rn) = c7 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairO (hn, lc, b') ->
                               let d2 = CPair (lc, (CSingle ((Pkt (b', n)),
                                 rl')))
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c7, lrest) ->
                                        let Pkt (lb, ln) = c7 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c7, rrest) ->
                                        let Pkt (rb, rn) = c7 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2))))
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
                       then let Pkt (c1, n) = pl' in
                            (match c1 with
                             | BHole ->
                               let Node (_, p2, s2) = n in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node rl')
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match rl' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rl')
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c3, lrest) ->
                                        let Pkt (lb, ln) = c3 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                                | CO ->
                                  (match rl' with
                                   | CEmpty ->
                                     CSingle ((Pkt (BHole, n0)), rl')
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c3, rrest) ->
                                        let Pkt (rb, rn) = c3 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                                | _ -> CSingle ((Pkt (BHole, n0)), rl')))
                             | BSingle (hn, b') ->
                               let d2 = CSingle ((Pkt (b', n)), rl') in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c3, lrest) ->
                                        let Pkt (lb, ln) = c3 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c3, rrest) ->
                                        let Pkt (rb, rn) = c3 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairY (hn, b', rc) ->
                               let d2 = CPair ((CSingle ((Pkt (b', n)),
                                 rl')), rc)
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c3, lrest) ->
                                        let Pkt (lb, ln) = c3 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c3, rrest) ->
                                        let Pkt (rb, rn) = c3 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                             | BPairO (hn, lc, b') ->
                               let d2 = CPair (lc, (CSingle ((Pkt (b', n)),
                                 rl')))
                               in
                               let Node (_, p2, s2) = hn in
                               Some ((cellF, (Some cellB)),
                               (let n0 = Node (KOnly, p2,
                                  (bapp s2 (bapp rp rs)))
                                in
                                match if negb (chain_has_node d2)
                                      then CG
                                      else let Node (k, p1, s) = n0 in
                                           let m =
                                             match k with
                                             | KOnly ->
                                               Nat.min (bsize p1) (bsize s)
                                             | KLeft -> bsize p1
                                             | KRight -> bsize s
                                           in
                                           if (<=) (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ
                                                (Stdlib.Int.succ 0)))))))) m
                                           then CG
                                           else if (=) m (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ
                                                     (Stdlib.Int.succ 0)))))))
                                                then CY
                                                else if (=) m
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          (Stdlib.Int.succ
                                                          0))))))
                                                     then CO
                                                     else CR with
                                | CY ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (c2, r0) ->
                                     (match c2 with
                                      | CSingle (c3, lrest) ->
                                        let Pkt (lb, ln) = c3 in
                                        CSingle ((Pkt ((BPairY (n0, lb, r0)),
                                        ln)), lrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | CO ->
                                  (match d2 with
                                   | CEmpty -> CSingle ((Pkt (BHole, n0)), d2)
                                   | CSingle (c2, rrest) ->
                                     let Pkt (rb, rn) = c2 in
                                     CSingle ((Pkt ((BSingle (n0, rb)), rn)),
                                     rrest)
                                   | CPair (l0, c2) ->
                                     (match c2 with
                                      | CSingle (c3, rrest) ->
                                        let Pkt (rb, rn) = c3 in
                                        CSingle ((Pkt ((BPairO (n0, l0, rb)),
                                        rn)), rrest)
                                      | _ -> CSingle ((Pkt (BHole, n0)), d2)))
                                | _ -> CSingle ((Pkt (BHole, n0)), d2))))
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
  (match if negb (chain_has_node rest)
         then CG
         else let Node (k, p0, s) = n in
              let m =
                match k with
                | KOnly -> Nat.min (bsize p0) (bsize s)
                | KLeft -> bsize p0
                | KRight -> bsize s
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

(** val push_chain_v2 : 'a1 stored -> 'a1 cchain -> 'a1 cchain **)

let rec push_chain_v2 s = function
| CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, (b1 s), bempty)))), CEmpty)
| CSingle (p, rest) ->
  let Pkt (c0, n) = p in
  (match c0 with
   | BHole ->
     let n0 =
       let Node (k, p0, suf) = n in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb (chain_has_node rest)
            then CG
            else let Node (k, p0, s0) = n0 in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
        (match rest with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (c1, r) ->
           (match c1 with
            | CSingle (c2, lrest) ->
              let Pkt (lb, ln) = c2 in
              CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
            | _ -> CSingle ((Pkt (BHole, n0)), rest)))
      | CO ->
        (match rest with
         | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
         | CPair (l, c1) ->
           (match c1 with
            | CSingle (c2, rrest) ->
              let Pkt (rb, rn) = c2 in
              CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
            | _ -> CSingle ((Pkt (BHole, n0)), rest)))
      | _ -> CSingle ((Pkt (BHole, n0)), rest))
   | BSingle (hn, b') ->
     let hn' =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb true
            then CG
            else let Node (k, p0, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
      | CG -> CSingle ((Pkt (BHole, hn')), (CSingle ((Pkt (b', n)), rest)))
      | CR -> CSingle ((Pkt (BHole, hn')), (CSingle ((Pkt (b', n)), rest)))
      | _ -> CSingle ((Pkt ((BSingle (hn', b')), n)), rest))
   | BPairY (hn, b', rc) ->
     let hn' =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb true
            then CG
            else let Node (k, p0, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
      | CY -> CSingle ((Pkt ((BPairY (hn', b', rc)), n)), rest)
      | CO ->
        (match rc with
         | CSingle (c1, rrest) ->
           let Pkt (rb, rn) = c1 in
           CSingle ((Pkt ((BPairO (hn', (CSingle ((Pkt (b', n)), rest)),
           rb)), rn)), rrest)
         | _ ->
           CSingle ((Pkt (BHole, hn')), (CPair ((CSingle ((Pkt (b', n)),
             rest)), rc))))
      | _ ->
        CSingle ((Pkt (BHole, hn')), (CPair ((CSingle ((Pkt (b', n)), rest)),
          rc))))
   | BPairO (hn, lc, b') ->
     let hn' =
       let Node (k, p0, suf) = hn in
       if bis_empty p0
       then Node (k, p0, (bpush s suf))
       else Node (k, (bpush s p0), suf)
     in
     (match if negb true
            then CG
            else let Node (k, p0, s0) = hn' in
                 let m =
                   match k with
                   | KOnly -> Nat.min (bsize p0) (bsize s0)
                   | KLeft -> bsize p0
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
         | CSingle (c1, lrest) ->
           let Pkt (lb, ln) = c1 in
           CSingle ((Pkt ((BPairY (hn', lb, (CSingle ((Pkt (b', n)),
           rest)))), ln)), lrest)
         | _ ->
           CSingle ((Pkt (BHole, hn')), (CPair (lc, (CSingle ((Pkt (b', n)),
             rest))))))
      | CO -> CSingle ((Pkt ((BPairO (hn', lc, b')), n)), rest)
      | _ ->
        CSingle ((Pkt (BHole, hn')), (CPair (lc, (CSingle ((Pkt (b', n)),
          rest)))))))
| CPair (l, r) -> CPair ((push_chain_v2 s l), r)

(** val inject_chain_v2 : 'a1 cchain -> 'a1 stored -> 'a1 cchain **)

let rec inject_chain_v2 c s =
  match c with
  | CEmpty -> CSingle ((Pkt (BHole, (Node (KOnly, bempty, (b1 s))))), CEmpty)
  | CSingle (p, rest) ->
    let Pkt (c0, n) = p in
    (match c0 with
     | BHole ->
       let n0 =
         let Node (k, p0, suf) = n in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb (chain_has_node rest)
              then CG
              else let Node (k, p0, s0) = n0 in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
          (match rest with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (c1, r) ->
             (match c1 with
              | CSingle (c2, lrest) ->
                let Pkt (lb, ln) = c2 in
                CSingle ((Pkt ((BPairY (n0, lb, r)), ln)), lrest)
              | _ -> CSingle ((Pkt (BHole, n0)), rest)))
        | CO ->
          (match rest with
           | CEmpty -> CSingle ((Pkt (BHole, n0)), rest)
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BSingle (n0, rb)), rn)), rrest)
           | CPair (l, c1) ->
             (match c1 with
              | CSingle (c2, rrest) ->
                let Pkt (rb, rn) = c2 in
                CSingle ((Pkt ((BPairO (n0, l, rb)), rn)), rrest)
              | _ -> CSingle ((Pkt (BHole, n0)), rest)))
        | _ -> CSingle ((Pkt (BHole, n0)), rest))
     | BSingle (hn, b') ->
       let hn' =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb true
              then CG
              else let Node (k, p0, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
        | CG -> CSingle ((Pkt (BHole, hn')), (CSingle ((Pkt (b', n)), rest)))
        | CR -> CSingle ((Pkt (BHole, hn')), (CSingle ((Pkt (b', n)), rest)))
        | _ -> CSingle ((Pkt ((BSingle (hn', b')), n)), rest))
     | BPairY (hn, b', rc) ->
       let hn' =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb true
              then CG
              else let Node (k, p0, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
        | CY -> CSingle ((Pkt ((BPairY (hn', b', rc)), n)), rest)
        | CO ->
          (match rc with
           | CSingle (c1, rrest) ->
             let Pkt (rb, rn) = c1 in
             CSingle ((Pkt ((BPairO (hn', (CSingle ((Pkt (b', n)), rest)),
             rb)), rn)), rrest)
           | _ ->
             CSingle ((Pkt (BHole, hn')), (CPair ((CSingle ((Pkt (b', n)),
               rest)), rc))))
        | _ ->
          CSingle ((Pkt (BHole, hn')), (CPair ((CSingle ((Pkt (b', n)),
            rest)), rc))))
     | BPairO (hn, lc, b') ->
       let hn' =
         let Node (k, p0, suf) = hn in
         if bis_empty suf
         then Node (k, (binject p0 s), suf)
         else Node (k, p0, (binject suf s))
       in
       (match if negb true
              then CG
              else let Node (k, p0, s0) = hn' in
                   let m =
                     match k with
                     | KOnly -> Nat.min (bsize p0) (bsize s0)
                     | KLeft -> bsize p0
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
           | CSingle (c1, lrest) ->
             let Pkt (lb, ln) = c1 in
             CSingle ((Pkt ((BPairY (hn', lb, (CSingle ((Pkt (b', n)),
             rest)))), ln)), lrest)
           | _ ->
             CSingle ((Pkt (BHole, hn')), (CPair (lc, (CSingle ((Pkt (b',
               n)), rest))))))
        | CO -> CSingle ((Pkt ((BPairO (hn', lc, b')), n)), rest)
        | _ ->
          CSingle ((Pkt (BHole, hn')), (CPair (lc, (CSingle ((Pkt (b', n)),
            rest)))))))
  | CPair (l, r) -> CPair (l, (inject_chain_v2 r s))

(** val cad_push_v2 : 'a1 -> 'a1 cadeque -> 'a1 cadeque **)

let cad_push_v2 x d =
  push_chain_v2 (SGround x) d

(** val cad_inject_v2 : 'a1 cadeque -> 'a1 -> 'a1 cadeque **)

let cad_inject_v2 d x =
  inject_chain_v2 d (SGround x)

(** val cad_pop_v2 : 'a1 cadeque -> ('a1 * 'a1 cadeque) option **)

let cad_pop_v2 d = match d with
| CEmpty -> None
| CSingle (p, rest) ->
  let Pkt (c, n) = p in
  (match c with
   | BHole ->
     let Node (k, p0, s) = n in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (s0, n') = p2 in
        (match s0 with
         | SGround a ->
           (match rest with
            | CEmpty ->
              Some (a,
                (let Node (k0, p3, s1) = n' in
                 if (&&) (bis_empty p3) (bis_empty s1)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              (match match if negb (chain_has_node rest)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), rest))
                     | CY ->
                       (match rest with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                     | CO ->
                       (match rest with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 rest
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 rest
                               else repair_both_f BHole p3 s1 rest
                        | KLeft -> repair_front_f KLeft BHole p3 s1 rest
                        | KRight -> repair_back_f KRight BHole p3 s1 rest) with
               | Some d'' -> Some (a, d'')
               | None -> None))
         | _ -> None)
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (s0, n') = p2 in
           (match s0 with
            | SGround a ->
              (match rest with
               | CEmpty ->
                 Some (a,
                   (let Node (k0, p3, s1) = n' in
                    if (&&) (bis_empty p3) (bis_empty s1)
                    then CEmpty
                    else (match k0 with
                          | KOnly ->
                            if (||) (bis_empty p3) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n')), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p3 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n')), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
               | _ ->
                 (match match if negb (chain_has_node rest)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CY ->
                          (match rest with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), rest))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                        | CO ->
                          (match rest with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), rest))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 rest
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 rest
                                  else repair_both_f BHole p3 s1 rest
                           | KLeft -> repair_front_f KLeft BHole p3 s1 rest
                           | KRight -> repair_back_f KRight BHole p3 s1 rest) with
                  | Some d'' -> Some (a, d'')
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BSingle (hn, b') ->
     let child = CSingle ((Pkt (b', n)), rest) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (s0, n') = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some (a,
                (let Node (k0, p3, s1) = n' in
                 if (&&) (bis_empty p3) (bis_empty s1)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (a, d'')
               | None -> None))
         | _ -> None)
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (s0, n') = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some (a,
                   (let Node (k0, p3, s1) = n' in
                    if (&&) (bis_empty p3) (bis_empty s1)
                    then CEmpty
                    else (match k0 with
                          | KOnly ->
                            if (||) (bis_empty p3) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n')), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p3 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n')), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (a, d'')
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BPairY (hn, b', rc) ->
     let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (s0, n') = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some (a,
                (let Node (k0, p3, s1) = n' in
                 if (&&) (bis_empty p3) (bis_empty s1)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (a, d'')
               | None -> None))
         | _ -> None)
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (s0, n') = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some (a,
                   (let Node (k0, p3, s1) = n' in
                    if (&&) (bis_empty p3) (bis_empty s1)
                    then CEmpty
                    else (match k0 with
                          | KOnly ->
                            if (||) (bis_empty p3) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n')), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p3 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n')), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (a, d'')
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BPairO (hn, lc, b') ->
     let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
     let Node (k, p0, s) = hn in
     (match bpop p0 with
      | Some p1 ->
        let (x, p') = p1 in
        let p2 = (x, (Node (k, p', s))) in
        let (s0, n') = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some (a,
                (let Node (k0, p3, s1) = n' in
                 if (&&) (bis_empty p3) (bis_empty s1)
                 then CEmpty
                 else (match k0 with
                       | KOnly ->
                         if (||) (bis_empty p3) (bis_empty s1)
                         then CSingle ((Pkt (BHole, n')), CEmpty)
                         else if (||)
                                   (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                                   (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
                              then CSingle ((Pkt (BHole, (Node (KOnly,
                                     (bapp p3 s1), bempty)))), CEmpty)
                              else CSingle ((Pkt (BHole, n')), CEmpty)
                       | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (a, d'')
               | None -> None))
         | _ -> None)
      | None ->
        (match bpop s with
         | Some p1 ->
           let (x, s') = p1 in
           let p2 = (x, (Node (k, p0, s'))) in
           let (s0, n') = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some (a,
                   (let Node (k0, p3, s1) = n' in
                    if (&&) (bis_empty p3) (bis_empty s1)
                    then CEmpty
                    else (match k0 with
                          | KOnly ->
                            if (||) (bis_empty p3) (bis_empty s1)
                            then CSingle ((Pkt (BHole, n')), CEmpty)
                            else if (||)
                                      (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                      (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0))))))
                                 then CSingle ((Pkt (BHole, (Node (KOnly,
                                        (bapp p3 s1), bempty)))), CEmpty)
                                 else CSingle ((Pkt (BHole, n')), CEmpty)
                          | _ -> CSingle ((Pkt (BHole, n')), CEmpty))))
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (a, d'')
                  | None -> None))
            | _ -> None)
         | None -> None)))
| CPair (_, _) ->
  (match pop_raw_f d with
   | Some p ->
     let (s, d') = p in
     (match s with
      | SGround x ->
        (match repair_pop_side_f d' with
         | Some d'' -> Some (x, d'')
         | None -> None)
      | _ -> None)
   | None -> None)

(** val cad_eject_v2 : 'a1 cadeque -> ('a1 cadeque * 'a1) option **)

let cad_eject_v2 d = match d with
| CEmpty -> None
| CSingle (p, rest) ->
  let Pkt (c, n) = p in
  (match c with
   | BHole ->
     let Node (k, p0, s) = n in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', s0) = p2 in
        (match s0 with
         | SGround a ->
           (match rest with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s1) = n' in
                  if (&&) (bis_empty p3) (bis_empty s1)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s1)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s1), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                a)
            | _ ->
              (match match if negb (chain_has_node rest)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), rest))
                     | CY ->
                       (match rest with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                     | CO ->
                       (match rest with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 rest
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 rest
                               else repair_both_f BHole p3 s1 rest
                        | KLeft -> repair_front_f KLeft BHole p3 s1 rest
                        | KRight -> repair_back_f KRight BHole p3 s1 rest) with
               | Some d'' -> Some (d'', a)
               | None -> None))
         | _ -> None)
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', s0) = p2 in
           (match s0 with
            | SGround a ->
              (match rest with
               | CEmpty ->
                 Some
                   ((let Node (k0, p3, s1) = n' in
                     if (&&) (bis_empty p3) (bis_empty s1)
                     then CEmpty
                     else (match k0 with
                           | KOnly ->
                             if (||) (bis_empty p3) (bis_empty s1)
                             then CSingle ((Pkt (BHole, n')), CEmpty)
                             else if (||)
                                       (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                       (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                  then CSingle ((Pkt (BHole, (Node (KOnly,
                                         (bapp p3 s1), bempty)))), CEmpty)
                                  else CSingle ((Pkt (BHole, n')), CEmpty)
                           | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                   a)
               | _ ->
                 (match match if negb (chain_has_node rest)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), rest))
                        | CY ->
                          (match rest with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), rest))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                        | CO ->
                          (match rest with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), rest))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), rest))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 rest
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 rest
                                  else repair_both_f BHole p3 s1 rest
                           | KLeft -> repair_front_f KLeft BHole p3 s1 rest
                           | KRight -> repair_back_f KRight BHole p3 s1 rest) with
                  | Some d'' -> Some (d'', a)
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BSingle (hn, b') ->
     let child = CSingle ((Pkt (b', n)), rest) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', s0) = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s1) = n' in
                  if (&&) (bis_empty p3) (bis_empty s1)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s1)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s1), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                a)
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (d'', a)
               | None -> None))
         | _ -> None)
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', s0) = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some
                   ((let Node (k0, p3, s1) = n' in
                     if (&&) (bis_empty p3) (bis_empty s1)
                     then CEmpty
                     else (match k0 with
                           | KOnly ->
                             if (||) (bis_empty p3) (bis_empty s1)
                             then CSingle ((Pkt (BHole, n')), CEmpty)
                             else if (||)
                                       (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                       (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                  then CSingle ((Pkt (BHole, (Node (KOnly,
                                         (bapp p3 s1), bempty)))), CEmpty)
                                  else CSingle ((Pkt (BHole, n')), CEmpty)
                           | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                   a)
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (d'', a)
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BPairY (hn, b', rc) ->
     let child = CPair ((CSingle ((Pkt (b', n)), rest)), rc) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', s0) = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s1) = n' in
                  if (&&) (bis_empty p3) (bis_empty s1)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s1)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s1), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                a)
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (d'', a)
               | None -> None))
         | _ -> None)
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', s0) = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some
                   ((let Node (k0, p3, s1) = n' in
                     if (&&) (bis_empty p3) (bis_empty s1)
                     then CEmpty
                     else (match k0 with
                           | KOnly ->
                             if (||) (bis_empty p3) (bis_empty s1)
                             then CSingle ((Pkt (BHole, n')), CEmpty)
                             else if (||)
                                       (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                       (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                  then CSingle ((Pkt (BHole, (Node (KOnly,
                                         (bapp p3 s1), bempty)))), CEmpty)
                                  else CSingle ((Pkt (BHole, n')), CEmpty)
                           | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                   a)
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (d'', a)
                  | None -> None))
            | _ -> None)
         | None -> None))
   | BPairO (hn, lc, b') ->
     let child = CPair (lc, (CSingle ((Pkt (b', n)), rest))) in
     let Node (k, p0, s) = hn in
     (match beject s with
      | Some p1 ->
        let (s', x) = p1 in
        let p2 = ((Node (k, p0, s')), x) in
        let (n', s0) = p2 in
        (match s0 with
         | SGround a ->
           (match child with
            | CEmpty ->
              Some
                ((let Node (k0, p3, s1) = n' in
                  if (&&) (bis_empty p3) (bis_empty s1)
                  then CEmpty
                  else (match k0 with
                        | KOnly ->
                          if (||) (bis_empty p3) (bis_empty s1)
                          then CSingle ((Pkt (BHole, n')), CEmpty)
                          else if (||)
                                    (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                                    (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      (Stdlib.Int.succ (Stdlib.Int.succ
                                      0))))))
                               then CSingle ((Pkt (BHole, (Node (KOnly,
                                      (bapp p3 s1), bempty)))), CEmpty)
                               else CSingle ((Pkt (BHole, n')), CEmpty)
                        | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                a)
            | _ ->
              (match match if negb (chain_has_node child)
                           then CG
                           else let Node (k0, p3, s1) = n' in
                                let m =
                                  match k0 with
                                  | KOnly -> Nat.min (bsize p3) (bsize s1)
                                  | KLeft -> bsize p3
                                  | KRight -> bsize s1
                                in
                                if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     (Stdlib.Int.succ (Stdlib.Int.succ
                                     0)))))))) m
                                then CG
                                else if (=) m (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          (Stdlib.Int.succ (Stdlib.Int.succ
                                          0)))))))
                                     then CY
                                     else if (=) m (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ
                                               (Stdlib.Int.succ 0))))))
                                          then CO
                                          else CR with
                     | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                     | CY ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (c0, r) ->
                          (match c0 with
                           | CSingle (c1, lrest) ->
                             let Pkt (lb, ln) = c1 in
                             repair_packet_f (Pkt ((BPairY (n', lb, r)), ln))
                               lrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CO ->
                       (match child with
                        | CEmpty -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CSingle (c0, rrest) ->
                          let Pkt (rb, rn) = c0 in
                          repair_packet_f (Pkt ((BSingle (n', rb)), rn)) rrest
                        | CPair (l, c0) ->
                          (match c0 with
                           | CSingle (c1, rrest) ->
                             let Pkt (rb, rn) = c1 in
                             repair_packet_f (Pkt ((BPairO (n', l, rb)), rn))
                               rrest
                           | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                     | CR ->
                       let Node (k0, p3, s1) = n' in
                       (match k0 with
                        | KOnly ->
                          if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                               (bsize s1)
                          then repair_front_f KOnly BHole p3 s1 child
                          else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    (Stdlib.Int.succ (Stdlib.Int.succ
                                    0)))))))) (bsize p3)
                               then repair_back_f KOnly BHole p3 s1 child
                               else repair_both_f BHole p3 s1 child
                        | KLeft -> repair_front_f KLeft BHole p3 s1 child
                        | KRight -> repair_back_f KRight BHole p3 s1 child) with
               | Some d'' -> Some (d'', a)
               | None -> None))
         | _ -> None)
      | None ->
        (match beject p0 with
         | Some p1 ->
           let (p', x) = p1 in
           let p2 = ((Node (k, p', bempty)), x) in
           let (n', s0) = p2 in
           (match s0 with
            | SGround a ->
              (match child with
               | CEmpty ->
                 Some
                   ((let Node (k0, p3, s1) = n' in
                     if (&&) (bis_empty p3) (bis_empty s1)
                     then CEmpty
                     else (match k0 with
                           | KOnly ->
                             if (||) (bis_empty p3) (bis_empty s1)
                             then CSingle ((Pkt (BHole, n')), CEmpty)
                             else if (||)
                                       (Nat.ltb (bsize p3) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                       (Nat.ltb (bsize s1) (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         (Stdlib.Int.succ (Stdlib.Int.succ
                                         0))))))
                                  then CSingle ((Pkt (BHole, (Node (KOnly,
                                         (bapp p3 s1), bempty)))), CEmpty)
                                  else CSingle ((Pkt (BHole, n')), CEmpty)
                           | _ -> CSingle ((Pkt (BHole, n')), CEmpty))),
                   a)
               | _ ->
                 (match match if negb (chain_has_node child)
                              then CG
                              else let Node (k0, p3, s1) = n' in
                                   let m =
                                     match k0 with
                                     | KOnly -> Nat.min (bsize p3) (bsize s1)
                                     | KLeft -> bsize p3
                                     | KRight -> bsize s1
                                   in
                                   if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        (Stdlib.Int.succ (Stdlib.Int.succ
                                        0)))))))) m
                                   then CG
                                   else if (=) m (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
                                             (Stdlib.Int.succ
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
                        | CG -> Some (CSingle ((Pkt (BHole, n')), child))
                        | CY ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (c0, r) ->
                             (match c0 with
                              | CSingle (c1, lrest) ->
                                let Pkt (lb, ln) = c1 in
                                repair_packet_f (Pkt ((BPairY (n', lb, r)),
                                  ln)) lrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CO ->
                          (match child with
                           | CEmpty ->
                             Some (CSingle ((Pkt (BHole, n')), child))
                           | CSingle (c0, rrest) ->
                             let Pkt (rb, rn) = c0 in
                             repair_packet_f (Pkt ((BSingle (n', rb)), rn))
                               rrest
                           | CPair (l, c0) ->
                             (match c0 with
                              | CSingle (c1, rrest) ->
                                let Pkt (rb, rn) = c1 in
                                repair_packet_f (Pkt ((BPairO (n', l, rb)),
                                  rn)) rrest
                              | _ -> Some (CSingle ((Pkt (BHole, n')), child))))
                        | CR ->
                          let Node (k0, p3, s1) = n' in
                          (match k0 with
                           | KOnly ->
                             if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))
                                  (bsize s1)
                             then repair_front_f KOnly BHole p3 s1 child
                             else if (<=) (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0)))))))) (bsize p3)
                                  then repair_back_f KOnly BHole p3 s1 child
                                  else repair_both_f BHole p3 s1 child
                           | KLeft -> repair_front_f KLeft BHole p3 s1 child
                           | KRight -> repair_back_f KRight BHole p3 s1 child) with
                  | Some d'' -> Some (d'', a)
                  | None -> None))
            | _ -> None)
         | None -> None)))
| CPair (_, _) ->
  (match eject_raw_f d with
   | Some p ->
     let (d', s) = p in
     (match s with
      | SGround x ->
        (match repair_eject_side_f d' with
         | Some d'' -> Some (d'', x)
         | None -> None)
      | _ -> None)
   | None -> None)
