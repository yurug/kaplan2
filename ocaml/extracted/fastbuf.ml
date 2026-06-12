(* Fastbuf — the production buffer behind the fast catenable deque.

   This module is the OCaml side of the extraction seam declared in
   rocq/KTDeque/Extract/ExtractionFast.v: each function implements the
   list semantics of the corresponding BufPrims.v primitive, with

     - all four end operations worst-case O(1): the storage is the
       CHECK-ERASED, size-fused verified §4 deque
       (rocq/KTDeque/DequePtr/ErasedOps.v, extracted at
       kTErasedChain.ml): the size rides in the top constructor
       (no wrapper record, [size] is a field read), push/inject return
       the chain bare, and the element trees carry NO runtime level
       discipline — leaves are unboxed (eraw.ml), pairing is one
       unchecked block, unpairing is blind field access.  Each erased
       op carries a success-conditional naturality lemma down to the
       keystone-proven kt4 op, so the deque keystone describes this
       storage on every input reachable from regular chains;
     - append O(min |a| |b|): the smaller side is folded into the
       larger — every §6 call site has a constant-bounded side under
       the regularity invariant J (the accounting audited in
       Catenable/Cost.v), so each reachable call is O(1).

   Elements are stored as level-0 element trees; [base]/[unbase] are
   the wrap/unwrap.  The fail arms of the sized ops return their input
   (a sentinel the §6 keystone proves unreachable on regular inputs). *)

open KTErasedChain

type 'a t = 'a Eraw.t gSChain

let empty : 'a t = egs_empty

let size (b : 'a t) : int =
  match b with
  | GSEnding (n, _) -> n
  | GSCons (n, _, _, _) -> n

let is_empty (b : 'a t) : bool = size b = 0

(* check-erased elements (eraw.ml): a level-0 element IS the value —
   zero allocation, zero runtime level checks *)
let base (x : 'a) : 'a Eraw.t = Eraw.leaf x

let unbase (t : 'a Eraw.t) : 'a = Eraw.unleaf t

let push (x : 'a) (b : 'a t) : 'a t = epush_s (base x) b

let inject (b : 'a t) (x : 'a) : 'a t = einject_s b (base x)

let pop (b : 'a t) : ('a * 'a t) option =
  match epop_s b with
  | GPopOk (x, b') -> Some (unbase x, b')
  | GPopFail -> None

let eject (b : 'a t) : ('a t * 'a) option =
  match eeject_s b with
  | GPopOk (x, b') -> Some (b', unbase x)
  | GPopFail -> None

let b1 (x : 'a) : 'a t = push x empty
let b2 (x : 'a) (y : 'a) : 'a t = push x (push y empty)
let b3 (x : 'a) (y : 'a) (z : 'a) : 'a t = push x (push y (push z empty))

(* front-to-back element list by pop-drain (each pop verified); O(n),
   used only by the bounded helpers and append's smaller side *)
let to_list (b : 'a t) : 'a list =
  let rec go acc b =
    match epop_s b with
    | GPopOk (x, b') -> go (unbase x :: acc) b'
    | GPopFail -> List.rev acc
  in
  go [] b

let append (a : 'a t) (b : 'a t) : 'a t =
  if size a = 0 then b
  else if size b = 0 then a
  else if size a <= size b then
    (* fold a's elements, back to front, onto b's front *)
    List.fold_right (fun x acc -> push x acc) (to_list a) b
  else
    (* fold b's elements, front to back, onto a's back *)
    List.fold_left (fun acc x -> inject acc x) a (to_list b)

let pop2 (b : 'a t) : (('a * 'a) * 'a t) option =
  match pop b with
  | Some (x, b1) -> (
      match pop b1 with
      | Some (y, b2) -> Some ((x, y), b2)
      | None -> None)
  | None -> None

let eject2 (b : 'a t) : (('a t * 'a) * 'a) option =
  match eject b with
  | Some (b1, z) -> (
      match eject b1 with
      | Some (b2, y) -> Some ((b2, y), z)
      | None -> None)
  | None -> None

let eject3 (b : 'a t) : ((('a t * 'a) * 'a) * 'a) option =
  match eject b with
  | Some (b1, c) -> (
      match eject b1 with
      | Some (b2, bb) -> (
          match eject b2 with
          | Some (b3, a) -> Some (((b3, a), bb), c)
          | None -> None)
      | None -> None)
  | None -> None

(* Coq argument order: bfold_right f z b / bfold_left f b z. *)
let fold_right (f : 'x -> 'z -> 'z) (z : 'z) (b : 'x t) : 'z =
  List.fold_right f (to_list b) z

let fold_left (f : 'z -> 'x -> 'z) (b : 'x t) (z : 'z) : 'z =
  List.fold_left f z (to_list b)
