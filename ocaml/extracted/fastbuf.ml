(* Fastbuf — the production buffer behind the fast catenable deque.

   This module is the OCaml side of the extraction seam declared in
   rocq/KTDeque/Extract/ExtractionFast.v: each function implements the
   list semantics of the corresponding BufPrims.v primitive, with

     - all four end operations worst-case O(1): the storage is the
       *verified* §4 Kaplan–Tarjan deque (KTDeque.push_kt4 family,
       whose sequence-correctness and WC O(1) bounds are the deque
       keystone, rocq/KTDeque/DequePtr/DequeKeystone.v);
     - size O(1): an exact element count rides along, making the §6
       colour tests an int compare;
     - append O(min |a| |b|): the smaller side is folded into the
       larger — every §6 call site has a constant-bounded side under
       the regularity invariant J (the accounting audited in
       Catenable/Cost.v), so each reachable call is O(1).

   Elements are stored as level-0 element trees ([ElementTree.base]);
   [unbase] inverts that wrapping.  The [assert false] arms are
   unreachable for buffers built through this interface: every Fastbuf
   value originates from [empty] via kt4 operations, which preserve the
   deque regularity invariant, under which the kt4 ops are total
   (DequeKeystone). *)

type 'a t = { d : 'a KTDeque.kChain; n : int }

let empty : 'a t = { d = KTDeque.empty_kchain; n = 0 }

let size (b : 'a t) : int = b.n

let is_empty (b : 'a t) : bool = b.n = 0

(* inlined ElementTree.base: a level-0 tree is ExistT (0, x) — avoids a
   call + lets the constructor be allocated in place (no flambda here) *)
let base (x : 'a) : 'a KTDeque.Coq_E.t = KTDeque.ExistT (0, Obj.magic x)

let unbase (t : 'a KTDeque.Coq_E.t) : 'a =
  let KTDeque.ExistT (_, v) = t in
  Obj.magic v

let push (x : 'a) (b : 'a t) : 'a t =
  match KTDeque.push_kt4 (base x) b.d with
  | KTDeque.PushOk d -> { d; n = b.n + 1 }
  | KTDeque.PushFail -> assert false

let inject (b : 'a t) (x : 'a) : 'a t =
  match KTDeque.inject_kt4 b.d (base x) with
  | KTDeque.PushOk d -> { d; n = b.n + 1 }
  | KTDeque.PushFail -> assert false

let pop (b : 'a t) : ('a * 'a t) option =
  if b.n = 0 then None
  else
    match KTDeque.pop_kt4 b.d with
    | KTDeque.PopOk (x, d) -> Some (unbase x, { d; n = b.n - 1 })
    | KTDeque.PopFail -> assert false

let eject (b : 'a t) : ('a t * 'a) option =
  if b.n = 0 then None
  else
    match KTDeque.eject_kt4 b.d with
    | KTDeque.PopOk (x, d) -> Some ({ d; n = b.n - 1 }, unbase x)
    | KTDeque.PopFail -> assert false

let b1 (x : 'a) : 'a t = push x empty
let b2 (x : 'a) (y : 'a) : 'a t = push x (push y empty)
let b3 (x : 'a) (y : 'a) (z : 'a) : 'a t = push x (push y (push z empty))

(* front-to-back element list; O(n), used only by the bounded helpers *)
let to_list (b : 'a t) : 'a list = KTDeque.kchain_to_list b.d

let append (a : 'a t) (b : 'a t) : 'a t =
  if a.n = 0 then b
  else if b.n = 0 then a
  else if a.n <= b.n then
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
