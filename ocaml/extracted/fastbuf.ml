(* Fastbuf — the production buffer behind the fast catenable deque.

   This module is the OCaml side of the extraction seam declared in
   rocq/KTDeque/Extract/ExtractionFast.v: each function implements the
   list semantics of the corresponding BufPrims.v primitive, with

     - all four end operations worst-case O(1): the storage is the
       SIZE-FUSED verified §4 Kaplan–Tarjan deque
       (rocq/KTDeque/DequePtr/SizedChain.v, extracted at
       kTSizedChain.ml).  [SChain] carries the element count fused
       into its top constructor — verified data-constructor fusion —
       so there is no wrapper record, push/inject return the chain
       bare (no result constructor), and [size] is a field read.
       Each sized op carries a [_spec] lemma in SizedChain.v reducing
       it to the keystone-proven kt4 op, so the deque keystone
       (sequence semantics + WC O(1)) describes this storage verbatim;
     - append O(min |a| |b|): the smaller side is folded into the
       larger — every §6 call site has a constant-bounded side under
       the regularity invariant J (the accounting audited in
       Catenable/Cost.v), so each reachable call is O(1).

   Elements are stored as level-0 element trees; [base]/[unbase] are
   the wrap/unwrap.  The fail arms of the sized ops return their input
   (a sentinel the §6 keystone proves unreachable on regular inputs). *)

open KTSizedChain

type 'a t = 'a sChain

let empty : 'a t = s_empty

let size (b : 'a t) : int =
  match b with
  | SEnding (n, _) -> n
  | SCons (n, _, _, _) -> n

let is_empty (b : 'a t) : bool = size b = 0

(* a level-0 element tree is ExistT (0, x) — allocated in place *)
let base (x : 'a) : 'a Coq0_E.t = ExistT (0, Obj.magic x)

let unbase (t : 'a Coq0_E.t) : 'a =
  let ExistT (_, v) = t in
  Obj.magic v

let push (x : 'a) (b : 'a t) : 'a t = push_s (base x) b

let inject (b : 'a t) (x : 'a) : 'a t = inject_s b (base x)

let pop (b : 'a t) : ('a * 'a t) option =
  match pop_s b with
  | SPopOk (x, b') -> Some (unbase x, b')
  | SPopFail -> None

let eject (b : 'a t) : ('a t * 'a) option =
  match eject_s b with
  | SPopOk (x, b') -> Some (b', unbase x)
  | SPopFail -> None

let b1 (x : 'a) : 'a t = push x empty
let b2 (x : 'a) (y : 'a) : 'a t = push x (push y empty)
let b3 (x : 'a) (y : 'a) (z : 'a) : 'a t = push x (push y (push z empty))

(* front-to-back element list; O(n), used only by the bounded helpers *)
let to_list (b : 'a t) : 'a list = s_to_list b

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
