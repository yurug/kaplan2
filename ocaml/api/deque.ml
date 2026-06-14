(* Idiomatic wrapper over the Rocq-extracted §4 deque (KTDeque, the
   [push_kt4] family).  The extracted ops carry a level-tagged element
   (Coq_E.t) and a 2-constructor result type; this module hides both. *)

module K = KTDeque

type 'a t = 'a K.kChain

(* base/unbase: the extracted deque stores level-tagged elements; user
   values live at level 0, where [Coq_E.base x] / flatten round-trip. *)
let base : 'a -> 'a K.Coq_E.t = K.Coq_E.base
let unbase (e : 'a K.Coq_E.t) : 'a =
  match K.Coq_E.to_list e with
  | [ x ] -> x
  | _ -> assert false  (* a level-0 element flattens to a singleton *)

let empty : 'a t = K.empty_kchain

let push x d =
  match K.push_kt4 (base x) d with
  | K.PushOk d' -> d'
  | K.PushFail -> assert false  (* totality: proven Some on regular inputs *)

let inject d x =
  match K.inject_kt4 d (base x) with
  | K.PushOk d' -> d'
  | K.PushFail -> assert false

let pop d =
  match K.pop_kt4 d with
  | K.PopOk (e, d') -> Some (unbase e, d')
  | K.PopFail -> None

let eject d =
  match K.eject_kt4 d with
  | K.PopOk (e, d') -> Some (d', unbase e)
  | K.PopFail -> None

let is_empty d = match K.pop_kt4 d with K.PopFail -> true | K.PopOk _ -> false
let peek_front d = match K.pop_kt4 d with K.PopOk (e, _) -> Some (unbase e) | K.PopFail -> None
let peek_back d = match K.eject_kt4 d with K.PopOk (e, _) -> Some (unbase e) | K.PopFail -> None

let to_list (d : 'a t) : 'a list = K.kchain_to_list d
let length d = List.length (to_list d)
let of_list xs = List.fold_left inject empty xs
let iter f d = List.iter f (to_list d)
let fold_left f acc d = List.fold_left f acc (to_list d)
let fold_right f d acc = List.fold_right f (to_list d) acc
let to_seq d = List.to_seq (to_list d)
let of_seq s = Seq.fold_left inject empty s
