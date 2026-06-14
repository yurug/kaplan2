(* Idiomatic wrapper over the Rocq-extracted §6 catenable deque
   (KTFlatCadeque, the [cad_*_x] family).  Elements are stored directly
   (the level/box discipline is internal), so there is no base/unbase. *)

module K = KTFlatCadeque

type 'a t = 'a K.fchain

let empty : 'a t = K.fcad_empty
let push x d = K.cad_push_x x d
let inject d x = K.cad_inject_x d x

let pop d =
  match K.cad_pop_x d with
  | Some (x, d') -> Some (x, d')
  | None -> None

let eject d =
  match K.cad_eject_x d with
  | Some (d', x) -> Some (d', x)
  | None -> None

let concat a b =
  match K.cad_concat_x a b with
  | Some c -> c
  | None -> assert false  (* totality: proven Some on regular inputs *)

let is_empty d = match K.cad_pop_x d with None -> true | Some _ -> false
let peek_front d = match K.cad_pop_x d with Some (x, _) -> Some x | None -> None
let peek_back d = match K.cad_eject_x d with Some (_, x) -> Some x | None -> None

(* to_list by front-to-back pop drain (no extracted walk is exported) *)
let to_list d =
  let rec go acc d =
    match K.cad_pop_x d with
    | Some (x, d') -> go (x :: acc) d'
    | None -> List.rev acc
  in
  go [] d

let length d =
  let rec go n d = match K.cad_pop_x d with Some (_, d') -> go (n+1) d' | None -> n in
  go 0 d

let of_list xs = List.fold_left inject empty xs
let iter f d = List.iter f (to_list d)
let fold_left f acc d = List.fold_left f acc (to_list d)
let fold_right f d acc = List.fold_right f (to_list d) acc
let to_seq d = List.to_seq (to_list d)
let of_seq s = Seq.fold_left inject empty s
