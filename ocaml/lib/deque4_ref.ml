(** Reference implementation of Deque4: a list-based, O(n)-per-op
    sequence with the same API.  Used as the ground-truth oracle in
    QCheck and Monolith harnesses (per ADR-0009 + VWGP §9.1).

    NOT for production: O(n) per operation, but obviously correct.
*)

type 'a t = 'a list

let empty : 'a t = []

let is_empty : 'a t -> bool = function [] -> true | _ -> false

let push : 'a -> 'a t -> 'a t = fun x xs -> x :: xs

let pop : 'a t -> ('a * 'a t) option = function
  | [] -> None
  | x :: xs -> Some (x, xs)

let inject : 'a t -> 'a -> 'a t = fun xs x -> xs @ [x]

let eject : 'a t -> ('a t * 'a) option = fun xs ->
  match List.rev xs with
  | [] -> None
  | x :: rs -> Some (List.rev rs, x)

let to_list : 'a t -> 'a list = fun xs -> xs
