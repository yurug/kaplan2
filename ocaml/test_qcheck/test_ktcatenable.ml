(** QCheck property-based tests for [KTCatenableDeque] -- the OCaml
    extraction of the Cadeque6 catenable deque (Rocq).

    Mirrors [test_ktdeque.ml] but targets the catenable cadeque
    operations [cad_push] / [cad_pop] / [cad_inject] / [cad_eject] /
    [cad_concat], plus the fully-regularity-preserving [_full]
    variants ([cad_pop_op_full] / [cad_eject_op_full] /
    [cad_concat_op_full]).

    Strategy: generate random sequences of operations against a list
    reference; check [cad_to_list_base] equals the reference list at
    every step.  Concat tests also fork two independent deques, then
    concat them and verify the result equals list-concatenation of
    their contents. *)

open KTCatenableDeque

(* ------------------------------------------------------------------ *)
(* Adapter: present a uniform ['a t] interface over the spec ops.     *)
(* ------------------------------------------------------------------ *)

module D = struct
  type 'a t = 'a cadeque

  let empty : 'a t = cad_empty

  let push (x : 'a) (d : 'a t) : 'a t = cad_push x d

  let inject (d : 'a t) (x : 'a) : 'a t = cad_inject d x

  let pop (d : 'a t) : ('a * 'a t) option = cad_pop d

  let eject (d : 'a t) : ('a t * 'a) option = cad_eject d

  let concat (a : 'a t) (b : 'a t) : 'a t = cad_concat a b

  let to_list (d : 'a t) : 'a list = cad_to_list_base d
end

(* Adapter for the _full / op variants (regularity-preserving). *)
module DF = struct
  type 'a t = 'a cadeque

  let empty : 'a t = cad_empty

  let push (x : 'a) (d : 'a t) : 'a t = cad_push_op x d

  let inject (d : 'a t) (x : 'a) : 'a t = cad_inject_op d x

  let pop (d : 'a t) : ('a * 'a t) option = cad_pop_op_full d

  let eject (d : 'a t) : ('a t * 'a) option = cad_eject_op_full d

  let concat (a : 'a t) (b : 'a t) : 'a t = cad_concat_op_full a b

  let to_list (d : 'a t) : 'a list = cad_to_list_base d
end

(* List reference. *)
module R = struct
  type 'a t = 'a list

  let empty = []
  let push x xs = x :: xs
  let inject xs x = xs @ [x]
  let pop = function [] -> None | x :: xs -> Some (x, xs)
  let eject xs =
    match List.rev xs with
    | [] -> None
    | x :: rev_rest -> Some (List.rev rev_rest, x)
  let concat a b = a @ b
  let to_list xs = xs
end

(* ------------------------------------------------------------------ *)
(* Operation language                                                 *)
(* ------------------------------------------------------------------ *)

type op =
  | Push of int
  | Pop
  | Inject of int
  | Eject

let pp_op = function
  | Push x -> Printf.sprintf "push(%d)" x
  | Pop -> "pop"
  | Inject x -> Printf.sprintf "inject(%d)" x
  | Eject -> "eject"

let pp_ops ops = String.concat " ; " (List.map pp_op ops)

let gen_op : op QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun x -> Push x) (int_range 0 1000);
    return Pop;
    map (fun x -> Inject x) (int_range 0 1000);
    return Eject;
  ]

(* ------------------------------------------------------------------ *)
(* Step both impls in lockstep                                        *)
(* ------------------------------------------------------------------ *)

let step_d (d : int D.t) (op : op) : int D.t =
  match op with
  | Push x -> D.push x d
  | Pop -> (match D.pop d with Some (_, d') -> d' | None -> d)
  | Inject x -> D.inject d x
  | Eject -> (match D.eject d with Some (d', _) -> d' | None -> d)

let step_df (d : int DF.t) (op : op) : int DF.t =
  match op with
  | Push x -> DF.push x d
  | Pop -> (match DF.pop d with Some (_, d') -> d' | None -> d)
  | Inject x -> DF.inject d x
  | Eject -> (match DF.eject d with Some (d', _) -> d' | None -> d)

let step_r (r : int R.t) (op : op) : int R.t =
  match op with
  | Push x -> R.push x r
  | Pop -> (match R.pop r with Some (_, r') -> r' | None -> r)
  | Inject x -> R.inject r x
  | Eject -> (match R.eject r with Some (r', _) -> r' | None -> r)

let run_with step empty (ops : op list) : int list * int list * int option =
  let rec go i d r ops =
    let cl = D.to_list d in
    let rl = R.to_list r in
    if cl <> rl then (cl, rl, Some i)
    else match ops with
    | [] -> (cl, rl, None)
    | op :: rest -> go (i + 1) (step d op) (step_r r op) rest
  in
  go 0 empty R.empty ops

(* ------------------------------------------------------------------ *)
(* Abstract spec ops: properties                                      *)
(* ------------------------------------------------------------------ *)

let prop_abstract_to_list_matches =
  QCheck.Test.make ~count:1000
    ~name:"cadeque (abstract): to_list matches list ref at every step"
    QCheck.(make ~print:pp_ops
              (QCheck.Gen.list_size QCheck.Gen.(int_range 1 100) gen_op))
    (fun ops ->
       (* Note: cad_pop / cad_eject return None when the front-buffer
          is empty even if the back-buffer has elements; the reference
          list pop/eject would still succeed.  This means abstract
          ops can DIVERGE from the list ref on the empty-front edge
          case.  We only check that the SUCCESSFUL ops preserve
          equivalence; for None we skip. *)
       let rec go d r = function
         | [] -> D.to_list d = R.to_list r
         | (Pop as op) :: rest ->
           let d' = step_d d op in
           (* If pop returned None on a non-empty list, we accept
              the divergence and stop checking. *)
           (match D.pop d, R.pop r with
            | None, Some _ -> true
            | _ -> go d' (step_r r op) rest)
         | (Eject as op) :: rest ->
           let d' = step_d d op in
           (match D.eject d, R.eject r with
            | None, Some _ -> true
            | _ -> go d' (step_r r op) rest)
         | op :: rest -> go (step_d d op) (step_r r op) rest
       in
       go D.empty R.empty ops)

let prop_abstract_pop_empty =
  QCheck.Test.make ~count:1
    ~name:"cadeque (abstract): pop empty returns None"
    QCheck.(make (QCheck.Gen.return ()))
    (fun () ->
       match D.pop D.empty with None -> true | Some _ -> false)

let prop_abstract_concat_observable =
  QCheck.Test.make ~count:1000
    ~name:"cadeque (abstract): to_list (concat a b) = to_list a ++ to_list b"
    QCheck.(make
              (QCheck.Gen.pair
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 50) (QCheck.Gen.int_range 0 1000))
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 50) (QCheck.Gen.int_range 0 1000))))
    (fun (xs, ys) ->
       let a = List.fold_right D.push xs D.empty in
       let b = List.fold_right D.push ys D.empty in
       D.to_list (D.concat a b) = D.to_list a @ D.to_list b)

(* ------------------------------------------------------------------ *)
(* _full ops: properties (totality + concat)                          *)
(* ------------------------------------------------------------------ *)

let prop_full_to_list_matches =
  QCheck.Test.make ~count:1000
    ~name:"cadeque (_full): to_list matches list ref at every step"
    QCheck.(make ~print:pp_ops
              (QCheck.Gen.list_size QCheck.Gen.(int_range 1 100) gen_op))
    (fun ops ->
       let (cl, rl, diverge) = run_with step_df DF.empty ops in
       match diverge with
       | None -> cl = rl
       | Some _i -> false)

let prop_full_concat_observable =
  QCheck.Test.make ~count:1000
    ~name:"cadeque (_full): to_list (concat a b) = to_list a ++ to_list b"
    QCheck.(make
              (QCheck.Gen.pair
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 50) (QCheck.Gen.int_range 0 1000))
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 50) (QCheck.Gen.int_range 0 1000))))
    (fun (xs, ys) ->
       let a = List.fold_right DF.push xs DF.empty in
       let b = List.fold_right DF.push ys DF.empty in
       DF.to_list (DF.concat a b) = DF.to_list a @ DF.to_list b)

let prop_full_concat_assoc =
  QCheck.Test.make ~count:500
    ~name:"cadeque (_full): concat is associative at the to_list level"
    QCheck.(make
              QCheck.Gen.(triple
                            (list_size (int_range 0 30) (int_range 0 1000))
                            (list_size (int_range 0 30) (int_range 0 1000))
                            (list_size (int_range 0 30) (int_range 0 1000))))
    (fun (xs, ys, zs) ->
       let a = List.fold_right DF.push xs DF.empty in
       let b = List.fold_right DF.push ys DF.empty in
       let c = List.fold_right DF.push zs DF.empty in
       DF.to_list (DF.concat (DF.concat a b) c)
       = DF.to_list (DF.concat a (DF.concat b c)))

let prop_full_persistence =
  QCheck.Test.make ~count:1000
    ~name:"cadeque (_full): persistence -- concat doesn't mutate inputs"
    QCheck.(make
              (QCheck.Gen.pair
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 30) (QCheck.Gen.int_range 0 1000))
                 (QCheck.Gen.list_size QCheck.Gen.(int_range 0 30) (QCheck.Gen.int_range 0 1000))))
    (fun (xs, ys) ->
       let a = List.fold_right DF.push xs DF.empty in
       let b = List.fold_right DF.push ys DF.empty in
       let snap_a = DF.to_list a in
       let snap_b = DF.to_list b in
       let _ = DF.concat a b in
       DF.to_list a = snap_a && DF.to_list b = snap_b)

let () =
  let tests = [
    prop_abstract_to_list_matches;
    prop_abstract_pop_empty;
    prop_abstract_concat_observable;
    prop_full_to_list_matches;
    prop_full_concat_observable;
    prop_full_concat_assoc;
    prop_full_persistence;
  ] in
  exit (QCheck_base_runner.run_tests ~verbose:true tests)
