(** QCheck property-based tests for the **verified** [ktdeque]
    library — the OCaml extraction of the Rocq formalization.

    Mirrors the property suite in [test_deque4.ml] (which exercises the
    bench-helper hand-written variant) but targets the published
    public library [KTDeque.push_kt2 / pop_kt2 / inject_kt2 /
    eject_kt2] — the bounded-cascade worst-case-O(1) entry points.

    Strategy: generate random sequences of operations against a list
    reference; check that the deque's [kchain_to_list] equals the
    reference list at every step.  Catches the same bug classes as
    test_deque4 (sequence-law violations, empty-deque transitions,
    persistence violations), but on the certified library.

    This addresses the gap called out in [ocaml/README.md]: the
    QCheck/Monolith suites previously only validated the
    bench-helper. *)

open KTDeque

(* ------------------------------------------------------------------ *)
(* Adapter: wrap push_kt2/pop_kt2/inject_kt2/eject_kt2 to look like a *)
(* simple ['a t] interface, hiding the Coq_E.t element wrapper.       *)
(* ------------------------------------------------------------------ *)

module D = struct
  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let push (x : 'a) (d : 'a t) : 'a t =
    match push_kt2 (Coq_E.base x) d with
    | Some d' -> d'
    | None -> failwith "KTDeque.push_kt2: regularity violated"

  let inject (d : 'a t) (x : 'a) : 'a t =
    match inject_kt2 d (Coq_E.base x) with
    | Some d' -> d'
    | None -> failwith "KTDeque.inject_kt2: regularity violated"

  let pop (d : 'a t) : ('a * 'a t) option =
    match pop_kt2 d with
    | None -> None
    | Some (e, d') ->
        (match Coq_E.to_list e with
         | [x] -> Some (x, d')
         | _ -> failwith "pop_kt2: top element is not a base singleton")

  let eject (d : 'a t) : ('a t * 'a) option =
    match eject_kt2 d with
    | None -> None
    | Some (d', e) ->
        (match Coq_E.to_list e with
         | [x] -> Some (d', x)
         | _ -> failwith "eject_kt2: top element is not a base singleton")

  let to_list (d : 'a t) : 'a list = kchain_to_list d
end

(* List reference: same as Deque4_ref but local — ocaml/lib/ is not
 * a public dep and test_qcheck only cares about D's behavior. *)
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

let step_r (r : int R.t) (op : op) : int R.t =
  match op with
  | Push x -> R.push x r
  | Pop -> (match R.pop r with Some (_, r') -> r' | None -> r)
  | Inject x -> R.inject r x
  | Eject -> (match R.eject r with Some (r', _) -> r' | None -> r)

let run (ops : op list) : int list * int list * int option =
  let rec go i d r ops =
    let cl = D.to_list d in
    let rl = R.to_list r in
    if cl <> rl then (cl, rl, Some i)
    else match ops with
    | [] -> (cl, rl, None)
    | op :: rest -> go (i + 1) (step_d d op) (step_r r op) rest
  in
  go 0 D.empty R.empty ops

(* ------------------------------------------------------------------ *)
(* Properties                                                         *)
(* ------------------------------------------------------------------ *)

let prop_to_list_matches_reference =
  QCheck.Test.make ~count:1000
    ~name:"ktdeque: to_list equals list reference at every step"
    QCheck.(make ~print:pp_ops
              (QCheck.Gen.list_size QCheck.Gen.(int_range 1 100) gen_op))
    (fun ops ->
       let (cl, rl, diverge) = run ops in
       match diverge with
       | None -> cl = rl
       | Some _i -> false)

let prop_pop_empty =
  QCheck.Test.make ~count:1
    ~name:"ktdeque: pop empty returns None"
    QCheck.(make (QCheck.Gen.return ()))
    (fun () ->
       match D.pop D.empty with None -> true | Some _ -> false)

let prop_eject_empty =
  QCheck.Test.make ~count:1
    ~name:"ktdeque: eject empty returns None"
    QCheck.(make (QCheck.Gen.return ()))
    (fun () ->
       match D.eject D.empty with None -> true | Some _ -> false)

let prop_push_then_pop_id =
  QCheck.Test.make ~count:1000
    ~name:"ktdeque: push x then pop returns x and original"
    QCheck.(make QCheck.Gen.(int_range 0 1000))
    (fun x ->
       let d = D.push x D.empty in
       match D.pop d with
       | Some (y, d') -> y = x && D.to_list d' = []
       | None -> false)

let prop_inject_then_eject_id =
  QCheck.Test.make ~count:1000
    ~name:"ktdeque: inject x then eject returns x and original"
    QCheck.(make QCheck.Gen.(int_range 0 1000))
    (fun x ->
       let d = D.inject D.empty x in
       match D.eject d with
       | Some (d', y) -> y = x && D.to_list d' = []
       | None -> false)

let prop_persistence_simple =
  QCheck.Test.make ~count:1000
    ~name:"ktdeque: persistence — old handle still has its content"
    QCheck.(make ~print:pp_ops
              (QCheck.Gen.list_size QCheck.Gen.(int_range 1 50) gen_op))
    (fun ops ->
       let d = List.fold_left step_d D.empty ops in
       let snapshot = D.to_list d in
       let _d2 = D.push 99 d in
       D.to_list d = snapshot)

let () =
  let tests = [
    prop_to_list_matches_reference;
    prop_pop_empty;
    prop_eject_empty;
    prop_push_then_pop_id;
    prop_inject_then_eject_id;
    prop_persistence_simple;
  ] in
  exit (QCheck_base_runner.run_tests ~verbose:true tests)
