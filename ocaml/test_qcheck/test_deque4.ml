(** QCheck property-based tests for Deque4.

    Strategy (per ADR-0009 + VWGP §9.1): generate random sequences of
    operations against a list reference; check that
    [to_list] of the candidate equals the reference list at every step.

    This catches:
    - sequence-law violations (push, pop, inject, eject swap or drop elements);
    - empty-deque behaviour (pop/eject on empty must return None);
    - persistence violations (replaying old handles must give the same result).

    Cross-references:
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
*)

module D = Ktdeque_bench_helpers.Deque4
module R = Ktdeque_bench_helpers.Deque4_ref

(* ------------------------------------------------------------------ *)
(* Operation language                                                   *)
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

(* ------------------------------------------------------------------ *)
(* Generators                                                           *)
(* ------------------------------------------------------------------ *)

let gen_op : op QCheck.Gen.t =
  let open QCheck.Gen in
  oneof [
    map (fun x -> Push x) (int_range 0 1000);
    return Pop;
    map (fun x -> Inject x) (int_range 0 1000);
    return Eject;
  ]

let gen_ops ~n : op list QCheck.Gen.t = QCheck.Gen.list_size (QCheck.Gen.return n) gen_op

(* ------------------------------------------------------------------ *)
(* Apply a sequence of operations to candidate and reference; return    *)
(* the final pair AND a witness if they ever diverge.                   *)
(* ------------------------------------------------------------------ *)

let step_d4 (d : int D.t) (op : op) : int D.t =
  match op with
  | Push x -> D.push x d
  | Pop -> (match D.pop d with Some (_, d') -> d' | None -> d)
  | Inject x -> D.inject d x
  | Eject -> (match D.eject d with Some (d', _) -> d' | None -> d)

let step_ref (r : int R.t) (op : op) : int R.t =
  match op with
  | Push x -> R.push x r
  | Pop -> (match R.pop r with Some (_, r') -> r' | None -> r)
  | Inject x -> R.inject r x
  | Eject -> (match R.eject r with Some (r', _) -> r' | None -> r)

(** [run ops] applies the ops to both impls and reports (candidate_list,
    reference_list, divergence_op_index_or_None). *)
let run (ops : op list) : int list * int list * int option =
  let rec go i d r ops =
    let cl = D.to_list d in
    let rl = R.to_list r in
    if cl <> rl then (cl, rl, Some i)
    else match ops with
    | [] -> (cl, rl, None)
    | op :: rest -> go (i + 1) (step_d4 d op) (step_ref r op) rest
  in
  go 0 D.empty R.empty ops

(* ------------------------------------------------------------------ *)
(* Properties                                                           *)
(* ------------------------------------------------------------------ *)

let prop_to_list_matches_reference =
  QCheck.Test.make ~count:1000 ~name:"P_obs: to_list equals list reference at every step"
    QCheck.(make ~print:pp_ops (QCheck.Gen.list_size QCheck.Gen.(int_range 1 100) gen_op))
    (fun ops ->
       let (cl, rl, diverge) = run ops in
       match diverge with
       | None -> cl = rl
       | Some _i -> false)

let prop_pop_empty =
  QCheck.Test.make ~count:1 ~name:"P2_T1: pop empty returns None"
    QCheck.(make (QCheck.Gen.return ()))
    (fun () ->
       match D.pop D.empty with
       | None -> true
       | Some _ -> false)

let prop_eject_empty =
  QCheck.Test.make ~count:1 ~name:"P4_T1: eject empty returns None"
    QCheck.(make (QCheck.Gen.return ()))
    (fun () ->
       match D.eject D.empty with
       | None -> true
       | Some _ -> false)

let prop_push_then_pop_id =
  QCheck.Test.make ~count:1000 ~name:"T21: push x then pop returns x and original"
    QCheck.(make QCheck.Gen.(int_range 0 1000))
    (fun x ->
       let d = D.push x D.empty in
       match D.pop d with
       | Some (y, d') -> y = x && D.to_list d' = []
       | None -> false)

let prop_inject_then_eject_id =
  QCheck.Test.make ~count:1000 ~name:"T_inj: inject x then eject returns x and original"
    QCheck.(make QCheck.Gen.(int_range 0 1000))
    (fun x ->
       let d = D.inject D.empty x in
       match D.eject d with
       | Some (d', y) -> y = x && D.to_list d' = []
       | None -> false)

let prop_persistence_simple =
  QCheck.Test.make ~count:1000 ~name:"T15: persistence — old handle still has its content"
    QCheck.(make ~print:pp_ops (QCheck.Gen.list_size QCheck.Gen.(int_range 1 50) gen_op))
    (fun ops ->
       let d = List.fold_left step_d4 D.empty ops in
       let snapshot = D.to_list d in
       (* mutate via more pushes *)
       let d2 = D.push 99 d in
       let _ = d2 in
       (* old [d] must still have its snapshot *)
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
  let cell = QCheck.Test.make_cell ~count:1 ~name:"dummy" QCheck.unit (fun () -> true) in
  let _ = cell in
  exit (QCheck_base_runner.run_tests ~verbose:true tests)
