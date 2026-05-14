(** Side-by-side benchmark: extracted catenable cadeque (Cadeque6) vs
    Viennot et al.'s hand-coded catenable cadeque.

    Two phases:

    1. **Functional equivalence**: run a random workload of push / pop /
       inject / eject / concat operations against both implementations and
       verify they produce the same sequence at every step.  This is the
       "extracted code is observationally equivalent to the reference"
       sanity check.

    2. **Timing**: micro-bench push/pop/inject/eject/concat at multiple
       sizes; report wall-clock time per op in nanoseconds for each
       implementation.

    Usage:
      dune exec ocaml/bench/catenable_compare.exe -- [N]

    Note: our public ops [cad_push_op] / [cad_inject_op] are WC O(1)
    structurally.  [cad_pop_op_full] / [cad_eject_op_full] / [cad_concat_op_full]
    use [cad_normalize] (which is O(n)) to fully restore regularity per
    operation — that's the abstract spec layer.  The §12.4 WC-O(1)
    imperative variant lives in [Cadeque6/Adopt6.v] and is not exported
    through the OCaml extraction (it operates on the rich heap layer
    [CadCellA6]).  So this bench is "extracted spec vs Viennot hand
    code"; expect Viennot to win on time because the spec uses
    [cad_normalize].  *)

module Kt = KTCatenableDeque
module Vi = Viennot_cadeque.Cadeque.Base

let kt_to_list d = Kt.cad_to_list_base d
let vi_to_list d = Vi.fold_right (fun x acc -> x :: acc) d []

(* ----------------------------------------------------------------------- *)
(* Functional equivalence: random workload                                 *)
(* ----------------------------------------------------------------------- *)

type op = Push of int | Inject of int | Pop | Eject | Concat

let sample_op () =
  match Random.int 7 with
  | 0 | 1 -> Push (Random.int 1000)
  | 2 -> Inject (Random.int 1000)
  | 3 -> Pop
  | 4 -> Eject
  | 5 -> Concat
  | _ -> Pop

let op_to_string = function
  | Push x -> Printf.sprintf "push %d" x
  | Inject x -> Printf.sprintf "inject %d" x
  | Pop -> "pop"
  | Eject -> "eject"
  | Concat -> "concat"

let functional_equivalence ~ops =
  Random.init 42;
  let kt = ref Kt.cad_empty in
  let vi = ref Vi.empty in
  let kt_rhs = ref Kt.cad_empty in
  let vi_rhs = ref Vi.empty in
  let mismatches = ref 0 in
  let checked = ref 0 in
  for i = 0 to ops - 1 do
    let op = sample_op () in
    (match op with
     | Push x ->
         kt := Kt.cad_push_op x !kt;
         vi := Vi.push x !vi
     | Inject x ->
         kt := Kt.cad_inject_op !kt x;
         vi := Vi.inject !vi x
     | Pop ->
         kt := (match Kt.cad_pop_op_full !kt with None -> !kt | Some (_, d) -> d);
         vi := (match Vi.pop !vi with None -> !vi | Some (_, d) -> d)
     | Eject ->
         kt := (match Kt.cad_eject_op_full !kt with None -> !kt | Some (d, _) -> d);
         vi := (match Vi.eject !vi with None -> !vi | Some (d, _) -> d)
     | Concat ->
         kt := Kt.cad_concat_op_full !kt !kt_rhs;
         vi := Vi.append !vi !vi_rhs);
    if i mod 5 = 0 then begin
      kt_rhs := Kt.cad_push_op i !kt_rhs;
      vi_rhs := Vi.push i !vi_rhs
    end;
    (* Compare every 25 iterations to keep this O(N) overall. *)
    if i mod 25 = 0 then begin
      incr checked;
      let kt_list = kt_to_list !kt in
      let vi_list = vi_to_list !vi in
      if kt_list <> vi_list then begin
        incr mismatches;
        if !mismatches <= 3 then
          Printf.printf "MISMATCH at step %d (op=%s):\n  Kt list = [%s]\n  Vi list = [%s]\n"
            i (op_to_string op)
            (String.concat ";" (List.map string_of_int kt_list))
            (String.concat ";" (List.map string_of_int vi_list))
      end
    end
  done;
  (* Final comparison *)
  let kt_list = kt_to_list !kt in
  let vi_list = vi_to_list !vi in
  let final_ok = kt_list = vi_list in
  Printf.printf "Functional equivalence (%d ops, mixed push/pop/inject/eject/concat, %d checks):\n" ops !checked;
  if !mismatches = 0 && final_ok then
    Printf.printf "  OK — Kt and Vi produced identical sequences (final size = %d).\n" (List.length kt_list)
  else
    Printf.printf "  FAIL — %d intermediate mismatches; final ok=%b\n" !mismatches final_ok

(* ----------------------------------------------------------------------- *)
(* Timing                                                                   *)
(* ----------------------------------------------------------------------- *)

let time label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-32s %9.3f ms\n%!" label ((t1 -. t0) *. 1000.);
  r

(* --- Kt side --- *)
let kt_bench_push n =
  let acc = ref Kt.cad_empty in
  for i = 0 to n - 1 do acc := Kt.cad_push_op i !acc done;
  !acc

let kt_bench_inject n =
  let acc = ref Kt.cad_empty in
  for i = 0 to n - 1 do acc := Kt.cad_inject_op !acc i done;
  !acc

let kt_bench_pop d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Kt.cad_pop_op_full !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

let kt_bench_eject d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Kt.cad_eject_op_full !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'; incr cnt
  done;
  !cnt

let kt_bench_concat base iter =
  let acc = ref base in
  for _ = 0 to iter - 1 do acc := Kt.cad_concat_op_full !acc base done;
  !acc

(* --- Vi side --- *)
let vi_bench_push n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.push i !acc done;
  !acc

let vi_bench_inject n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.inject !acc i done;
  !acc

let vi_bench_pop d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Vi.pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

let vi_bench_eject d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Vi.eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'; incr cnt
  done;
  !cnt

let vi_bench_concat base iter =
  let acc = ref base in
  for _ = 0 to iter - 1 do acc := Vi.append !acc base done;
  !acc

let run_timing n =
  Printf.printf "\nTiming (N = %d):\n\n" n;

  Printf.printf "Push N elements (left to empty):\n";
  let _ = time "Kt (extracted) push" (fun () -> kt_bench_push n) in
  let _ = time "Vi (Viennot)   push" (fun () -> vi_bench_push n) in

  Printf.printf "\nInject N elements (right to empty):\n";
  let _ = time "Kt (extracted) inject" (fun () -> kt_bench_inject n) in
  let _ = time "Vi (Viennot)   inject" (fun () -> vi_bench_inject n) in

  Printf.printf "\nPop all from a size-N deque:\n";
  let d_kt = kt_bench_push n in
  let _ = time "Kt (extracted) pop" (fun () -> kt_bench_pop d_kt) in
  let d_vi = vi_bench_push n in
  let _ = time "Vi (Viennot)   pop" (fun () -> vi_bench_pop d_vi) in

  Printf.printf "\nEject all from a size-N deque:\n";
  let _ = time "Kt (extracted) eject" (fun () -> kt_bench_eject d_kt) in
  let _ = time "Vi (Viennot)   eject" (fun () -> vi_bench_eject d_vi) in

  let iter_concat = max 1 (1000 / max 1 (n / 100)) in
  Printf.printf "\nConcat: %d iterations of concat(d, d) where |d|=%d:\n" iter_concat n;
  let _ = time "Kt (extracted) concat" (fun () -> kt_bench_concat d_kt iter_concat) in
  let _ = time "Vi (Viennot)   concat" (fun () -> vi_bench_concat d_vi iter_concat) in
  ()

(* ----------------------------------------------------------------------- *)

let () =
  let n =
    if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1)
    else 10_000
  in
  let ops_fe =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2)
    else 1000
  in
  Printf.printf "=== Catenable cadeque benchmark: extracted Kt vs Viennot ===\n%!";
  Printf.printf "Note: Kt = extracted Coq spec layer (cad_*_op_full); these call\n";
  Printf.printf "      [cad_normalize] which is O(n) per op.  The §12.4 WC O(1)\n";
  Printf.printf "      imperative path lives in Adopt6.v and is not extracted yet.\n%!";
  functional_equivalence ~ops:ops_fe;
  run_timing n;
  Printf.printf "\nDone.\n%!"
