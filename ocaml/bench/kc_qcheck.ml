(** Property-based equivalence: Kc (KCadeque from Cadeque7) vs a
    simple OCaml [list] reference, under random workloads.

    For each of [num_runs] runs:
    - Pick a fresh random seed.
    - Apply [ops_per_run] random operations to both Kc and a list.
    - At every step, assert that [Kc.kcad_to_list kc = reference_list].
    - If any check fails, print the trace and exit non-zero.

    Operations: push, inject, pop, eject, concat (with the empty
    deque or with itself).

    This catches regressions in the [KCadequeShim] spill cache,
    Phase 5b's non-recursive push/inject, and the Phase 5d
    [Extract Inductive Buf6] override path. *)

module Kc = KCadeque

type op =
  | Push of int
  | Inject of int
  | Pop
  | Eject
  | ConcatSelf
  | ConcatEmpty
  | ConcatRight

let op_to_string = function
  | Push x -> Printf.sprintf "push %d" x
  | Inject x -> Printf.sprintf "inject %d" x
  | Pop -> "pop"
  | Eject -> "eject"
  | ConcatSelf -> "concat-self"
  | ConcatEmpty -> "concat-empty"
  | ConcatRight -> "concat-right"

(* Sample [op] but throttle ConcatSelf based on current size to keep
   total work polynomial.  Without the gate, repeated ConcatSelf
   doubles the deque exponentially and the list-reference [xs @ xs]
   eats memory before the test finishes. *)
let sample_op cur_size =
  match Random.int 10 with
  | 0 | 1 | 2 -> Push (Random.int 1000)
  | 3 | 4 | 5 -> Inject (Random.int 1000)
  | 6         -> Pop
  | 7         -> Eject
  | 8         -> if cur_size < 4_000 then ConcatSelf else Pop
  | _         -> if Random.bool () then ConcatEmpty else ConcatRight

let apply_op_kc kc = function
  | Push x      -> Kc.kcad_push x kc
  | Inject x    -> Kc.kcad_inject kc x
  | Pop         ->
      (match Kc.kcad_pop kc with
       | None       -> kc
       | Some (_, kc') -> kc')
  | Eject       ->
      (match Kc.kcad_eject kc with
       | None       -> kc
       | Some (kc', _) -> kc')
  | ConcatSelf  -> Kc.kcad_concat kc kc
  | ConcatEmpty -> Kc.kcad_concat kc Kc.kcad_empty
  | ConcatRight ->
      let small =
        Kc.kcad_push (Random.int 100)
          (Kc.kcad_push (Random.int 100) Kc.kcad_empty)
      in
      Kc.kcad_concat kc small

let apply_op_ref xs = function
  | Push x      -> x :: xs
  | Inject x    -> xs @ [x]
  | Pop         -> (match xs with [] -> [] | _ :: t -> t)
  | Eject       -> (match List.rev xs with
                    | [] -> []
                    | _ :: t -> List.rev t)
  | ConcatSelf  -> xs @ xs
  | ConcatEmpty -> xs
  | ConcatRight ->
      let small =
        let a = Random.int 100 in
        let b = Random.int 100 in
        [a; b]  (* must match the Kc construction order *)
      in
      xs @ small

let check_eq kc xs =
  let got = Kc.kcad_to_list kc in
  if got <> xs then begin
    Printf.eprintf "MISMATCH: Kc=%s ref=%s\n%!"
      (String.concat ";" (List.map string_of_int got))
      (String.concat ";" (List.map string_of_int xs));
    false
  end else true

let run_once ~seed ~ops_per_run =
  Random.init seed;
  let kc = ref Kc.kcad_empty in
  let xs = ref [] in
  let ops_trace = ref [] in
  let ok = ref true in
  for _ = 1 to ops_per_run do
    if !ok then begin
      let op = sample_op (List.length !xs) in
      ops_trace := op :: !ops_trace;
      (* ConcatRight requires both branches to consume the same two
         Random.int values, so factor it out and apply atomically. *)
      (match op with
       | ConcatRight ->
           let a = Random.int 100 in
           let b = Random.int 100 in
           let small_kc =
             Kc.kcad_push a (Kc.kcad_push b Kc.kcad_empty) in
           kc := Kc.kcad_concat !kc small_kc;
           xs := !xs @ [a; b]
       | _ ->
           kc := apply_op_kc !kc op;
           xs := apply_op_ref !xs op);
      if not (check_eq !kc !xs) then begin
        Printf.eprintf "FAIL seed=%d after ops: %s\n%!"
          seed
          (String.concat " ; "
             (List.map op_to_string (List.rev !ops_trace)));
        ok := false
      end
    end
  done;
  !ok

(* Persistence test: build a deque, fork two divergent branches via
   distinct ops on the SAME initial value, then verify each branch
   reflects only its own ops.  Catches accidental mutation of shared
   structure inside the Phase 5d shim. *)
let persistence_test ~ops_per_branch =
  Random.init 0xCAFE;
  let base =
    let acc = ref Kc.kcad_empty in
    for i = 0 to 200 do acc := Kc.kcad_push i !acc done;
    !acc
  in
  let base_xs = Kc.kcad_to_list base in
  (* Branch A: keep injecting odd numbers. *)
  let a = ref base in
  let a_xs = ref base_xs in
  for i = 1 to ops_per_branch do
    let v = 2 * i + 1 in
    a := Kc.kcad_inject !a v;
    a_xs := !a_xs @ [v]
  done;
  (* Branch B: keep pushing negative numbers. *)
  let b = ref base in
  let b_xs = ref base_xs in
  for i = 1 to ops_per_branch do
    let v = -i in
    b := Kc.kcad_push v !b;
    b_xs := v :: !b_xs
  done;
  (* All three (base, a, b) should still reflect their own state. *)
  let ok = ref true in
  if Kc.kcad_to_list base <> base_xs then begin
    Printf.eprintf "persistence: base changed!\n%!"; ok := false
  end;
  if Kc.kcad_to_list !a <> !a_xs then begin
    Printf.eprintf "persistence: branch A diverged from reference!\n%!"; ok := false
  end;
  if Kc.kcad_to_list !b <> !b_xs then begin
    Printf.eprintf "persistence: branch B diverged from reference!\n%!"; ok := false
  end;
  !ok

(* Concat-heavy stress test: builds a deque via many concats, applies
   a sequence of injects + pops, and verifies correctness against
   a list reference at every step.  This specifically exercises
   Phase 5c's Stored-cell wrap path: concat → KSingle with stored
   cells, subsequent injects stay in the packet, pop hits the
   fallback once then drains O(1) per op. *)
let concat_heavy_test ~num_concats ~per_chunk ~ops_after =
  Random.init 0xC0DE;
  let chunk_xs () =
    let xs = ref [] in
    for i = 0 to per_chunk - 1 do xs := i :: !xs done;
    !xs
  in
  let chunk () =
    List.fold_left (fun acc x -> Kc.kcad_push x acc) Kc.kcad_empty
      (List.rev (chunk_xs ()))
  in
  let k = ref Kc.kcad_empty in
  let ref_xs = ref [] in
  for _ = 1 to num_concats do
    let c = chunk () in
    k := Kc.kcad_concat !k c;
    ref_xs := !ref_xs @ chunk_xs ()
  done;
  let ok = ref true in
  if Kc.kcad_to_list !k <> !ref_xs then begin
    Printf.eprintf "concat_heavy_test: list mismatch after concats!\n%!";
    ok := false
  end;
  for _ = 1 to ops_after do
    if !ok then begin
      match Random.int 4 with
      | 0 ->
          let v = Random.int 10000 in
          k := Kc.kcad_push v !k;
          ref_xs := v :: !ref_xs
      | 1 ->
          let v = Random.int 10000 in
          k := Kc.kcad_inject !k v;
          ref_xs := !ref_xs @ [v]
      | 2 ->
          (match Kc.kcad_pop !k with
           | None -> ()
           | Some (x, k') ->
               k := k';
               (match !ref_xs with
                | y :: ys when y = x -> ref_xs := ys
                | y :: _ ->
                    Printf.eprintf "concat_heavy: pop got %d, expected %d\n%!"
                      x y; ok := false
                | [] ->
                    Printf.eprintf "concat_heavy: pop got %d, ref empty\n%!"
                      x; ok := false))
      | _ ->
          (match Kc.kcad_eject !k with
           | None -> ()
           | Some (k', x) ->
               k := k';
               match List.rev !ref_xs with
               | y :: rest when y = x -> ref_xs := List.rev rest
               | y :: _ ->
                   Printf.eprintf "concat_heavy: eject got %d, expected %d\n%!"
                     x y; ok := false
               | [] ->
                   Printf.eprintf "concat_heavy: eject got %d, ref empty\n%!"
                     x; ok := false);
      if !ok && Kc.kcad_to_list !k <> !ref_xs then begin
        Printf.eprintf "concat_heavy: list mismatch mid-stream\n%!";
        ok := false
      end
    end
  done;
  !ok

let () =
  let num_runs    = if Array.length Sys.argv > 1
                    then int_of_string Sys.argv.(1) else 200 in
  let ops_per_run = if Array.length Sys.argv > 2
                    then int_of_string Sys.argv.(2) else 200 in
  Printf.printf "QCheck-style: %d runs × %d ops each, checking Kc vs list ref...\n%!"
    num_runs ops_per_run;
  let failed = ref 0 in
  for i = 1 to num_runs do
    if not (run_once ~seed:i ~ops_per_run)
    then incr failed
  done;
  if !failed > 0 then begin
    Printf.printf "FAILED: %d/%d runs\n%!" !failed num_runs;
    exit 1
  end;
  Printf.printf "OK: %d/%d runs passed\n%!" num_runs num_runs;

  Printf.printf "Persistence test: forking 2 branches after 200 pushes...\n%!";
  if persistence_test ~ops_per_branch:500
  then Printf.printf "Persistence: OK\n%!"
  else begin
    Printf.printf "Persistence: FAILED\n%!"; exit 1
  end;

  Printf.printf "Concat-heavy test (%d concats × 50 elts + 500 random ops)...\n%!"
    50;
  if concat_heavy_test ~num_concats:50 ~per_chunk:50 ~ops_after:500
  then Printf.printf "Concat-heavy: OK\n%!"
  else begin
    Printf.printf "Concat-heavy: FAILED\n%!"; exit 1
  end
