(** Property-based equivalence: Cadeque8 (the strict-WC O(1) §6
    catenable cadeque) vs a list reference.

    Cadeque8 differs from Cadeque7: a [K8Triple] has a head buffer,
    a middle deque of stored cells, and a tail buffer.  Concat wraps
    the boundary as one stored cell — never falls back.  Pop drains
    the head; when empty, unfolds the leftmost stored cell.  Per-call
    cost is WC O(1) by construction (every op does at most a constant
    number of [buf6_*] ops, each itself WC O(1) via the Phase 5d
    [KCadequeShim] / certified kt2 family). *)

module K = KCadeque8

type op =
  | Push of int
  | Inject of int
  | Pop
  | Eject
  | ConcatSelf
  | ConcatRight

let op_to_string = function
  | Push x -> Printf.sprintf "push %d" x
  | Inject x -> Printf.sprintf "inject %d" x
  | Pop -> "pop"
  | Eject -> "eject"
  | ConcatSelf -> "concat-self"
  | ConcatRight -> "concat-right"

let sample_op cur_size =
  match Random.int 10 with
  | 0 | 1 | 2 -> Push (Random.int 1000)
  | 3 | 4 | 5 -> Inject (Random.int 1000)
  | 6         -> Pop
  | 7         -> Eject
  | 8         -> if cur_size < 4_000 then ConcatSelf else Pop
  | _         -> ConcatRight

let apply_op_ref xs = function
  | Push x      -> x :: xs
  | Inject x    -> xs @ [x]
  | Pop         -> (match xs with [] -> [] | _ :: t -> t)
  | Eject       ->
      (match List.rev xs with [] -> [] | _ :: t -> List.rev t)
  | ConcatSelf  -> xs @ xs
  | ConcatRight ->
      let a = Random.int 100 in
      let b = Random.int 100 in
      xs @ [a; b]

let apply_op_k k = function
  | Push x     -> K.kcad8_push x k
  | Inject x   -> K.kcad8_inject k x
  | Pop        ->
      (match K.kcad8_pop k with None -> k | Some (_, k') -> k')
  | Eject      ->
      (match K.kcad8_eject k with None -> k | Some (k', _) -> k')
  | ConcatSelf -> K.kcad8_concat k k
  | ConcatRight ->
      let a = Random.int 100 in
      let b = Random.int 100 in
      let small = K.kcad8_push a (K.kcad8_push b K.kcad8_empty) in
      K.kcad8_concat k small

let check_eq k xs =
  let got = K.kcad8_to_list k in
  if got <> xs then begin
    Printf.eprintf "MISMATCH: K=%s ref=%s\n%!"
      (String.concat ";" (List.map string_of_int got))
      (String.concat ";" (List.map string_of_int xs));
    false
  end else true

let run_once ~seed ~ops_per_run =
  Random.init seed;
  let k = ref K.kcad8_empty in
  let xs = ref [] in
  let trace = ref [] in
  let ok = ref true in
  for _ = 1 to ops_per_run do
    if !ok then begin
      let op = sample_op (List.length !xs) in
      trace := op :: !trace;
      (match op with
       | ConcatRight ->
           let a = Random.int 100 in
           let b = Random.int 100 in
           let small = K.kcad8_push a (K.kcad8_push b K.kcad8_empty) in
           k := K.kcad8_concat !k small;
           xs := !xs @ [a; b]
       | _ ->
           k := apply_op_k !k op;
           xs := apply_op_ref !xs op);
      if not (check_eq !k !xs) then begin
        Printf.eprintf "FAIL seed=%d trace: %s\n%!" seed
          (String.concat " ; "
             (List.map op_to_string (List.rev !trace)));
        ok := false
      end
    end
  done;
  !ok

let () =
  let num_runs    = if Array.length Sys.argv > 1
                    then int_of_string Sys.argv.(1) else 50 in
  let ops_per_run = if Array.length Sys.argv > 2
                    then int_of_string Sys.argv.(2) else 100 in
  Printf.printf "Cadeque8 QCheck: %d runs × %d ops each...\n%!"
    num_runs ops_per_run;
  let failed = ref 0 in
  for i = 1 to num_runs do
    if not (run_once ~seed:i ~ops_per_run)
    then incr failed
  done;
  if !failed > 0 then begin
    Printf.printf "FAILED: %d/%d runs\n%!" !failed num_runs;
    exit 1
  end else
    Printf.printf "OK: %d/%d runs passed\n%!" num_runs num_runs
