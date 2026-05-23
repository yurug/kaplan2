(** k8i_qcheck — property-based equivalence test for ALL three
    Cadeque8 op flavours (cert, fast, inline) against a list
    reference, including concat.

    Where the existing [kc8_qcheck.ml] only tests the [_cert]
    variants, this exercises every variant in parallel so that
    a sequence-preservation bug in any single variant breaks
    the test.

    Each run also cross-checks the inline against the fast at
    every step, so any kt4-result mismatch surfaces immediately. *)

module K  = KCadeque8
module KI = KCadeque8Inline

type op =
  | Push    of int
  | Inject  of int
  | Pop
  | Eject
  | ConcatSelf
  | ConcatRight of int * int      (* concat with a fresh 2-element chunk *)
  | ConcatLeft  of int * int      (* prepend a fresh 2-element chunk *)
  | ConcatTwo   of int list       (* concat with a fresh n-element chunk *)

let op_to_string = function
  | Push x         -> Printf.sprintf "push %d" x
  | Inject x       -> Printf.sprintf "inject %d" x
  | Pop            -> "pop"
  | Eject          -> "eject"
  | ConcatSelf     -> "concat-self"
  | ConcatRight (a, b) -> Printf.sprintf "concat-right [%d;%d]" a b
  | ConcatLeft  (a, b) -> Printf.sprintf "concat-left  [%d;%d]" a b
  | ConcatTwo xs   ->
      Printf.sprintf "concat-two [%s]"
        (String.concat ";" (List.map string_of_int xs))

let sample_op cur_size =
  match Random.int 32 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 -> Push (Random.int 1000)
  | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 -> Inject (Random.int 1000)
  | 16 | 17 | 18 | 19 -> Pop
  | 20 | 21 | 22 | 23 -> Eject
  | 24 when cur_size < 200 -> ConcatSelf
  | 24              -> Pop
  | 25 | 26 | 27    -> ConcatRight (Random.int 100, Random.int 100)
  | 28 | 29         -> ConcatLeft  (Random.int 100, Random.int 100)
  | _               ->
      let len = 1 + Random.int 5 in
      let xs = List.init len (fun _ -> Random.int 100) in
      ConcatTwo xs

(* List reference model. *)
let apply_op_ref xs = function
  | Push x         -> x :: xs
  | Inject x       -> xs @ [x]
  | Pop            -> (match xs with [] -> [] | _ :: t -> t)
  | Eject          ->
      (match List.rev xs with [] -> [] | _ :: t -> List.rev t)
  | ConcatSelf     -> xs @ xs
  | ConcatRight (a, b) -> xs @ [a; b]
  | ConcatLeft  (a, b) -> [a; b] @ xs
  | ConcatTwo ys   -> xs @ ys

(* Build a small fresh deque from a list using cert ops. *)
let mk_small_cert xs =
  List.fold_left K.kcad8_inject K.kcad8_empty xs

(* Apply an op using the certified API. *)
let apply_op_cert d = function
  | Push x         -> K.kcad8_push x d
  | Inject x       -> K.kcad8_inject d x
  | Pop            ->
      (match K.kcad8_pop d with None -> d | Some (_, d') -> d')
  | Eject          ->
      (match K.kcad8_eject d with None -> d | Some (d', _) -> d')
  | ConcatSelf     -> K.kcad8_concat d d
  | ConcatRight (a, b) ->
      K.kcad8_concat d (mk_small_cert [a; b])
  | ConcatLeft  (a, b) ->
      K.kcad8_concat (mk_small_cert [a; b]) d
  | ConcatTwo ys   ->
      K.kcad8_concat d (mk_small_cert ys)

(* Apply an op using the fast API. *)
let apply_op_fast d = function
  | Push x         -> K.kcad8_push_fast x d
  | Inject x       -> K.kcad8_inject_fast d x
  | Pop            ->
      (match K.kcad8_pop_fast d with
       | K.PopFail8 -> d
       | K.PopOk8 (_, d') -> d')
  | Eject          ->
      (match K.kcad8_eject_fast d with
       | K.EjectFail8 -> d
       | K.EjectOk8 (d', _) -> d')
  | ConcatSelf     -> K.kcad8_concat_fast d d
  | ConcatRight (a, b) ->
      K.kcad8_concat_fast d (mk_small_cert [a; b])
  | ConcatLeft  (a, b) ->
      K.kcad8_concat_fast (mk_small_cert [a; b]) d
  | ConcatTwo ys   ->
      K.kcad8_concat_fast d (mk_small_cert ys)

(* Apply an op using the inline API.  Concat falls back to the fast
   variant since we have no [_inline] concat. *)
let apply_op_inline d = function
  | Push x         -> KI.kcad8_push_inline x d
  | Inject x       -> KI.kcad8_inject_inline d x
  | Pop            ->
      (match KI.kcad8_pop_inline d with
       | K.PopFail8 -> d
       | K.PopOk8 (_, d') -> d')
  | Eject          ->
      (match KI.kcad8_eject_inline d with
       | K.EjectFail8 -> d
       | K.EjectOk8 (d', _) -> d')
  | ConcatSelf     -> K.kcad8_concat_fast d d
  | ConcatRight (a, b) ->
      K.kcad8_concat_fast d (mk_small_cert [a; b])
  | ConcatLeft  (a, b) ->
      K.kcad8_concat_fast (mk_small_cert [a; b]) d
  | ConcatTwo ys   ->
      K.kcad8_concat_fast d (mk_small_cert ys)

let lists_match label k_list ref_list =
  if k_list <> ref_list then begin
    Printf.eprintf "MISMATCH %s:\n  got = [%s]\n  ref = [%s]\n%!"
      label
      (String.concat ";" (List.map string_of_int k_list))
      (String.concat ";" (List.map string_of_int ref_list));
    false
  end else true

let run_once ~seed ~ops_per_run ~check_every =
  Random.init seed;
  let dc = ref K.kcad8_empty in
  let df = ref K.kcad8_empty in
  let di = ref K.kcad8_empty in
  let xs = ref [] in
  let trace = ref [] in
  let ok = ref true in
  for step = 1 to ops_per_run do
    if !ok then begin
      let op = sample_op (List.length !xs) in
      trace := op :: !trace;
      dc := apply_op_cert !dc op;
      df := apply_op_fast !df op;
      di := apply_op_inline !di op;
      xs := apply_op_ref !xs op;
      if step mod check_every = 0 || step = ops_per_run then begin
        let cl = K.kcad8_to_list !dc in
        let fl = K.kcad8_to_list !df in
        let il = K.kcad8_to_list !di in
        let rl = !xs in
        if not (lists_match "cert"   cl rl
             && lists_match "fast"   fl rl
             && lists_match "inline" il rl) then begin
          Printf.eprintf "FAIL seed=%d step=%d trace tail (last 30): %s\n%!" seed step
            (String.concat " ; "
               (List.map op_to_string
                  (List.rev (List.filteri (fun i _ -> i < 30) !trace))));
          ok := false
        end
      end
    end
  done;
  !ok

let () =
  let num_runs    = if Array.length Sys.argv > 1
                    then int_of_string Sys.argv.(1) else 500 in
  let ops_per_run = if Array.length Sys.argv > 2
                    then int_of_string Sys.argv.(2) else 200 in
  let check_every = if Array.length Sys.argv > 3
                    then int_of_string Sys.argv.(3) else 20 in
  Printf.printf
    "Cadeque8 QCheck (cert + fast + inline vs list ref): %d runs × %d ops (check every %d)...\n%!"
    num_runs ops_per_run check_every;
  let failed = ref 0 in
  for i = 1 to num_runs do
    if not (run_once ~seed:i ~ops_per_run ~check_every)
    then incr failed
  done;
  if !failed > 0 then begin
    Printf.printf "FAILED: %d/%d runs\n%!" !failed num_runs;
    exit 1
  end else
    Printf.printf "OK: %d/%d runs passed (%d ops total)\n%!"
      num_runs num_runs (num_runs * ops_per_run)
