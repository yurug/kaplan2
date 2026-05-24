(** k9_qcheck — property-based test for Cadeque9.

    Sanity-checks the extracted Cadeque9 against a list reference
    across push / inject / pop / eject / concat. *)

module K = KCadeque9

type op =
  | Push    of int
  | Inject  of int
  | Pop
  | Eject
  | ConcatSelf
  | ConcatRight of int * int
  | ConcatLeft  of int * int
  | ConcatTwo   of int list

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
      ConcatTwo (List.init len (fun _ -> Random.int 100))

let apply_ref xs = function
  | Push x         -> x :: xs
  | Inject x       -> xs @ [x]
  | Pop            -> (match xs with [] -> [] | _ :: t -> t)
  | Eject          -> (match List.rev xs with [] -> [] | _ :: t -> List.rev t)
  | ConcatSelf     -> xs @ xs
  | ConcatRight (a, b) -> xs @ [a; b]
  | ConcatLeft  (a, b) -> [a; b] @ xs
  | ConcatTwo ys   -> xs @ ys

let mk_small xs = List.fold_left K.kcad9_inject K.kcad9_empty xs

let apply_k9 d = function
  | Push x         -> K.kcad9_push x d
  | Inject x       -> K.kcad9_inject d x
  | Pop            -> (match K.kcad9_pop d with None -> d | Some (_, d') -> d')
  | Eject          -> (match K.kcad9_eject d with None -> d | Some (d', _) -> d')
  | ConcatSelf     -> K.kcad9_concat d d
  | ConcatRight (a, b) -> K.kcad9_concat d (mk_small [a; b])
  | ConcatLeft  (a, b) -> K.kcad9_concat (mk_small [a; b]) d
  | ConcatTwo ys   -> K.kcad9_concat d (mk_small ys)

let run_once ~seed ~ops_per_run ~check_every =
  Random.init seed;
  let d = ref K.kcad9_empty in
  let xs = ref [] in
  let ok = ref true in
  for step = 1 to ops_per_run do
    if !ok then begin
      let op = sample_op (List.length !xs) in
      d := apply_k9 !d op;
      xs := apply_ref !xs op;
      if step mod check_every = 0 || step = ops_per_run then begin
        let got = K.kcad9_to_list !d in
        if got <> !xs then begin
          Printf.eprintf "MISMATCH seed=%d step=%d\n  got = [%s]\n  ref = [%s]\n"
            seed step
            (String.concat ";" (List.map string_of_int got))
            (String.concat ";" (List.map string_of_int !xs));
          ok := false
        end
      end
    end
  done;
  !ok

let () =
  let num_runs    = if Array.length Sys.argv > 1
                    then int_of_string Sys.argv.(1) else 200 in
  let ops_per_run = if Array.length Sys.argv > 2
                    then int_of_string Sys.argv.(2) else 200 in
  let check_every = if Array.length Sys.argv > 3
                    then int_of_string Sys.argv.(3) else 20 in
  Printf.printf "Cadeque9 QCheck: %d runs × %d ops (check every %d)...\n%!"
    num_runs ops_per_run check_every;
  let failed = ref 0 in
  for i = 1 to num_runs do
    if not (run_once ~seed:i ~ops_per_run ~check_every) then incr failed
  done;
  if !failed > 0 then begin
    Printf.printf "FAILED: %d/%d\n" !failed num_runs; exit 1
  end else
    Printf.printf "OK: %d/%d runs (%d ops total)\n"
      num_runs num_runs (num_runs * ops_per_run)
