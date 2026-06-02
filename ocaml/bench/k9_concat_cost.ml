(** k9_concat_cost -- time the KCadeque9 concat operation itself.

    k9_tt_concat_stress times drain-eject after a T+T concat.  That is useful,
    but it does not measure the concat call.  This bench times only
    [kcad9_concat t1 t2] on prebuilt triple inputs, exposing the current
    [buf6_concat] blocker directly. *)

module K = KCadeque9

let build_push n =
  let d = ref K.kcad9_empty in
  for i = 0 to n - 1 do
    d := K.kcad9_push i !d
  done;
  !d

let build_triple n =
  let half = build_push (max 1 (n / 2)) in
  K.kcad9_concat half half

let time_concat_once reps t1 t2 =
  Gc.compact ();
  let start = Unix.gettimeofday () in
  for _ = 1 to reps do
    ignore (Sys.opaque_identity (K.kcad9_concat t1 t2))
  done;
  let stop = Unix.gettimeofday () in
  (stop -. start, ((stop -. start) *. 1e9) /. float_of_int reps)

let time_concat t1 t2 =
  let min_seconds = 0.02 in
  let max_reps = 100_000 in
  let rec loop reps =
    let elapsed, avg = time_concat_once reps t1 t2 in
    if elapsed < min_seconds && reps < max_reps then
      loop (min max_reps (reps * 4))
    else
      (reps, avg)
  in
  loop 16

let fail_if_obvious_regression samples =
  match samples with
  | [] | [_] -> ()
  | (_, _, first_avg) :: rest ->
      let baseline = max 100.0 first_avg in
      let limit = max 20_000.0 (baseline *. 200.0) in
      List.iter (fun (n, _, avg) ->
        if avg > limit then begin
          Printf.eprintf
            "k9_concat_cost: concat avg at N=%d was %.0f ns, above %.0f ns regression limit\n%!"
            n avg limit;
          exit 1
        end
      ) rest

let () =
  Printf.printf "k9_concat_cost: timing KCadeque9.kcad9_concat itself.\n";
  Printf.printf "A strict WC O(1) concat should not scale with N.\n\n";
  let samples =
    List.map (fun n ->
      let t1 = build_triple n in
      let t2 = build_triple n in
      let reps, avg = time_concat t1 t2 in
      Printf.printf "  N=%-8d reps=%-6d concat avg=%.0f ns\n%!"
        n reps avg;
      (n, reps, avg)
    ) [1_000; 10_000; 100_000; 1_000_000]
  in
  fail_if_obvious_regression samples
