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

let time_concat reps t1 t2 =
  Gc.compact ();
  let start = Unix.gettimeofday () in
  for _ = 1 to reps do
    ignore (Sys.opaque_identity (K.kcad9_concat t1 t2))
  done;
  let stop = Unix.gettimeofday () in
  ((stop -. start) *. 1e9) /. float_of_int reps

let reps_for n =
  max 3 (min 200 (1_000_000 / max 1 n))

let () =
  Printf.printf "k9_concat_cost: timing KCadeque9.kcad9_concat itself.\n";
  Printf.printf "A strict WC O(1) concat should not scale with N.\n\n";
  List.iter (fun n ->
    let t1 = build_triple n in
    let t2 = build_triple n in
    let reps = reps_for n in
    let avg = time_concat reps t1 t2 in
    Printf.printf "  N=%-8d reps=%-4d concat avg=%.0f ns\n%!"
      n reps avg
  ) [1_000; 10_000; 100_000; 1_000_000]
