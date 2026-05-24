(** k8_tt_concat_stress — (T+T) concat then drain-eject.
    Cleaner version. *)

module K = KCadeque8

let build_simple n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_push i !d done;
  !d

let build_triple n =
  let half = build_simple (n / 2) in
  K.kcad8_concat half half  (* S+S → T *)

let batch_size = 1_000

let drain_eject d0 =
  let d = ref d0 in
  let max_batch_ns = ref 0.0 in
  let total_ns = ref 0.0 in
  let total_ejects = ref 0 in
  let batches_done = ref 0 in
  let cont = ref true in
  while !cont do
    let t_start = Unix.gettimeofday () in
    let count = ref 0 in
    while !count < batch_size && !cont do
      (match K.kcad8_eject !d with
       | None -> cont := false
       | Some (d', _) -> d := d'; incr count; incr total_ejects)
    done;
    let t_end = Unix.gettimeofday () in
    if !count > 0 then begin
      let batch_ns_per_op = (t_end -. t_start) *. 1e9 /. float_of_int !count in
      total_ns := !total_ns +. (t_end -. t_start) *. 1e9;
      incr batches_done;
      if batch_ns_per_op > !max_batch_ns then
        max_batch_ns := batch_ns_per_op
    end
  done;
  (!total_ejects, !max_batch_ns, !total_ns /. float_of_int !total_ejects)

let () =
  Printf.printf "k8_tt_concat_stress: (T+T) concat then drain-eject.\n\n";
  List.iter (fun n ->
    let t1 = build_triple n in
    let t2 = build_triple n in
    let combined = K.kcad8_concat t1 t2 in
    let (ejects, max_b, avg) = drain_eject combined in
    Printf.printf "  N = %d (each half) — %d ejects, avg=%.0f, max-batch=%.0f, ratio=%.1fx\n"
      n ejects avg max_b (max_b /. avg)
  ) [1_000; 10_000]
