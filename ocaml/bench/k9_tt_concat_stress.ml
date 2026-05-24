(** k9_tt_concat_stress — Cadeque9 (T+T) concat then drain-eject.

    Mirrors [k8_tt_concat_stress.ml] but uses [KCadeque9].  This is
    the bench that demonstrates the structural fix: under Cadeque8
    this workload was Θ(n) per eject (avg 194 µs/op at N=10K);
    under Cadeque9 it should be flat across N. *)

module K = KCadeque9
module KI = KCadeque9Inline

let build_simple n =
  let d = ref K.kcad9_empty in
  for i = 0 to n - 1 do d := K.kcad9_push i !d done;
  !d

let build_triple n =
  let half = build_simple (n / 2) in
  K.kcad9_concat half half  (* S+S → T *)

let batch_size = 1_000

let drain_eject d0 =
  let d = ref d0 in
  let max_batch_ns = ref 0.0 in
  let total_ns = ref 0.0 in
  let total_ejects = ref 0 in
  let cont = ref true in
  while !cont do
    let t_start = Unix.gettimeofday () in
    let count = ref 0 in
    while !count < batch_size && !cont do
      (match K.kcad9_eject !d with
       | None -> cont := false
       | Some (d', _) -> d := d'; incr count; incr total_ejects)
    done;
    let t_end = Unix.gettimeofday () in
    if !count > 0 then begin
      let batch_ns_per_op = (t_end -. t_start) *. 1e9 /. float_of_int !count in
      total_ns := !total_ns +. (t_end -. t_start) *. 1e9;
      if batch_ns_per_op > !max_batch_ns then
        max_batch_ns := batch_ns_per_op
    end
  done;
  (!total_ejects, !max_batch_ns, !total_ns /. float_of_int !total_ejects)

let drain_eject_inline d0 =
  let d = ref d0 in
  let max_batch_ns = ref 0.0 in
  let total_ns = ref 0.0 in
  let total_ejects = ref 0 in
  let cont = ref true in
  while !cont do
    let t_start = Unix.gettimeofday () in
    let count = ref 0 in
    while !count < batch_size && !cont do
      (match KI.kcad9_eject_inline !d with
       | K.EjectFail9 -> cont := false
       | K.EjectOk9 (d', _) -> d := d'; incr count; incr total_ejects)
    done;
    let t_end = Unix.gettimeofday () in
    if !count > 0 then begin
      let batch_ns_per_op = (t_end -. t_start) *. 1e9 /. float_of_int !count in
      total_ns := !total_ns +. (t_end -. t_start) *. 1e9;
      if batch_ns_per_op > !max_batch_ns then
        max_batch_ns := batch_ns_per_op
    end
  done;
  (!total_ejects, !max_batch_ns, !total_ns /. float_of_int !total_ejects)

let () =
  Printf.printf "k9_tt_concat_stress: Cadeque9 (T+T) concat then drain-eject.\n";
  Printf.printf "If WC O(1): max-batch flat across N.\n\n";
  List.iter (fun n ->
    let t1 = build_triple n in
    let t2 = build_triple n in
    let combined = K.kcad9_concat t1 t2 in
    let combined2 = K.kcad9_concat t1 t2 in
    let (ejects, max_b, avg) = drain_eject combined in
    Printf.printf "  N=%d   default: %d ejects avg=%.0f max=%.0f ratio=%.1fx\n"
      n ejects avg max_b (max_b /. avg);
    let (ejects_i, max_bi, avg_i) = drain_eject_inline combined2 in
    Printf.printf "  N=%d   inline:  %d ejects avg=%.0f max=%.0f ratio=%.1fx\n"
      n ejects_i avg_i max_bi (max_bi /. avg_i)
  ) [1_000; 10_000; 100_000; 1_000_000]
