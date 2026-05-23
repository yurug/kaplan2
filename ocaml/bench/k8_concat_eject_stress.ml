(** k8_concat_eject_stress — eject-side analog of
    [k8_concat_pop_stress].  Checks whether [K8Triple h1 m1 t1
    `concat` K8Simple bb] (the symmetric (T+S) case) violates WC
    O(1) on a drain-eject workload.

    Hypothesis: the (T+S) concat injects [StoredSmall8 t1] at the
    right end of [m].  [stored_sub_right_safe (StoredSmall8 _) =
    false] always, so [rebalance_after_t_empty] returns [None], and
    [kcad8_eject_fast] falls back to [kcad8_to_list ;
    kcad8_from_list] — Θ(n). *)

module K = KCadeque8

let build_simple n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_push i !d done;
  !d

let build_triple n =
  let half = build_simple (n / 2) in
  K.kcad8_concat half half

let batch_size = 1_000

let drain_with_stats label d0 =
  let d = ref d0 in
  let max_batch = ref 0.0 in
  let total_time = ref 0.0 in
  let pop_count = ref 0 in
  let continue = ref true in
  while !continue do
    let t0 = Unix.gettimeofday () in
    let cnt = ref 0 in
    while !cnt < batch_size && !continue do
      match K.kcad8_eject !d with
      | None -> continue := false
      | Some (d', _) ->
          d := d';
          incr cnt;
          incr pop_count
    done;
    let t1 = Unix.gettimeofday () in
    if !cnt > 0 then begin
      let batch_t = (t1 -. t0) *. 1e9 /. float_of_int !cnt in
      total_time := !total_time +. (t1 -. t0);
      if batch_t > !max_batch then max_batch := batch_t
    end
  done;
  let avg = !total_time *. 1e9 /. float_of_int !pop_count in
  Printf.printf "  %-32s avg=%6.0f  max-batch=%9.0f ns/op  ratio=%6.1fx  (ejected %d)\n"
    label avg !max_batch (!max_batch /. avg) !pop_count

let () =
  Printf.printf "k8_concat_eject_stress: K8Triple |+| K8Simple then drain-eject.\n\n";
  List.iter (fun n ->
    Printf.printf "== N = %d (each half) ==\n" n;
    let k8t = build_triple n in
    let k8s = build_simple n in
    let combined = K.kcad8_concat k8t k8s in
    drain_with_stats "K8Triple |+| K8Simple" combined
  ) [1_000; 10_000; 100_000; 1_000_000]
