(** k8_concat_pop_stress — targeted test for the WC O(1) gap I
    suspect in [K8Simple `concat` K8Triple] followed by drain-pop.

    Sequence:
      1. Build [k8s] = K8Simple with N elements (via push).
      2. Build [k8t] = K8Triple with N elements (via concat-self).
      3. Compute [r = k8s `concat` k8t].  Per the Rocq concat
         definition, this creates a [StoredBig8] in m whose sub is
         [K8Triple ø m2 ø] — empty left boundary.
      4. Pop [r] until h drains.  The pop that triggers rebalance
         will hit [stored_sub_left_safe = false] and fall back to
         [kcad8_to_list ; kcad8_from_list] — a Θ(2N) operation.

    If WC O(1) holds, max per-pop time is bounded by a constant
    across N values.  If the fallback fires, max time scales with N.

    Reports max-batch and median-batch ns/op.  If max grows with N
    while median doesn't, we've found the gap. *)

module K = KCadeque8

let build_simple n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_push i !d done;
  !d

let build_triple n =
  (* Build something via concat to get a K8Triple structure *)
  let half = build_simple (n / 2) in
  K.kcad8_concat half half  (* this becomes K8Triple if both are non-empty K8Simple *)

let batch_size = 1_000

let drain_with_stats label d0 =
  let d = ref d0 in
  let max_batch = ref 0.0 in
  let total_time = ref 0.0 in
  let batch_count = ref 0 in
  let pop_count = ref 0 in
  let continue = ref true in
  while !continue do
    let t0 = Unix.gettimeofday () in
    let cnt = ref 0 in
    while !cnt < batch_size && !continue do
      match K.kcad8_pop !d with
      | None -> continue := false
      | Some (_, d') ->
          d := d';
          incr cnt;
          incr pop_count
    done;
    let t1 = Unix.gettimeofday () in
    if !cnt > 0 then begin
      let batch_t = (t1 -. t0) *. 1e9 /. float_of_int !cnt in
      total_time := !total_time +. (t1 -. t0);
      incr batch_count;
      if batch_t > !max_batch then max_batch := batch_t
    end
  done;
  let avg = !total_time *. 1e9 /. float_of_int !pop_count in
  Printf.printf "  %-32s avg=%6.0f  max-batch=%9.0f ns/op  ratio=%6.1fx  (popped %d)\n"
    label avg !max_batch (!max_batch /. avg) !pop_count

let () =
  Printf.printf "k8_concat_pop_stress: testing K8Simple `concat` K8Triple drain.\n";
  Printf.printf "If WC O(1): max-batch is flat across N.\n";
  Printf.printf "If O(n) fallback fires: max-batch scales with N.\n\n";
  List.iter (fun n ->
    Printf.printf "== N = %d (each half) ==\n" n;
    let k8s = build_simple n in
    let k8t = build_triple n in
    let combined = K.kcad8_concat k8s k8t in
    drain_with_stats (Printf.sprintf "K8Simple |+| K8Triple") combined
  ) [1_000; 10_000; 100_000; 1_000_000]
