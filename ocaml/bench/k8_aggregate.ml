(** k8_aggregate — mixed-workload throughput benchmark.

    The headline numbers in [k8_alloc] measure single ops in
    isolation.  This bench measures realistic mixed workloads where
    multiple op types interleave, which is what users actually run.

    Workload mix [pop+push, pop+inject, FIFO+drain, LIFO+drain,
    push+eject].  Each runs 1M ops and reports total ns and ns/op.
*)

module K  = KCadeque8
module KI = KCadeque8Inline
module Vi = Viennot_cadeque.Cadeque.Base

let n = 1_000_000

let time_total label f =
  let t0 = Unix.gettimeofday () in
  let () = f () in
  let t1 = Unix.gettimeofday () in
  let ns_per_op = (t1 -. t0) *. 1e9 /. float_of_int n in
  Printf.printf "  %-44s %7.1f ns/op (%4.0f ms total)\n"
    label ns_per_op ((t1 -. t0) *. 1000.0)

(* Workload 1: round-trip — push 1 then pop 1 repeatedly. *)
let wl_roundtrip_k8i () =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do
    d := KI.kcad8_push_inline i !d;
    match KI.kcad8_pop_inline !d with
    | K.PopFail8 -> ()
    | K.PopOk8 (_, d') -> d := d'
  done

let wl_roundtrip_vi () =
  let d = ref Vi.empty in
  for i = 0 to n - 1 do
    d := Vi.push i !d;
    match Vi.pop !d with
    | None -> ()
    | Some (_, d') -> d := d'
  done

(* Workload 2: FIFO — inject n then pop n. *)
let wl_fifo_k8i () =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := KI.kcad8_inject_inline !d i done;
  for _ = 0 to n - 1 do
    match KI.kcad8_pop_inline !d with
    | K.PopFail8 -> ()
    | K.PopOk8 (_, d') -> d := d'
  done

let wl_fifo_vi () =
  let d = ref Vi.empty in
  for i = 0 to n - 1 do d := Vi.inject !d i done;
  for _ = 0 to n - 1 do
    match Vi.pop !d with
    | None -> ()
    | Some (_, d') -> d := d'
  done

(* Workload 3: LIFO — push n then pop n. *)
let wl_lifo_k8i () =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := KI.kcad8_push_inline i !d done;
  for _ = 0 to n - 1 do
    match KI.kcad8_pop_inline !d with
    | K.PopFail8 -> ()
    | K.PopOk8 (_, d') -> d := d'
  done

let wl_lifo_vi () =
  let d = ref Vi.empty in
  for i = 0 to n - 1 do d := Vi.push i !d done;
  for _ = 0 to n - 1 do
    match Vi.pop !d with
    | None -> ()
    | Some (_, d') -> d := d'
  done

(* Workload 4: double-ended — push and inject interleaved, then drain
   from both ends.  This exercises all 4 dequeue operations. *)
let wl_double_k8i () =
  let d = ref K.kcad8_empty in
  for i = 0 to (n / 2) - 1 do
    d := KI.kcad8_push_inline i !d;
    d := KI.kcad8_inject_inline !d i
  done;
  for _ = 0 to (n / 2) - 1 do
    (match KI.kcad8_pop_inline !d with
     | K.PopFail8 -> ()
     | K.PopOk8 (_, d') -> d := d');
    (match KI.kcad8_eject_inline !d with
     | K.EjectFail8 -> ()
     | K.EjectOk8 (d', _) -> d := d')
  done

let wl_double_vi () =
  let d = ref Vi.empty in
  for i = 0 to (n / 2) - 1 do
    d := Vi.push i !d;
    d := Vi.inject !d i
  done;
  for _ = 0 to (n / 2) - 1 do
    (match Vi.pop !d with
     | None -> ()
     | Some (_, d') -> d := d');
    (match Vi.eject !d with
     | None -> ()
     | Some (d', _) -> d := d')
  done

let () =
  Printf.printf "==== Cadeque8_inline vs Viennot, mixed workloads (n = %d) ====\n\n" n;
  Printf.printf "Workload: round-trip (push 1, pop 1) x n\n";
  time_total "Cadeque8_inline" wl_roundtrip_k8i;
  time_total "Viennot" wl_roundtrip_vi;
  Printf.printf "\nWorkload: FIFO (inject n, pop n)\n";
  time_total "Cadeque8_inline" wl_fifo_k8i;
  time_total "Viennot" wl_fifo_vi;
  Printf.printf "\nWorkload: LIFO (push n, pop n)\n";
  time_total "Cadeque8_inline" wl_lifo_k8i;
  time_total "Viennot" wl_lifo_vi;
  Printf.printf "\nWorkload: double-ended (push+inject n/2 each, then pop+eject n/2 each)\n";
  time_total "Cadeque8_inline" wl_double_k8i;
  time_total "Viennot" wl_double_vi
