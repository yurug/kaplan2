(** k8_wc_stress — empirical worst-case bound check via batched
    timing.  Individual ops are ~100 ns, below [Unix.gettimeofday]
    resolution; instead we time batches of [B] ops and report the
    SLOWEST batch.

    For a WC O(1) implementation, the worst batch over N samples
    has time bounded by [B × C] where C is the per-op constant —
    independent of the deque size [n].  If any op is Θ(n), the
    worst batch will scale linearly with [n].

    Output:
      worst[b] = max-over-K-trials of (batch-time / B)   (ns/op)
      With B=1000 trials=100 and a true WC bound, [worst] is flat
      across deque sizes from [n=1K] to [n=1M].
*)

module K  = KCadeque8
module KI = KCadeque8Inline

let batch_size = 1_000
let n_batches  = 100

let measure_batch ~label ~init ~op ~n =
  ignore n;
  let d = ref init in
  let worst = ref 0.0 in
  let total_time = ref 0.0 in
  for _ = 1 to n_batches do
    let t0 = Unix.gettimeofday () in
    for _ = 1 to batch_size do d := op !d done;
    let t1 = Unix.gettimeofday () in
    let dt = t1 -. t0 in
    total_time := !total_time +. dt;
    if dt > !worst then worst := dt
  done;
  let avg_ns = !total_time *. 1e9 /. float_of_int (n_batches * batch_size) in
  let worst_ns = !worst *. 1e9 /. float_of_int batch_size in
  Printf.printf
    "  %-30s avg=%5.0f ns/op   worst-batch=%6.0f ns/op   ratio=%4.1fx\n"
    label avg_ns worst_ns (worst_ns /. avg_ns);
  ignore !d

let build_push n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_push i !d done;
  !d

let build_inject n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_inject !d i done;
  !d

let build_concat n =
  let chunk_size = 100 in
  let chunk = build_push chunk_size in
  let depth = max 1 (n / chunk_size) in
  let rec loop d k =
    if k <= 0 then d
    else loop (K.kcad8_concat d chunk) (k - 1)
  in
  loop K.kcad8_empty depth

let stress_op name op_label op build =
  Printf.printf "== %s — %s ==\n" name op_label;
  List.iter (fun n ->
    let d0 = build n in
    measure_batch
      ~label:(Printf.sprintf "n=%9d" n)
      ~init:d0
      ~op
      ~n
  ) [1_000; 10_000; 100_000; 1_000_000; 10_000_000];
  Printf.printf "\n"

let () =
  Printf.printf
    "k8_wc_stress: %d batches of %d ops each, at sizes 1K..10M.\n" n_batches batch_size;
  Printf.printf
    "If WC O(1): worst-batch ns/op is flat across deque sizes.\n";
  Printf.printf
    "If O(n) fallback exists: worst-batch scales linearly with n.\n\n";

  stress_op "push_inline" "deque built via push"
    (fun d -> KI.kcad8_push_inline (Random.bits ()) d)
    build_push;

  stress_op "pop_inline" "deque built via push"
    (fun d -> match KI.kcad8_pop_inline d with
              | K.PopFail8 -> d
              | K.PopOk8 (_, d') -> d')
    (fun n -> build_push (max n (batch_size * n_batches * 2)));

  stress_op "inject_inline" "deque built via inject"
    (fun d -> KI.kcad8_inject_inline d (Random.bits ()))
    build_inject;

  stress_op "eject_inline" "deque built via inject"
    (fun d -> match KI.kcad8_eject_inline d with
              | K.EjectFail8 -> d
              | K.EjectOk8 (d', _) -> d')
    (fun n -> build_inject (max n (batch_size * n_batches * 2)));

  stress_op "push_inline" "deque built via repeated concat (K8Triple)"
    (fun d -> KI.kcad8_push_inline (Random.bits ()) d)
    build_concat;

  stress_op "pop_inline" "deque built via repeated concat (K8Triple)"
    (fun d -> match KI.kcad8_pop_inline d with
              | K.PopFail8 -> d
              | K.PopOk8 (_, d') -> d')
    (fun n -> build_concat (max n (batch_size * n_batches * 2)))
