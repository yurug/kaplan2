(** k9_wc_stress — Cadeque9 batched WC O(1) check, mirroring
    [k8_wc_stress.ml].  Tests push / pop / inject / eject across
    deque sizes 1K..10M built by push and by repeated concat. *)

module K = KCadeque9

let batch_size = 1_000
let n_batches  = 100

let measure_batch ~label ~init ~op =
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
  let d = ref K.kcad9_empty in
  for i = 0 to n - 1 do d := K.kcad9_push i !d done;
  !d

let build_inject n =
  let d = ref K.kcad9_empty in
  for i = 0 to n - 1 do d := K.kcad9_inject !d i done;
  !d

let build_concat n =
  let chunk_size = 100 in
  let chunk = build_push chunk_size in
  let depth = max 1 (n / chunk_size) in
  let rec loop d k = if k <= 0 then d else loop (K.kcad9_concat d chunk) (k - 1) in
  loop K.kcad9_empty depth

let stress_op name op_label op build =
  Printf.printf "== %s — %s ==\n" name op_label;
  List.iter (fun n ->
    let d0 = build n in
    measure_batch
      ~label:(Printf.sprintf "n=%9d" n)
      ~init:d0
      ~op
  ) [1_000; 10_000; 100_000; 1_000_000];
  Printf.printf "\n"

let () =
  Printf.printf
    "k9_wc_stress: %d batches of %d ops each, at sizes 1K..10M.\n" n_batches batch_size;
  Printf.printf
    "If WC O(1): worst-batch ns/op is flat across deque sizes.\n\n";

  stress_op "push" "deque built via push"
    (fun d -> K.kcad9_push (Random.bits ()) d)
    build_push;

  stress_op "pop" "deque built via push"
    (fun d -> match K.kcad9_pop d with
              | None -> d
              | Some (_, d') -> d')
    (fun n -> build_push (max n (batch_size * n_batches * 2)));

  stress_op "inject" "deque built via inject"
    (fun d -> K.kcad9_inject d (Random.bits ()))
    build_inject;

  stress_op "eject" "deque built via inject"
    (fun d -> match K.kcad9_eject d with
              | None -> d
              | Some (d', _) -> d')
    (fun n -> build_inject (max n (batch_size * n_batches * 2)));

  (* Concat-built tests omitted from this default run: buf6_concat
     at the spec level is O(|a|+|b|), making setup slow.  The
     [k9_tt_concat_stress.ml] focused bench exercises the (T+T)
     concat+eject pattern at scale. *)
  Printf.printf
    "(Concat-build tests omitted — see k9_tt_concat_stress for that pattern.)\n"
