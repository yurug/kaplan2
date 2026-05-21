(** kc8_csv.ml — Cadeque8 vs Cadeque8_fast vs Viennot catenable,
    CSV output for plotting.

    Emits a single CSV to stdout with columns:
      n, op, impl, ns_per_op

    For each N in argv, runs each op against THREE implementations:
      Cadeque8       — the certified version (Cadeque8/Ops.v)
      Cadeque8_fast  — the kt4-style optimised version (Cadeque8/OpsFast.v)
      Viennot        — Viennot's hand-coded reference

    Plus an adversarial workload at the end:
      pop_all after `depth` concats of 100-element chunks.
*)

module K  = KCadeque8
module Vi = Viennot_cadeque.Cadeque.Base

let emit n op impl ns_per_op =
  Printf.printf "%d,%s,%s,%.3f\n" n op impl ns_per_op

let time_ns_per_op n f =
  let t0 = Unix.gettimeofday () in
  let r  = f () in
  let t1 = Unix.gettimeofday () in
  let ns = (t1 -. t0) *. 1e9 /. float_of_int n in
  (ns, r)

(* --- K8 op closures (certified) --- *)
let k8_push_n n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_push i !acc done;
  !acc

let k8_inject_n n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_inject !acc i done;
  !acc

let k8_pop_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match K.kcad8_pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'
  done

let k8_eject_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match K.kcad8_eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'
  done

(* --- K8 op closures (fast, kt4-style flat sum types) --- *)
let k8f_push_n n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_push_fast i !acc done;
  !acc

let k8f_inject_n n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_inject_fast !acc i done;
  !acc

let k8f_pop_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match K.kcad8_pop_fast !acc with
    | K.PopFail8 -> cont := false
    | K.PopOk8 (_, d') -> acc := d'
  done

let k8f_eject_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match K.kcad8_eject_fast !acc with
    | K.EjectFail8 -> cont := false
    | K.EjectOk8 (d', _) -> acc := d'
  done

(* --- Viennot op closures --- *)
let vi_push_n n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.push i !acc done;
  !acc

let vi_inject_n n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.inject !acc i done;
  !acc

let vi_pop_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match Vi.pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'
  done

let vi_eject_all d =
  let acc = ref d in
  let cont = ref true in
  while !cont do
    match Vi.eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'
  done

let run n =
  (* push *)
  let (ns, dk) = time_ns_per_op n (fun () -> k8_push_n n) in
  emit n "push" "Cadeque8" ns;
  let (ns, dkf) = time_ns_per_op n (fun () -> k8f_push_n n) in
  emit n "push" "Cadeque8_fast" ns;
  let (ns, dv) = time_ns_per_op n (fun () -> vi_push_n n) in
  emit n "push" "Viennot" ns;

  (* inject *)
  let (ns, dki) = time_ns_per_op n (fun () -> k8_inject_n n) in
  emit n "inject" "Cadeque8" ns;
  let (ns, dkfi) = time_ns_per_op n (fun () -> k8f_inject_n n) in
  emit n "inject" "Cadeque8_fast" ns;
  let (ns, dvi) = time_ns_per_op n (fun () -> vi_inject_n n) in
  emit n "inject" "Viennot" ns;

  (* pop *)
  let (ns, ()) = time_ns_per_op n (fun () -> k8_pop_all dk) in
  emit n "pop" "Cadeque8" ns;
  let (ns, ()) = time_ns_per_op n (fun () -> k8f_pop_all dkf) in
  emit n "pop" "Cadeque8_fast" ns;
  let (ns, ()) = time_ns_per_op n (fun () -> vi_pop_all dv) in
  emit n "pop" "Viennot" ns;

  (* eject *)
  let (ns, ()) = time_ns_per_op n (fun () -> k8_eject_all dki) in
  emit n "eject" "Cadeque8" ns;
  let (ns, ()) = time_ns_per_op n (fun () -> k8f_eject_all dkfi) in
  emit n "eject" "Cadeque8_fast" ns;
  let (ns, ()) = time_ns_per_op n (fun () -> vi_eject_all dvi) in
  emit n "eject" "Viennot" ns;

  (* concat: 100 iters *)
  let iters = 100 in
  let (ns, _) = time_ns_per_op iters
    (fun () ->
      let acc = ref dk in
      for _ = 1 to iters do acc := K.kcad8_concat !acc dk done; !acc)
  in
  emit n "concat" "Cadeque8" ns;
  let (ns, _) = time_ns_per_op iters
    (fun () ->
      let acc = ref dkf in
      for _ = 1 to iters do acc := K.kcad8_concat_fast !acc dkf done; !acc)
  in
  emit n "concat" "Cadeque8_fast" ns;
  let (ns, _) = time_ns_per_op iters
    (fun () ->
      let acc = ref dv in
      for _ = 1 to iters do acc := Vi.append !acc dv done; !acc)
  in
  emit n "concat" "Viennot" ns

let adv_chain_k8 ~depth ~per_chunk =
  let chunk () =
    let acc = ref K.kcad8_empty in
    for i = 0 to per_chunk - 1 do acc := K.kcad8_push i !acc done;
    !acc
  in
  let rec build d acc =
    if d <= 0 then acc else build (d - 1) (K.kcad8_concat acc (chunk ()))
  in
  build depth K.kcad8_empty

let adv_chain_vi ~depth ~per_chunk =
  let chunk () =
    let acc = ref Vi.empty in
    for i = 0 to per_chunk - 1 do acc := Vi.push i !acc done;
    !acc
  in
  let rec build d acc =
    if d <= 0 then acc else build (d - 1) (Vi.append acc (chunk ()))
  in
  build depth Vi.empty

let run_adv depth =
  let per_chunk = 100 in
  let total = depth * per_chunk in
  let dk = adv_chain_k8 ~depth ~per_chunk in
  let (ns, ()) = time_ns_per_op total (fun () -> k8_pop_all dk) in
  emit total "adv_pop" "Cadeque8" ns;
  let dv = adv_chain_vi ~depth ~per_chunk in
  let (ns, ()) = time_ns_per_op total (fun () -> vi_pop_all dv) in
  emit total "adv_pop" "Viennot" ns

let () =
  Printf.printf "n,op,impl,ns_per_op\n";
  let sizes =
    if Array.length Sys.argv > 1 then
      List.map int_of_string (List.tl (Array.to_list Sys.argv))
    else [1_000; 3_000; 10_000; 30_000; 100_000; 300_000; 1_000_000]
  in
  List.iter run sizes;
  List.iter run_adv [10; 30; 100; 300; 1000; 3000; 10000]
