(** Cadeque8 (the §6 strict-WC O(1) catenable deque) vs Viennot's
    hand-coded reference, including adversarial workloads. *)

module K = KCadeque8
module Vi = Viennot_cadeque.Cadeque.Base

let time label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-32s %10.3f ms\n%!" label ((t1 -. t0) *. 1000.);
  r

let k8_push n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_push i !acc done;
  !acc

let k8_inject n =
  let acc = ref K.kcad8_empty in
  for i = 0 to n - 1 do acc := K.kcad8_inject !acc i done;
  !acc

let k8_pop_all d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match K.kcad8_pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

let k8_eject_all d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match K.kcad8_eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'; incr cnt
  done;
  !cnt

let k8_concat_iter base iter =
  let acc = ref base in
  for _ = 0 to iter - 1 do acc := K.kcad8_concat !acc base done;
  !acc

(* Viennot side *)
let vi_push n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.push i !acc done;
  !acc

let vi_pop_all d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Vi.pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

(* Adversarial *)
let adv_concat_chain ~depth ~per_chunk =
  let chunk () =
    let acc = ref K.kcad8_empty in
    for i = 0 to per_chunk - 1 do acc := K.kcad8_push i !acc done;
    !acc
  in
  let rec build d acc =
    if d <= 0 then acc else build (d - 1) (K.kcad8_concat acc (chunk ()))
  in
  build depth K.kcad8_empty

let run n =
  Printf.printf "\n=== Cadeque8 vs Viennot at N = %d ===\n\n" n;
  Printf.printf "Push N elements:\n";
  let d_k = time "K8 push"  (fun () -> k8_push n) in
  let d_v = time "Vi push" (fun () -> vi_push n) in
  Printf.printf "\nInject N elements:\n";
  let _ = time "K8 inject" (fun () -> k8_inject n) in
  Printf.printf "\nPop all N:\n";
  let _ = time "K8 pop" (fun () -> k8_pop_all d_k) in
  let _ = time "Vi pop" (fun () -> vi_pop_all d_v) in
  Printf.printf "\nEject all N:\n";
  let _ = time "K8 eject" (fun () -> k8_eject_all d_k) in
  ignore (d_v);
  let iter_concat = max 10 (1000 / max 1 (n / 1000)) in
  Printf.printf "\nConcat: %d iterations of concat(d, d) where |d|=%d:\n"
    iter_concat n;
  let _ = time "K8 concat" (fun () -> k8_concat_iter d_k iter_concat) in
  ()

let run_adv () =
  Printf.printf "\n=== Adversarial: pop-all after N concats × 100 elts ===\n";
  let do_one depth =
    let d = adv_concat_chain ~depth ~per_chunk:100 in
    let _ =
      time (Printf.sprintf "K8 pop-all (%d concats)" depth)
        (fun () -> k8_pop_all d)
    in ()
  in
  do_one 100;
  do_one 1000

let () =
  let sizes =
    if Array.length Sys.argv > 1 then
      List.map int_of_string (List.tl (Array.to_list Sys.argv))
    else [1_000; 10_000; 100_000]
  in
  List.iter run sizes;
  run_adv ();
  Printf.printf "\nDone.\n%!"
