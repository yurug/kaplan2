(** k9_compare — side-by-side throughput bench:
    Cadeque9 vs Cadeque8_inline vs Viennot.

    Mirrors the workloads from [k8_aggregate.ml] but adds Cadeque9.
    The headline question: how much does Cadeque9 give up on the
    fast paths (where Cadeque8_inline shines) in exchange for the
    closed (T+T) bug? *)

module K8  = KCadeque8
module K8I = KCadeque8Inline
module K9  = KCadeque9
module K9I = KCadeque9Inline
module Vi  = Viennot_cadeque.Cadeque.Base

let n = 100_000

let time_total label f =
  Printf.printf "  %-32s ... %!" label;
  let t0 = Unix.gettimeofday () in
  let () = f () in
  let t1 = Unix.gettimeofday () in
  let ns_per_op = (t1 -. t0) *. 1e9 /. float_of_int n in
  Printf.printf "%7.1f ns/op  (%.0f ms total)\n%!"
    ns_per_op ((t1 -. t0) *. 1000.0)

(* ---- push only ---- *)

let wl_push_k9 () =
  let d = ref K9.kcad9_empty in
  for i = 0 to n - 1 do d := K9.kcad9_push i !d done

let wl_push_k9i () =
  let d = ref K9.kcad9_empty in
  for i = 0 to n - 1 do d := K9I.kcad9_push_inline i !d done

let wl_push_k8i () =
  let d = ref K8.kcad8_empty in
  for i = 0 to n - 1 do d := K8I.kcad8_push_inline i !d done

let wl_push_vi () =
  let d = ref Vi.empty in
  for i = 0 to n - 1 do d := Vi.push i !d done

(* ---- inject only ---- *)

let wl_inject_k9 () =
  let d = ref K9.kcad9_empty in
  for i = 0 to n - 1 do d := K9.kcad9_inject !d i done

let wl_inject_k9i () =
  let d = ref K9.kcad9_empty in
  for i = 0 to n - 1 do d := K9I.kcad9_inject_inline !d i done

let wl_inject_k8i () =
  let d = ref K8.kcad8_empty in
  for i = 0 to n - 1 do d := K8I.kcad8_inject_inline !d i done

let wl_inject_vi () =
  let d = ref Vi.empty in
  for i = 0 to n - 1 do d := Vi.inject !d i done

(* ---- pop drain after push-build ---- *)

let drain_pop_k9 d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K9.kcad9_pop !d with
    | None -> cont := false
    | Some (_, d') -> d := d'
  done

let drain_pop_k9i d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K9I.kcad9_pop_inline !d with
    | K9.PopFail9 -> cont := false
    | K9.PopOk9 (_, d') -> d := d'
  done

let drain_pop_k8i d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K8I.kcad8_pop_inline !d with
    | K8.PopFail8 -> cont := false
    | K8.PopOk8 (_, d') -> d := d'
  done

let drain_pop_vi d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match Vi.pop !d with
    | None -> cont := false
    | Some (_, d') -> d := d'
  done

(* ---- eject drain after inject-build ---- *)

let drain_eject_k9 d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K9.kcad9_eject !d with
    | None -> cont := false
    | Some (d', _) -> d := d'
  done

let drain_eject_k9i d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K9I.kcad9_eject_inline !d with
    | K9.EjectFail9 -> cont := false
    | K9.EjectOk9 (d', _) -> d := d'
  done

let drain_eject_k8i d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match K8I.kcad8_eject_inline !d with
    | K8.EjectFail8 -> cont := false
    | K8.EjectOk8 (d', _) -> d := d'
  done

let drain_eject_vi d0 =
  let d = ref d0 in
  let cont = ref true in
  while !cont do
    match Vi.eject !d with
    | None -> cont := false
    | Some (d', _) -> d := d'
  done

(* ---- concat 100 iters at N ---- *)

let concat_iters = 100

let wl_concat_k9 dk9 () =
  let acc = ref dk9 in
  for _ = 1 to concat_iters do acc := K9.kcad9_concat !acc dk9 done

let wl_concat_k8 dk8 () =
  let acc = ref dk8 in
  for _ = 1 to concat_iters do acc := K8.kcad8_concat !acc dk8 done

let wl_concat_vi dvi () =
  let acc = ref dvi in
  for _ = 1 to concat_iters do acc := Vi.append !acc dvi done

let time_concat label f =
  let t0 = Unix.gettimeofday () in
  let () = f () in
  let t1 = Unix.gettimeofday () in
  let ns_per_op = (t1 -. t0) *. 1e9 /. float_of_int concat_iters in
  Printf.printf "  %-32s %7.1f ns/op  (%.0f ms total, %d iters)\n"
    label ns_per_op ((t1 -. t0) *. 1000.0) concat_iters

let () =
  Printf.printf "k9_compare: Cadeque9 vs Cadeque8_inline vs Viennot (n = %d)\n\n%!" n;

  Printf.printf "== push (build) ==\n%!";
  time_total "Cadeque9 push"          wl_push_k9;
  time_total "Cadeque9_inline push"   wl_push_k9i;
  time_total "Cadeque8_inline push"   wl_push_k8i;
  time_total "Viennot push"           wl_push_vi;

  Printf.printf "\n== inject (build) ==\n";
  time_total "Cadeque9 inject"          wl_inject_k9;
  time_total "Cadeque9_inline inject"   wl_inject_k9i;
  time_total "Cadeque8_inline inject"   wl_inject_k8i;
  time_total "Viennot inject"           wl_inject_vi;

  (* Build the test fixtures, then drain. *)
  Printf.printf "\n== pop (drain push-built) ==\n";
  let dk9 = ref K9.kcad9_empty in
  for i = 0 to n - 1 do dk9 := K9.kcad9_push i !dk9 done;
  let dk8 = ref K8.kcad8_empty in
  for i = 0 to n - 1 do dk8 := K8I.kcad8_push_inline i !dk8 done;
  let dvi = ref Vi.empty in
  for i = 0 to n - 1 do dvi := Vi.push i !dvi done;
  let dk9_for_inline = ref K9.kcad9_empty in
  for i = 0 to n - 1 do dk9_for_inline := K9I.kcad9_push_inline i !dk9_for_inline done;
  time_total "Cadeque9 pop"          (fun () -> drain_pop_k9  !dk9);
  time_total "Cadeque9_inline pop"   (fun () -> drain_pop_k9i !dk9_for_inline);
  time_total "Cadeque8_inline pop"   (fun () -> drain_pop_k8i !dk8);
  time_total "Viennot pop"           (fun () -> drain_pop_vi  !dvi);

  Printf.printf "\n== eject (drain inject-built) ==\n";
  let dk9i = ref K9.kcad9_empty in
  for i = 0 to n - 1 do dk9i := K9.kcad9_inject !dk9i i done;
  let dk8i = ref K8.kcad8_empty in
  for i = 0 to n - 1 do dk8i := K8I.kcad8_inject_inline !dk8i i done;
  let dvii = ref Vi.empty in
  for i = 0 to n - 1 do dvii := Vi.inject !dvii i done;
  let dk9i_for_inline = ref K9.kcad9_empty in
  for i = 0 to n - 1 do dk9i_for_inline := K9I.kcad9_inject_inline !dk9i_for_inline i done;
  time_total "Cadeque9 eject"          (fun () -> drain_eject_k9  !dk9i);
  time_total "Cadeque9_inline eject"   (fun () -> drain_eject_k9i !dk9i_for_inline);
  time_total "Cadeque8_inline eject"   (fun () -> drain_eject_k8i !dk8i);
  time_total "Viennot eject"           (fun () -> drain_eject_vi  !dvii);

  Printf.printf
    "\n== concat (100 iters at N) — skipped for raw Cadeque9 (no O(1) buf6_concat in spec) ==\n";
  time_concat "Cadeque8 concat"        (wl_concat_k8 !dk8);
  time_concat "Viennot append"         (wl_concat_vi !dvi)
