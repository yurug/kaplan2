(** k8_alloc — measure allocation rate of push/inject for
    Cadeque8_fast vs Viennot's catenable.  This is the alloc
    breakdown that explains the residual ns/op gap. *)

module K  = KCadeque8
module KI = KCadeque8Inline
module Vi = Viennot_cadeque.Cadeque.Base

let measure label ~n ~mk ~op =
  let t = ref (mk ()) in
  let stat0 = Gc.quick_stat () in
  let t0 = Unix.gettimeofday () in
  for i = 0 to n - 1 do t := op i !t done;
  let t1 = Unix.gettimeofday () in
  let stat1 = Gc.quick_stat () in
  let bytes_per_op =
    (stat1.Gc.minor_words -. stat0.Gc.minor_words) *. 8.0 /. float_of_int n
  in
  let words_per_op = bytes_per_op /. 8.0 in
  Printf.printf "  %-32s %6.1f ns/op  %5.2f w/op  %4.0f b/op\n"
    label
    ((t1 -. t0) *. 1e9 /. float_of_int n)
    words_per_op
    bytes_per_op;
  ignore !t

(* Drain-style measurement for pop/eject: takes a [drain] closure that
   pops/ejects [n] times in place and returns unit. *)
let measure_drain label ~n ~mk ~drain =
  let v = mk () in
  let stat0 = Gc.quick_stat () in
  let t0 = Unix.gettimeofday () in
  drain v;
  let t1 = Unix.gettimeofday () in
  let stat1 = Gc.quick_stat () in
  let bytes_per_op =
    (stat1.Gc.minor_words -. stat0.Gc.minor_words) *. 8.0 /. float_of_int n
  in
  let words_per_op = bytes_per_op /. 8.0 in
  Printf.printf "  %-32s %6.1f ns/op  %5.2f w/op  %4.0f b/op\n"
    label
    ((t1 -. t0) *. 1e9 /. float_of_int n)
    words_per_op
    bytes_per_op

let () =
  let n = 1_000_000 in
  Printf.printf "==== push (n = %d) ====\n" n;
  measure "Cadeque8 push (cert)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:K.kcad8_push;
  measure "Cadeque8 push_fast (flat)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:K.kcad8_push_fast;
  measure "Cadeque8 push_inline (1-call)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:KCadeque8Inline.kcad8_push_inline;
  measure "Viennot push (ref)" ~n
    ~mk:(fun () -> Vi.empty)
    ~op:Vi.push;
  Printf.printf "\n==== inject (n = %d) ====\n" n;
  measure "Cadeque8 inject (cert)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:(fun i d -> K.kcad8_inject d i);
  measure "Cadeque8 inject_fast (flat)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:(fun i d -> K.kcad8_inject_fast d i);
  measure "Cadeque8 inject_inline (1-call)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:(fun i d -> KCadeque8Inline.kcad8_inject_inline d i);
  measure "Viennot inject (ref)" ~n
    ~mk:(fun () -> Vi.empty)
    ~op:(fun i d -> Vi.inject d i);
  Printf.printf "\n==== pop (n = %d) ====\n" n;
  let build_k () =
    let d = ref K.kcad8_empty in
    for i = 0 to n - 1 do d := K.kcad8_push i !d done; !d
  in
  let build_vi () =
    let d = ref Vi.empty in
    for i = 0 to n - 1 do d := Vi.push i !d done; !d
  in
  measure_drain "Cadeque8 pop_fast" ~n ~mk:build_k
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match K.kcad8_pop_fast !d with
        | K.PopFail8 -> ()
        | K.PopOk8 (_, d') -> d := d'
      done);
  measure_drain "Cadeque8 pop_inline" ~n ~mk:build_k
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match KI.kcad8_pop_inline !d with
        | K.PopFail8 -> ()
        | K.PopOk8 (_, d') -> d := d'
      done);
  measure_drain "Viennot pop" ~n ~mk:build_vi
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match Vi.pop !d with
        | None -> ()
        | Some (_, d') -> d := d'
      done);
  Printf.printf "\n==== eject (n = %d) ====\n" n;
  let build_ki () =
    let d = ref K.kcad8_empty in
    for i = 0 to n - 1 do d := K.kcad8_inject !d i done; !d
  in
  let build_vii () =
    let d = ref Vi.empty in
    for i = 0 to n - 1 do d := Vi.inject !d i done; !d
  in
  measure_drain "Cadeque8 eject_fast" ~n ~mk:build_ki
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match K.kcad8_eject_fast !d with
        | K.EjectFail8 -> ()
        | K.EjectOk8 (d', _) -> d := d'
      done);
  measure_drain "Cadeque8 eject_inline" ~n ~mk:build_ki
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match KI.kcad8_eject_inline !d with
        | K.EjectFail8 -> ()
        | K.EjectOk8 (d', _) -> d := d'
      done);
  measure_drain "Viennot eject" ~n ~mk:build_vii
    ~drain:(fun d0 ->
      let d = ref d0 in
      for _ = 0 to n - 1 do
        match Vi.eject !d with
        | None -> ()
        | Some (d', _) -> d := d'
      done)
