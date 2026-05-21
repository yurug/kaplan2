(** k8_alloc — measure allocation rate of push/inject for
    Cadeque8_fast vs Viennot's catenable.  This is the alloc
    breakdown that explains the residual ns/op gap. *)

module K  = KCadeque8
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
  Printf.printf "  %-30s %6.1f ns/op  %5.2f w/op  %4.0f b/op\n"
    label
    ((t1 -. t0) *. 1e9 /. float_of_int n)
    words_per_op
    bytes_per_op;
  ignore !t

let () =
  let n = 1_000_000 in
  Printf.printf "==== push (n = %d) ====\n" n;
  measure "Cadeque8 push (cert)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:K.kcad8_push;
  measure "Cadeque8 push_fast (flat)" ~n
    ~mk:(fun () -> K.kcad8_empty)
    ~op:K.kcad8_push_fast;
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
  measure "Viennot inject (ref)" ~n
    ~mk:(fun () -> Vi.empty)
    ~op:(fun i d -> Vi.inject d i)
