(* Measure Viennot OCaml's alloc rate during pop drain. *)
module D = Viennot_deque.Deque.Base
let () =
  let n = 1_000_000 in
  let t = ref D.empty in
  for i = 1 to n do t := D.push i !t done;
  let stat0 = Gc.quick_stat () in
  let t0 = Unix.gettimeofday () in
  for _ = 1 to n do
    match D.pop !t with
    | Some (_, t') -> t := t'
    | None         -> ()
  done;
  let t1 = Unix.gettimeofday () in
  let stat1 = Gc.quick_stat () in
  Printf.printf "Viennot pop drain:\n";
  Printf.printf "  time: %.1f ms (%.1f ns/op)\n"
    ((t1 -. t0) *. 1000.0) ((t1 -. t0) *. 1e9 /. float_of_int n);
  Printf.printf "  minor_words allocated: %.0f (%.1f bytes/op)\n"
    (stat1.Gc.minor_words -. stat0.Gc.minor_words)
    ((stat1.Gc.minor_words -. stat0.Gc.minor_words) *. 8.0 /. float_of_int n);
  Printf.printf "  minor_collections: %d\n"
    (stat1.Gc.minor_collections - stat0.Gc.minor_collections);
  Printf.printf "  promoted_words: %.0f\n"
    (stat1.Gc.promoted_words -. stat0.Gc.promoted_words);
  Printf.printf "  major_collections: %d\n"
    (stat1.Gc.major_collections - stat0.Gc.major_collections)
