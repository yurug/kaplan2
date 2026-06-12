(* push_prof.ml — single-workload profile target.
   argv: impl(kt|vi) n reps; prints ns/op and minor words/op. *)
let n = try int_of_string Sys.argv.(2) with _ -> 1_000_000
let reps = try int_of_string Sys.argv.(3) with _ -> 5

let run name f =
  let s0 = Gc.quick_stat () in
  let t0 = Unix.gettimeofday () in
  for _ = 1 to reps do ignore (Sys.opaque_identity (f n)) done;
  let t1 = Unix.gettimeofday () in
  let s1 = Gc.quick_stat () in
  let ops = float_of_int (n * reps) in
  Printf.printf
    "%s: %.1f ns/op, minor %.1f w/op, promoted %.1f w/op, major %.1f w/op, minor-gcs %d, major-gcs %d\n%!"
    name
    ((t1 -. t0) *. 1e9 /. ops)
    ((s1.Gc.minor_words -. s0.Gc.minor_words) /. ops)
    ((s1.Gc.promoted_words -. s0.Gc.promoted_words) /. ops)
    ((s1.Gc.major_words -. s0.Gc.major_words) /. ops)
    (s1.Gc.minor_collections - s0.Gc.minor_collections)
    (s1.Gc.major_collections - s0.Gc.major_collections)

let kt_push n =
  let d = ref KTFlatCadeque.fcad_empty in
  for i = 1 to n do d := KTFlatCadeque.cad_push_x i !d done; !d

let vi_push n =
  let d = ref Viennot_deque.Cadeque.empty in
  for i = 1 to n do d := Viennot_deque.Cadeque.push i !d done; !d

let kt_inject n =
  let d = ref KTFlatCadeque.fcad_empty in
  for i = 1 to n do d := KTFlatCadeque.cad_inject_x !d i done; !d

let vi_inject n =
  let d = ref Viennot_deque.Cadeque.empty in
  for i = 1 to n do d := Viennot_deque.Cadeque.inject !d i done; !d

let live name build =
  let d = build n in
  Gc.compact ();
  let s = Gc.quick_stat () in
  Printf.printf "%s: %.2f live words/element (n=%d)\n%!" name
    (float_of_int s.Gc.live_words /. float_of_int n) n;
  ignore (Sys.opaque_identity d)

let () =
  match Sys.argv.(1) with
  | "kt" -> run "kt-push" kt_push
  | "vi" -> run "vi-push" vi_push
  | "kti" -> run "kt-inject" kt_inject
  | "vii" -> run "vi-inject" vi_inject
  | "ktl" -> live "kt-live" kt_push
  | "vil" -> live "vi-live" vi_push
  | _ -> prerr_endline "usage: push_prof (kt|vi|kti|vii|ktl|vil) n reps"; exit 1
