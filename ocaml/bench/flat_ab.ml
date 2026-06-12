(* flat_ab.ml — interleaved A/B: previous production artifact
   (KTCadequeFast, OpsFast/OpsFused mirror) vs the fused-spine artifact
   (KTFlatCadeque).  Same binary, alternating reps, so load noise hits
   both sides equally. *)

let time f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (r, t1 -. t0)

let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000
let reps = try int_of_string Sys.argv.(2) with _ -> 7

module Old = struct
  let push n =
    let d = ref KTCadequeFast.cad_empty in
    for i = 1 to n do d := KTCadequeFast.cad_push_v2 i !d done; !d
  let inject n =
    let d = ref KTCadequeFast.cad_empty in
    for i = 1 to n do d := KTCadequeFast.cad_inject_v2 !d i done; !d
  let mixed n =
    let d = ref KTCadequeFast.cad_empty in
    for i = 1 to n do
      d := KTCadequeFast.cad_push_v2 i !d;
      d := KTCadequeFast.cad_push_v2 i !d;
      (match KTCadequeFast.cad_pop_v2 !d with
       | Some (_, d') -> d := d' | None -> assert false)
    done; !d
end

module New = struct
  let push n =
    let d = ref KTFlatCadeque.fcad_empty in
    for i = 1 to n do d := KTFlatCadeque.cad_push_x i !d done; !d
  let inject n =
    let d = ref KTFlatCadeque.fcad_empty in
    for i = 1 to n do d := KTFlatCadeque.cad_inject_x !d i done; !d
  let mixed n =
    let d = ref KTFlatCadeque.fcad_empty in
    for i = 1 to n do
      d := KTFlatCadeque.cad_push_x i !d;
      d := KTFlatCadeque.cad_push_x i !d;
      (match KTFlatCadeque.cad_pop_x !d with
       | Some (_, d') -> d := d' | None -> assert false)
    done; !d
end

let bench name old_f new_f ops =
  let olds = ref [] and news = ref [] in
  for _ = 1 to reps do
    let (_, t1) = time (fun () -> ignore (Sys.opaque_identity (old_f n))) in
    let (_, t2) = time (fun () -> ignore (Sys.opaque_identity (new_f n))) in
    olds := t1 :: !olds; news := t2 :: !news
  done;
  let med l = List.nth (List.sort compare l) (List.length l / 2) in
  Printf.printf "%-8s old %.0f ns/op   new(flat) %.0f ns/op\n%!"
    name (med !olds *. 1e9 /. float_of_int ops)
    (med !news *. 1e9 /. float_of_int ops)

let () =
  Printf.printf "A/B n=%d reps=%d (medians)\n%!" n reps;
  bench "push" Old.push New.push n;
  bench "inject" Old.inject New.inject n;
  bench "mixed" Old.mixed New.mixed (3 * n)
