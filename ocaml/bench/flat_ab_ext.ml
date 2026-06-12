let time f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (r, t1 -. t0)

let n = try int_of_string Sys.argv.(1) with _ -> 1_000_000
let reps = try int_of_string Sys.argv.(2) with _ -> 7

module O = KTCadequeFast
module N = KTFlatCadeque

let o_push n = let d = ref O.cad_empty in
  for i = 1 to n do d := O.cad_push_v2 i !d done; !d
let n_push n = let d = ref N.fcad_empty in
  for i = 1 to n do d := N.cad_push_x i !d done; !d

let o_popall d = let d = ref d and c = ref 0 in
  (try while true do match O.cad_pop_v2 !d with
     | Some (_, d') -> incr c; d := d' | None -> raise Exit done
   with Exit -> ()); !c
let n_popall d = let d = ref d and c = ref 0 in
  (try while true do match N.cad_pop_x !d with
     | Some (_, d') -> incr c; d := d' | None -> raise Exit done
   with Exit -> ()); !c

let o_ejall d = let d = ref d and c = ref 0 in
  (try while true do match O.cad_eject_v2 !d with
     | Some (d', _) -> incr c; d := d' | None -> raise Exit done
   with Exit -> ()); !c
let n_ejall d = let d = ref d and c = ref 0 in
  (try while true do match N.cad_eject_x !d with
     | Some (d', _) -> incr c; d := d' | None -> raise Exit done
   with Exit -> ()); !c

let o_block k = let d = ref O.cad_empty in
  for i = 1 to k do d := O.cad_inject_v2 !d i done; !d
let n_block k = let d = ref N.fcad_empty in
  for i = 1 to k do d := N.cad_inject_x !d i done; !d

let o_fold n =
  let b = o_block 64 in
  let d = ref O.cad_empty in
  for _ = 1 to n / 64 do
    match O.cad_concat_f !d b with Some c -> d := c | None -> assert false
  done; !d
let n_fold n =
  let b = n_block 64 in
  let d = ref N.fcad_empty in
  for _ = 1 to n / 64 do
    match N.cad_concat_x !d b with Some c -> d := c | None -> assert false
  done; !d

let o_fork n =
  let d = o_push 1024 in
  let acc = ref 0 in
  for _ = 1 to n do
    match O.cad_pop_v2 d with Some (x, _) -> acc := !acc + x | None -> ()
  done; !acc
let n_fork n =
  let d = n_push 1024 in
  let acc = ref 0 in
  for _ = 1 to n do
    match N.cad_pop_x d with Some (x, _) -> acc := !acc + x | None -> ()
  done; !acc

let bench name fo fn ops =
  let olds = ref [] and news = ref [] in
  for _ = 1 to reps do
    let (_, t1) = time (fun () -> ignore (Sys.opaque_identity (fo ()))) in
    let (_, t2) = time (fun () -> ignore (Sys.opaque_identity (fn ()))) in
    olds := t1 :: !olds; news := t2 :: !news
  done;
  let med l = List.nth (List.sort compare l) (List.length l / 2) in
  Printf.printf "%-10s old %4.0f   new(flat) %4.0f  ns/op\n%!"
    name (med !olds *. 1e9 /. float_of_int ops)
    (med !news *. 1e9 /. float_of_int ops)

let () =
  Printf.printf "A/B(ext) n=%d reps=%d (medians)\n%!" n reps;
  let od = o_push n and nd = n_push n in
  bench "pop-all" (fun () -> o_popall od) (fun () -> n_popall nd) n;
  bench "eject-all" (fun () -> o_ejall od) (fun () -> n_ejall nd) n;
  bench "fold" (fun () -> o_fold n) (fun () -> n_fold n) n;
  bench "fork" (fun () -> o_fork n) (fun () -> n_fork n) n
