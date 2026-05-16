(** Kc (KCadeque, Cadeque7 with KChain-backed Buf6) vs
    Vi (Viennot's hand-coded catenable cadeque).

    Skips the Cadeque6-spec Kt side which uses [cad_normalize] (O(n) per
    op) — interesting only as a soundness reference, not for timing.
    See [catenable_compare.ml] for the three-way version. *)

module Kc = KCadeque
module Vi = Viennot_cadeque.Cadeque.Base

let time label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-32s %10.3f ms\n%!" label ((t1 -. t0) *. 1000.);
  r

let kc_push n =
  let acc = ref Kc.kcad_empty in
  for i = 0 to n - 1 do acc := Kc.kcad_push i !acc done;
  !acc

let kc_inject n =
  let acc = ref Kc.kcad_empty in
  for i = 0 to n - 1 do acc := Kc.kcad_inject !acc i done;
  !acc

let kc_pop d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Kc.kcad_pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

let kc_eject d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Kc.kcad_eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'; incr cnt
  done;
  !cnt

let kc_concat base iter =
  let acc = ref base in
  for _ = 0 to iter - 1 do acc := Kc.kcad_concat !acc base done;
  !acc

let vi_push n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.push i !acc done;
  !acc

let vi_inject n =
  let acc = ref Vi.empty in
  for i = 0 to n - 1 do acc := Vi.inject !acc i done;
  !acc

let vi_pop d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Vi.pop !acc with
    | None -> cont := false
    | Some (_, d') -> acc := d'; incr cnt
  done;
  !cnt

let vi_eject d =
  let acc = ref d in
  let cnt = ref 0 in
  let cont = ref true in
  while !cont do
    match Vi.eject !acc with
    | None -> cont := false
    | Some (d', _) -> acc := d'; incr cnt
  done;
  !cnt

let vi_concat base iter =
  let acc = ref base in
  for _ = 0 to iter - 1 do acc := Vi.append !acc base done;
  !acc

let run n =
  Printf.printf "\n=== Kc (KCadeque) vs Vi (Viennot) at N = %d ===\n\n" n;
  Printf.printf "Push N elements:\n";
  let _ = time "Kc push" (fun () -> kc_push n) in
  let _ = time "Vi push" (fun () -> vi_push n) in
  Printf.printf "\nInject N elements:\n";
  let _ = time "Kc inject" (fun () -> kc_inject n) in
  let _ = time "Vi inject" (fun () -> vi_inject n) in
  let d_kc = kc_push n in
  let d_vi = vi_push n in
  Printf.printf "\nPop all N (preloaded via push):\n";
  let _ = time "Kc pop" (fun () -> kc_pop d_kc) in
  let _ = time "Vi pop" (fun () -> vi_pop d_vi) in
  Printf.printf "\nEject all N (preloaded via push):\n";
  let _ = time "Kc eject" (fun () -> kc_eject d_kc) in
  let _ = time "Vi eject" (fun () -> vi_eject d_vi) in
  let iter_concat = max 10 (1000 / max 1 (n / 1000)) in
  Printf.printf "\nConcat: %d iterations of concat(d, d) where |d|=%d:\n"
    iter_concat n;
  let _ = time "Kc concat" (fun () -> kc_concat d_kc iter_concat) in
  let _ = time "Vi concat" (fun () -> vi_concat d_vi iter_concat) in
  ()

(* Adversarial: build a deep KPair tree via repeated concat, then
   measure push/inject onto it.  Without Phase 5b, kcad_push on KPair
   recurses into the left subtree — O(depth) per call.  With Phase 5b
   it wraps as a fresh KSingle — O(1). *)
let adversarial_concat_then_push ~depth ~pushes =
  let base = kc_push 100 in
  let rec build k d =
    if d <= 0 then k else build (Kc.kcad_concat k base) (d - 1)
  in
  let k = build base depth in
  let acc = ref k in
  for i = 0 to pushes - 1 do acc := Kc.kcad_push i !acc done;
  !acc

let adversarial_concat_then_inject ~depth ~injects =
  let base = kc_push 100 in
  let rec build k d =
    if d <= 0 then k else build (Kc.kcad_concat k base) (d - 1)
  in
  let k = build base depth in
  let acc = ref k in
  for i = 0 to injects - 1 do acc := Kc.kcad_inject !acc i done;
  !acc

(* Worst case for pop: start with concat'd structure (KPair), inject many
   times — each inject builds a left-deep KPair (Phase 5b's tradeoff:
   O(1) inject at the cost of O(depth) pop).  Until Phase 5c implements
   the KT §6 head/middle/tail-deque mechanism, this is the residual gap.
*)
let adversarial_inject_then_pop ~prefix ~injects =
  let a = kc_push prefix in
  let b = kc_push prefix in
  let start = Kc.kcad_concat a b in
  let acc = ref start in
  for i = 0 to injects - 1 do acc := Kc.kcad_inject !acc i done;
  kc_pop !acc

(* Stress test for Phase 5c: many concats then drain.  Each concat
   wraps the previous result in a fresh KSingle with stored cells;
   after N concats the nesting depth is N.  Drain first hits the
   [kcad_pop] fallback which calls Coq-extracted [kcad_to_list] +
   [kcad_from_list].  Both are O(total) on a flat structure but
   [kcad_to_list] degenerates to **O(N × total)** on deeply-nested
   structures because it uses left-associative [app] from the Coq
   spec — each level concatenates its packet's content (which
   itself unfolds the entire prev recursive result via [++]).

   This is a Coq-spec limitation independent of Phase 5c's
   concat redesign.  Fixing it requires either:
   - An accumulator-style [kcad_to_list_fast] in Coq, proven
     equivalent to [kcad_to_list], used in the fallback.
   - The §12.4 [adopt6] incremental-unfold pop that doesn't
     materialize the full list at all. *)
let adversarial_concat_chain_then_drain ~depth ~per_chunk =
  let chunk () =
    let acc = ref Kc.kcad_empty in
    for i = 0 to per_chunk - 1 do acc := Kc.kcad_push i !acc done;
    !acc
  in
  let rec build d acc =
    if d <= 0 then acc else build (d - 1) (Kc.kcad_concat acc (chunk ()))
  in
  let k = build depth Kc.kcad_empty in
  kc_pop k

let run_adversarial () =
  Printf.printf "\n=== Adversarial: 100k ops on a depth-1000 KPair tree ===\n";
  let _ = time "Kc push  (after concat depth 1000)"
            (fun () -> adversarial_concat_then_push
                        ~depth:1000 ~pushes:100_000) in
  let _ = time "Kc inject (after concat depth 1000)"
            (fun () -> adversarial_concat_then_inject
                        ~depth:1000 ~injects:100_000) in
  Printf.printf "\n=== Adversarial: pop-all after concat+%d injects ===\n"
    10_000;
  let _ = time "Kc pop-all (after concat+10k injects)"
            (fun () -> adversarial_inject_then_pop
                        ~prefix:100 ~injects:10_000) in
  Printf.printf "\n=== Adversarial: pop-all after 100 concats of 100-elt chunks ===\n";
  let _ = time "Kc pop-all (100 concats × 100 elts)"
            (fun () -> adversarial_concat_chain_then_drain
                        ~depth:100 ~per_chunk:100) in
  Printf.printf "\n=== Adversarial: pop-all after 1000 concats of 100-elt chunks ===\n";
  let _ = time "Kc pop-all (1000 concats × 100 elts)"
            (fun () -> adversarial_concat_chain_then_drain
                        ~depth:1000 ~per_chunk:100) in
  ()

let () =
  let sizes =
    if Array.length Sys.argv > 1 then
      List.map int_of_string (List.tl (Array.to_list Sys.argv))
    else [1_000; 10_000; 100_000]
  in
  List.iter run sizes;
  run_adversarial ();
  Printf.printf "\nDone.\n%!"
