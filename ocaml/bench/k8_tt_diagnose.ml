(** Diagnose: what shape is the deque AFTER (T+T) concat with my fix?
    Trace through enough ejects to see which cell shapes appear. *)

module K = KCadeque8

let n = 100

let inspect_top label k =
  Printf.printf "  %s: " label;
  match k with
  | K.K8Empty -> Printf.printf "K8Empty\n"
  | K.K8Simple _ -> Printf.printf "K8Simple\n"
  | K.K8Triple _ -> Printf.printf "K8Triple\n"

let () =
  let half = ref K.kcad8_empty in
  for i = 0 to n - 1 do half := K.kcad8_push i !half done;
  let t1 = K.kcad8_concat !half !half in
  let t2 = K.kcad8_concat !half !half in
  Printf.printf "Setup: t1 = K8Triple? %b, t2 = K8Triple? %b\n"
    (match t1 with K.K8Triple _ -> true | _ -> false)
    (match t2 with K.K8Triple _ -> true | _ -> false);
  let combined = K.kcad8_concat t1 t2 in
  inspect_top "combined" combined;
  let d = ref combined in
  (* Eject one at a time and time each *)
  let max_ns = ref 0.0 in
  for i = 1 to 4 * n do
    let t0 = Unix.gettimeofday () in
    (match K.kcad8_eject !d with
     | None -> ()
     | Some (d', _) -> d := d');
    let t1 = Unix.gettimeofday () in
    let ns = (t1 -. t0) *. 1e9 in
    if ns > !max_ns then begin
      max_ns := ns;
      Printf.printf "  eject %d: %.0f ns (new max)\n" i ns
    end
  done;
  Printf.printf "Done.  Max eject: %.0f ns\n" !max_ns
