(** Smoke test: does basic Cadeque9 work end-to-end? *)

module K = KCadeque9

let () =
  Printf.printf "Smoke: push 100\n%!";
  let d = ref K.kcad9_empty in
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 100 in
  for i = 0 to n - 1 do d := K.kcad9_push i !d done;
  Printf.printf "  size = %d\n%!" (List.length (K.kcad9_to_list !d));

  Printf.printf "Smoke: pop all\n%!";
  let count = ref 0 in
  let cont = ref true in
  while !cont do
    match K.kcad9_pop !d with
    | None -> cont := false
    | Some (_, d') -> d := d'; incr count
  done;
  Printf.printf "  popped = %d\n%!" !count;

  Printf.printf "Smoke: inject 100\n%!";
  let d = ref K.kcad9_empty in
  for i = 0 to n - 1 do d := K.kcad9_inject !d i done;
  Printf.printf "  size = %d\n%!" (List.length (K.kcad9_to_list !d));

  Printf.printf "Smoke: eject all\n%!";
  let count = ref 0 in
  let cont = ref true in
  while !cont do
    match K.kcad9_eject !d with
    | None -> cont := false
    | Some (d', _) -> d := d'; incr count
  done;
  Printf.printf "  ejected = %d\n%!" !count;

  Printf.printf "Smoke: done\n%!"
