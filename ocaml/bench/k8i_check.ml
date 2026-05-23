(** k8i_check — differential correctness check: confirm
    [KCadeque8Inline.kcad8_pop_inline] and [kcad8_eject_inline]
    return the same values as [KCadeque8.kcad8_pop_fast] /
    [kcad8_eject_fast] on a long randomized sequence. *)

module K  = KCadeque8
module KI = KCadeque8Inline

let n = 2_000_000

let () =
  Random.init 0xCAFE;
  (* Build two deques (one for fast, one for inline) by interleaving
     push/inject/pop/eject. *)
  let dk_fast = ref K.kcad8_empty in
  let dk_inl  = ref K.kcad8_empty in
  for i = 0 to n - 1 do
    match Random.int 4 with
    | 0 ->
        dk_fast := K.kcad8_push_fast i !dk_fast;
        dk_inl  := KI.kcad8_push_inline i !dk_inl
    | 1 ->
        dk_fast := K.kcad8_inject_fast !dk_fast i;
        dk_inl  := KI.kcad8_inject_inline !dk_inl i
    | 2 ->
        (match K.kcad8_pop_fast !dk_fast, KI.kcad8_pop_inline !dk_inl with
         | K.PopFail8, K.PopFail8 -> ()
         | K.PopOk8 (x1, d1), K.PopOk8 (x2, d2) when x1 = x2 ->
             dk_fast := d1; dk_inl := d2
         | _ ->
             Printf.eprintf "MISMATCH on pop at step %d\n" i;
             exit 1)
    | _ ->
        (match K.kcad8_eject_fast !dk_fast, KI.kcad8_eject_inline !dk_inl with
         | K.EjectFail8, K.EjectFail8 -> ()
         | K.EjectOk8 (d1, x1), K.EjectOk8 (d2, x2) when x1 = x2 ->
             dk_fast := d1; dk_inl := d2
         | _ ->
             Printf.eprintf "MISMATCH on eject at step %d\n" i;
             exit 1)
  done;
  (* Final cross-check: drain both as lists. *)
  let l1 = K.kcad8_to_list !dk_fast in
  let l2 = K.kcad8_to_list !dk_inl in
  if l1 = l2
  then Printf.printf "k8i_check OK: %d ops, final list length = %d\n"
         n (List.length l1)
  else begin
    Printf.eprintf "FINAL LISTS DIFFER\n";
    exit 1
  end
