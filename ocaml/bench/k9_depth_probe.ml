(** k9_depth_probe -- public-operation depth guard for Cadeque9.

    This is decision evidence for Gate D.  The probe uses only public
    KCadeque9 operations to build states, then inspects the public extracted
    constructors to ensure the adversarial concat/drain sequence keeps
    StoredMiddle9 nesting depth within the current constant bound. *)

module K = KCadeque9

let of_list xs =
  List.fold_left K.kcad9_inject K.kcad9_empty xs

let singleton x =
  of_list [x]

let buf_of_list xs =
  List.fold_left K.buf6_inject K.buf6_empty xs

let base_buf xs =
  buf_of_list (List.map (fun x -> K.XBase9 x) xs)

let stored_small xs =
  K.StoredSmall9 (base_buf xs)

let stored_middle cells =
  K.StoredMiddle9 (buf_of_list cells)

let buf_append_probe a b =
  buf_of_list (K.buf6_elems a @ K.buf6_elems b)

let prepend_simple concat x d =
  concat (singleton x) d

let middle_inject rest sm =
  if K.buf6_is_empty sm then rest else K.buf6_inject rest (K.StoredMiddle9 sm)

let selective_open_back_base m1 t1 h2 m2_rest = function
  | K.StoredSmall9 b ->
      let cell = K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, b) in
      K.buf6_inject m1 cell
  | K.StoredBig9 (pre, sm, suf) ->
      let cell =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      K.buf6_inject (K.buf6_inject m1 cell) (K.StoredBig9 (pre, sm, suf))
  | K.StoredMiddle9 sm ->
      let cell =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      K.buf6_inject (K.buf6_inject m1 cell) (K.StoredMiddle9 sm)

let selective_open_back_middle_one m1 t1 h2 m2_rest = function
  | K.StoredMiddle9 sm ->
      (match K.buf6_eject sm with
       | Some (sm_rest, inner_back) ->
           selective_open_back_base
             m1
             t1
             h2
             (middle_inject m2_rest sm_rest)
             inner_back
       | None ->
           let cell =
             K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
           in
           K.buf6_inject m1 cell)
  | back_cell ->
      selective_open_back_base m1 t1 h2 m2_rest back_cell

let kcad9_concat_selective_open_back a b =
  match a, b with
  | K.K9Empty, _ -> b
  | _, K.K9Empty -> a
  | K.K9Simple ba, K.K9Simple bb ->
      K.K9Triple (ba, K.buf6_empty, bb)
  | K.K9Simple ba, K.K9Triple (h2, m2, t2) ->
      K.K9Triple (ba, K.buf6_push (K.StoredSmall9 h2) m2, t2)
  | K.K9Triple (h1, m1, t1), K.K9Simple bb ->
      K.K9Triple (h1, K.buf6_inject m1 (K.StoredSmall9 t1), bb)
  | K.K9Triple (h1, m1, t1), K.K9Triple (h2, m2, t2) ->
      let m_new =
        match K.buf6_eject m2 with
        | Some (m2_rest, back_cell) ->
            selective_open_back_middle_one m1 t1 h2 m2_rest back_cell
        | None ->
            let cell = K.StoredBig9 (t1, K.buf6_empty, h2) in
            K.buf6_inject m1 cell
      in
      K.K9Triple (h1, m_new, t2)

let maybe_inject_middle rest sm =
  if K.buf6_is_empty sm then rest else K.buf6_inject rest (K.StoredMiddle9 sm)

let big_split_open_back_base m1 t1 h2 m2_rest = function
  | K.StoredSmall9 b ->
      let cell = K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, b) in
      K.buf6_inject m1 cell
  | K.StoredMiddle9 sm ->
      let cell =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      K.buf6_inject (K.buf6_inject m1 cell) (K.StoredMiddle9 sm)
  | K.StoredBig9 (pre, sm, suf) ->
      let bridge =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      let rest = K.buf6_inject (K.buf6_inject m1 bridge) (K.StoredSmall9 pre) in
      let rest =
        match K.buf6_pop sm with
        | Some (front_cell, sm_rest) ->
            maybe_inject_middle (K.buf6_inject rest front_cell) sm_rest
        | None ->
            rest
      in
      K.buf6_inject rest (K.StoredSmall9 suf)

let big_split_open_back_middle_one m1 t1 h2 m2_rest = function
  | K.StoredMiddle9 sm ->
      (match K.buf6_eject sm with
       | Some (sm_rest, inner_back) ->
           big_split_open_back_base
             m1
             t1
             h2
             (middle_inject m2_rest sm_rest)
             inner_back
       | None ->
           let cell =
             K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
           in
           K.buf6_inject m1 cell)
  | back_cell ->
      big_split_open_back_base m1 t1 h2 m2_rest back_cell

let kcad9_concat_big_split_open_back a b =
  match a, b with
  | K.K9Empty, _ -> b
  | _, K.K9Empty -> a
  | K.K9Simple ba, K.K9Simple bb ->
      K.K9Triple (ba, K.buf6_empty, bb)
  | K.K9Simple ba, K.K9Triple (h2, m2, t2) ->
      K.K9Triple (ba, K.buf6_push (K.StoredSmall9 h2) m2, t2)
  | K.K9Triple (h1, m1, t1), K.K9Simple bb ->
      K.K9Triple (h1, K.buf6_inject m1 (K.StoredSmall9 t1), bb)
  | K.K9Triple (h1, m1, t1), K.K9Triple (h2, m2, t2) ->
      let m_new =
        match K.buf6_eject m2 with
        | Some (m2_rest, back_cell) ->
            big_split_open_back_middle_one m1 t1 h2 m2_rest back_cell
        | None ->
            let cell = K.StoredBig9 (t1, K.buf6_empty, h2) in
            K.buf6_inject m1 cell
      in
      K.K9Triple (h1, m_new, t2)

let tail_split_open_back_base m1 t1 h2 m2_rest t2 = function
  | K.StoredSmall9 b ->
      let cell = K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, b) in
      (K.buf6_inject m1 cell, t2)
  | K.StoredMiddle9 sm ->
      let cell =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      (K.buf6_inject (K.buf6_inject m1 cell) (K.StoredMiddle9 sm), t2)
  | K.StoredBig9 (pre, sm, suf) ->
      let bridge =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      let rest = K.buf6_inject (K.buf6_inject m1 bridge) (K.StoredSmall9 pre) in
      let rest =
        match K.buf6_pop sm with
        | Some (front_cell, sm_rest) ->
            maybe_inject_middle (K.buf6_inject rest front_cell) sm_rest
        | None ->
            rest
      in
      (rest, buf_append_probe suf t2)

let tail_split_open_back_middle_one m1 t1 h2 m2_rest t2 = function
  | K.StoredMiddle9 sm ->
      (match K.buf6_eject sm with
       | Some (sm_rest, inner_back) ->
           tail_split_open_back_base
             m1
             t1
             h2
             (middle_inject m2_rest sm_rest)
             t2
             inner_back
       | None ->
           let cell =
             K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
           in
           (K.buf6_inject m1 cell, t2))
  | back_cell ->
      tail_split_open_back_base m1 t1 h2 m2_rest t2 back_cell

let kcad9_concat_tail_split_open_back a b =
  match a, b with
  | K.K9Empty, _ -> b
  | _, K.K9Empty -> a
  | K.K9Simple ba, K.K9Simple bb ->
      K.K9Triple (ba, K.buf6_empty, bb)
  | K.K9Simple ba, K.K9Triple (h2, m2, t2) ->
      K.K9Triple (ba, K.buf6_push (K.StoredSmall9 h2) m2, t2)
  | K.K9Triple (h1, m1, t1), K.K9Simple bb ->
      K.K9Triple (h1, K.buf6_inject m1 (K.StoredSmall9 t1), bb)
  | K.K9Triple (h1, m1, t1), K.K9Triple (h2, m2, t2) ->
      let m_new, t_new =
        match K.buf6_eject m2 with
        | Some (m2_rest, back_cell) ->
            tail_split_open_back_middle_one m1 t1 h2 m2_rest t2 back_cell
        | None ->
            let cell = K.StoredBig9 (t1, K.buf6_empty, h2) in
            (K.buf6_inject m1 cell, t2)
      in
      K.K9Triple (h1, m_new, t_new)

let inject_stored_cells rest cells =
  List.fold_left K.buf6_inject rest (K.buf6_elems cells)

let full_split_open_back_base m1 t1 h2 m2_rest t2 = function
  | K.StoredSmall9 b ->
      let cell = K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, b) in
      (K.buf6_inject m1 cell, t2)
  | K.StoredMiddle9 sm ->
      let cell =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      (K.buf6_inject (K.buf6_inject m1 cell) (K.StoredMiddle9 sm), t2)
  | K.StoredBig9 (pre, sm, suf) ->
      let bridge =
        K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
      in
      let rest = K.buf6_inject (K.buf6_inject m1 bridge) (K.StoredSmall9 pre) in
      let rest = inject_stored_cells rest sm in
      (rest, buf_append_probe suf t2)

let full_split_open_back_middle_one m1 t1 h2 m2_rest t2 = function
  | K.StoredMiddle9 sm ->
      (match K.buf6_eject sm with
       | Some (sm_rest, inner_back) ->
           full_split_open_back_base
             m1
             t1
             h2
             (middle_inject m2_rest sm_rest)
             t2
             inner_back
       | None ->
           let cell =
             K.StoredBig9 (t1, K.buf6_push (K.StoredSmall9 h2) m2_rest, K.buf6_empty)
           in
           (K.buf6_inject m1 cell, t2))
  | back_cell ->
      full_split_open_back_base m1 t1 h2 m2_rest t2 back_cell

let kcad9_concat_full_split_open_back a b =
  match a, b with
  | K.K9Empty, _ -> b
  | _, K.K9Empty -> a
  | K.K9Simple ba, K.K9Simple bb ->
      K.K9Triple (ba, K.buf6_empty, bb)
  | K.K9Simple ba, K.K9Triple (h2, m2, t2) ->
      K.K9Triple (ba, K.buf6_push (K.StoredSmall9 h2) m2, t2)
  | K.K9Triple (h1, m1, t1), K.K9Simple bb ->
      K.K9Triple (h1, K.buf6_inject m1 (K.StoredSmall9 t1), bb)
  | K.K9Triple (h1, m1, t1), K.K9Triple (h2, m2, t2) ->
      let m_new, t_new =
        match K.buf6_eject m2 with
        | Some (m2_rest, back_cell) ->
            full_split_open_back_middle_one m1 t1 h2 m2_rest t2 back_cell
        | None ->
            let cell = K.StoredBig9 (t1, K.buf6_empty, h2) in
            (K.buf6_inject m1 cell, t2)
      in
      K.K9Triple (h1, m_new, t_new)

let max_buf_depth depth_of b =
  List.fold_left
    (fun acc x -> max acc (depth_of x))
    0
    (K.buf6_elems b)

let rec kelem_depth = function
  | K.XBase9 _ -> 0
  | K.XStored9 s -> stored_depth s

and stored_depth = function
  | K.StoredSmall9 b ->
      max_buf_depth kelem_depth b
  | K.StoredBig9 (pre, middle, suf) ->
      max
        (max_buf_depth kelem_depth pre)
        (max (middle_depth middle) (max_buf_depth kelem_depth suf))
  | K.StoredMiddle9 middle ->
      1 + middle_depth middle

and middle_depth b =
  max_buf_depth stored_depth b

let deque_middle_depth = function
  | K.K9Empty -> 0
  | K.K9Simple b -> max_buf_depth kelem_depth b
  | K.K9Triple (h, middle, t) ->
      max
        (max_buf_depth kelem_depth h)
        (max (middle_depth middle) (max_buf_depth kelem_depth t))

let top_middle_size = function
  | K.K9Triple (_, middle, _) -> K.buf6_size middle
  | K.K9Empty | K.K9Simple _ -> 0

let top_middle_depths = function
  | K.K9Triple (_, middle, _) ->
      List.map stored_depth (K.buf6_elems middle)
  | K.K9Empty | K.K9Simple _ -> []

let string_of_ints xs =
  String.concat "," (List.map string_of_int xs)

let check_list step expected d =
  let got = K.kcad9_to_list d in
  if got <> expected then begin
    Printf.eprintf
      "k9_depth_probe: sequence mismatch at step %d\n  got = [%s]\n  ref = [%s]\n"
      step
      (String.concat ";" (List.map string_of_int got))
      (String.concat ";" (List.map string_of_int expected));
    exit 1
  end

let assert_depth_at_most label step max_allowed_depth d =
  let depth = deque_middle_depth d in
  if depth > max_allowed_depth then begin
    Printf.eprintf
      "FAILED: %s step %d reached StoredMiddle9 depth %d, allowed %d\n"
      label
      step
      depth
      max_allowed_depth;
    exit 1
  end;
  depth

let pop_checked step expected d =
  match expected, K.kcad9_pop d with
  | x :: xs, Some (got, d') when got = x ->
      check_list step xs d';
      (xs, d')
  | x :: _, Some (got, _) ->
      Printf.eprintf
        "k9_depth_probe: pop mismatch at step %d: got %d, expected %d\n"
        step
        got
        x;
      exit 1
  | [], None ->
      ([], d)
  | [], Some (got, _) ->
      Printf.eprintf
        "k9_depth_probe: pop from empty reference returned %d at step %d\n"
        got
        step;
      exit 1
  | _ :: _, None ->
      Printf.eprintf
        "k9_depth_probe: pop failed on non-empty reference at step %d\n"
        step;
      exit 1

let find_depth_exceedance start_step max_allowed_depth expected d =
  let expected = ref expected in
  let d = ref d in
  let step = ref 0 in
  let found = ref None in
  while !expected <> [] do
    let depth = deque_middle_depth !d in
    if depth > max_allowed_depth then begin
      found := Some (start_step + !step, depth);
      expected := []
    end else begin
      let expected', d' = pop_checked (start_step + !step) !expected !d in
      expected := expected';
      d := d';
      incr step
    end
  done;
  !found

let run_depth_guard label concat =
  let left_values = [100; 101] in
  let left = concat (singleton 100) (singleton 101) in

  let seed =
    concat (singleton 10) (singleton 11)
    |> prepend_simple concat 9
    |> prepend_simple concat 8
  in
  let expected = ref [8; 9; 10; 11] in
  check_list 0 !expected seed;

  let iterations = 30 in
  let max_allowed_depth = 1 in
  let d = ref seed in
  let observed_max = ref (deque_middle_depth !d) in

  Printf.printf
    "k9_depth_probe: %s\n"
    label;
  Printf.printf
    "  step=%d len=%d top_middle=%d stored_middle_depth=%d depths=[%s]\n%!"
    0
    (List.length !expected)
    (top_middle_size !d)
    !observed_max
    (string_of_ints (top_middle_depths !d));

  for step = 1 to iterations do
    d := concat left !d;
    expected := left_values @ !expected;
    check_list step !expected !d;
    let depth = assert_depth_at_most label step max_allowed_depth !d in
    observed_max := max !observed_max depth;
    Printf.printf
      "  step=%d len=%d top_middle=%d stored_middle_depth=%d depths=[%s]\n%!"
      step
      (List.length !expected)
      (top_middle_size !d)
      depth
      (string_of_ints (top_middle_depths !d))
  done;

  let pop_step = ref 0 in
  while !expected <> [] do
    let depth = assert_depth_at_most label !pop_step max_allowed_depth !d in
    observed_max := max !observed_max depth;
    let expected', d' = pop_checked (1000 + !pop_step) !expected !d in
    expected := expected';
    d := d';
    incr pop_step
  done;
  check_list 2000 [] !d;

  Printf.printf
    "OK: %s max StoredMiddle9 depth stayed <= %d across %d concats and %d pops.\n"
    label
    max_allowed_depth
    iterations
    !pop_step

let run_depth_measure label concat =
  let left_values = [100; 101] in
  let left = concat (singleton 100) (singleton 101) in
  let seed =
    concat (singleton 10) (singleton 11)
    |> prepend_simple concat 9
    |> prepend_simple concat 8
  in
  let expected = ref [8; 9; 10; 11] in
  check_list 5000 !expected seed;
  let iterations = 30 in
  let d = ref seed in
  let observed_max = ref (deque_middle_depth !d) in
  for step = 1 to iterations do
    d := concat left !d;
    expected := left_values @ !expected;
    check_list (5000 + step) !expected !d;
    observed_max := max !observed_max (deque_middle_depth !d)
  done;
  let pop_step = ref 0 in
  while !expected <> [] do
    observed_max := max !observed_max (deque_middle_depth !d);
    let expected', d' = pop_checked (6000 + !pop_step) !expected !d in
    expected := expected';
    d := d';
    incr pop_step
  done;
  check_list 7000 [] !d;
  Printf.printf
    "MEASURE: %s max StoredMiddle9 depth = %d across %d concats and %d pops.\n"
    label
    !observed_max
    iterations
    !pop_step

let run_selective_nested_back_cell_guard () =
  let h1 = base_buf [0] in
  let t1 = base_buf [1] in
  let h2 = base_buf [2] in
  let t2 = base_buf [6] in
  let nested_back =
    K.StoredBig9
      (base_buf [3],
       buf_of_list [stored_middle [stored_small [4]]],
       base_buf [5])
  in
  let a = K.K9Triple (h1, K.buf6_empty, t1) in
  let b = K.K9Triple (h2, buf_of_list [nested_back], t2) in
  let d = kcad9_concat_selective_open_back a b in
  let expected = [0; 1; 2; 3; 4; 5; 6] in
  let label = "selective nested StoredBig9 back-cell guard" in
  check_list 3000 expected d;
  let initial_depth = assert_depth_at_most label 3000 1 d in
  match find_depth_exceedance 3001 1 expected d with
  | Some (step, depth) ->
      Printf.printf
        "EXPECTED-BLOCKER: %s starts at depth %d but reaches depth %d at drain step %d.\n"
        label
        initial_depth
        depth
        step
  | None ->
      Printf.eprintf
        "FAILED: %s no longer exposes the documented depth-growth blocker; update the Gate-D plan.\n"
        label;
      exit 1

let run_nested_back_cell_candidate_guard label concat expect_ok =
  let h1 = base_buf [0] in
  let t1 = base_buf [1] in
  let h2 = base_buf [2] in
  let t2 = base_buf [6] in
  let nested_back =
    K.StoredBig9
      (base_buf [3],
       buf_of_list [stored_middle [stored_small [4]]],
       base_buf [5])
  in
  let a = K.K9Triple (h1, K.buf6_empty, t1) in
  let b = K.K9Triple (h2, buf_of_list [nested_back], t2) in
  let d = concat a b in
  let expected = [0; 1; 2; 3; 4; 5; 6] in
  check_list 4000 expected d;
  let initial_depth = assert_depth_at_most label 4000 1 d in
  match expect_ok, find_depth_exceedance 4001 1 expected d with
  | true, Some (step, depth) ->
      Printf.eprintf
        "FAILED: %s starts at depth %d but reaches depth %d at drain step %d.\n"
        label
        initial_depth
        depth
        step;
      exit 1
  | true, None ->
      Printf.printf
        "OK: %s stayed <= depth 1 through the crafted drain (initial=%d).\n"
        label
        initial_depth
  | false, Some (step, depth) ->
      Printf.printf
        "EXPECTED-BLOCKER: %s starts at depth %d but reaches depth %d at drain step %d.\n"
        label
        initial_depth
        depth
        step
  | false, None ->
      Printf.eprintf
        "FAILED: %s no longer exposes the documented depth-growth blocker; update the Gate-D plan.\n"
        label;
      exit 1

let run_big_split_nested_back_cell_guard () =
  run_nested_back_cell_candidate_guard
    "big-split open-back nested StoredBig9 candidate guard"
    kcad9_concat_big_split_open_back
    true

let run_tail_split_nested_back_cell_guard () =
  run_nested_back_cell_candidate_guard
    "tail-split open-back nested StoredBig9 candidate guard"
    kcad9_concat_tail_split_open_back
    true

let run_full_split_nested_back_cell_guard () =
  run_nested_back_cell_candidate_guard
    "full-split open-back nested StoredBig9 candidate guard"
    kcad9_concat_full_split_open_back
    true

let run_big_split_repeated_measure () =
  run_depth_measure
    "big-split open-back concat candidate"
    kcad9_concat_big_split_open_back

let run_full_split_repeated_measure () =
  run_depth_measure
    "full-split open-back concat candidate"
    kcad9_concat_full_split_open_back

let run_tail_split_repeated_measure () =
  let label = "tail-split open-back concat candidate" in
  run_depth_measure label kcad9_concat_tail_split_open_back;
  let left = kcad9_concat_tail_split_open_back (singleton 100) (singleton 101) in
  let seed =
    kcad9_concat_tail_split_open_back (singleton 10) (singleton 11)
    |> prepend_simple kcad9_concat_tail_split_open_back 9
    |> prepend_simple kcad9_concat_tail_split_open_back 8
  in
  let expected = ref [8; 9; 10; 11] in
  let d = ref seed in
  let max_allowed_depth = 2 in
  let first_exceedance = ref None in
  for step = 1 to 30 do
    d := kcad9_concat_tail_split_open_back left !d;
    expected := [100; 101] @ !expected;
    check_list (8000 + step) !expected !d;
    let depth = deque_middle_depth !d in
    if depth > max_allowed_depth && !first_exceedance = None then
      first_exceedance := Some (step, depth)
  done;
  let pop_step = ref 0 in
  while !expected <> [] do
    let depth = deque_middle_depth !d in
    if depth > max_allowed_depth && !first_exceedance = None then
      first_exceedance := Some (!pop_step, depth);
    let expected', d' = pop_checked (9000 + !pop_step) !expected !d in
    expected := expected';
    d := d';
    incr pop_step
  done;
  match !first_exceedance with
  | Some (step, depth) ->
      Printf.printf
        "EXPECTED-BLOCKER: %s exceeds depth %d at schedule step %d with depth %d.\n"
        label
        max_allowed_depth
        step
        depth
  | None ->
      Printf.eprintf
        "FAILED: %s unexpectedly stayed within depth %d; update the Gate-D plan.\n"
        label
        max_allowed_depth;
      exit 1

let () =
  run_depth_guard
    "scheduled public KCadeque9 concat/refill depth guard"
    K.kcad9_concat;
  run_depth_guard
    "selective open-back concat candidate depth guard"
    kcad9_concat_selective_open_back;
  run_selective_nested_back_cell_guard ();
  run_big_split_repeated_measure ();
  run_big_split_nested_back_cell_guard ();
  run_full_split_repeated_measure ();
  run_full_split_nested_back_cell_guard ();
  run_tail_split_repeated_measure ();
  run_tail_split_nested_back_cell_guard ()
