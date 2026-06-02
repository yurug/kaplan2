(** Safe compatibility aliases for the former Cadeque9 hand-fused hot paths.

    Earlier versions of this module duplicated parts of [KCadeque9] in OCaml
    and used [Obj.magic] to unwrap level-0 payloads returned by [KTDeque].
    That optimization was outside the proved invariant/cost boundary.  Keep the
    public inline names available for existing benchmark and experiment code,
    but delegate to the extracted [_fast] operations.

    A future inlined implementation should be generated or proved against the
    same invariant as [KCadeque9] before being reintroduced as a release path. *)

let kcad9_push_inline = KCadeque9.kcad9_push_fast

let kcad9_inject_inline = KCadeque9.kcad9_inject_fast

let kcad9_pop_inline = KCadeque9.kcad9_pop_fast

let kcad9_eject_inline = KCadeque9.kcad9_eject_fast
