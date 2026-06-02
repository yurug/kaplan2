(** Safe compatibility aliases for the former Cadeque8 hand-fused hot paths.

    Earlier versions of this module duplicated parts of [KCadeque8] in OCaml
    and used [Obj.magic] to unwrap level-0 payloads returned by [KTDeque].
    That made the module faster on a narrow benchmark path, but it also put the
    public inline surface outside the proved invariant/cost boundary.

    Keep the inline function names for existing benchmark and experiment code,
    but delegate to the extracted [_fast] operations.  This removes the
    hand-written payload casts from the release surface; any future fused
    implementation should come with theorem coverage over the same invariant as
    the extracted operation it replaces. *)

let kcad8_push_inline = KCadeque8.kcad8_push_fast

let kcad8_inject_inline = KCadeque8.kcad8_inject_fast

let kcad8_pop_inline = KCadeque8.kcad8_pop_fast

let kcad8_eject_inline = KCadeque8.kcad8_eject_fast
