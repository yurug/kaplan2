(** * Module: KTDeque.Cadeque6.Correctness -- re-export bundle.

    Single import point for the entire Cadeque6 development.

    A file that needs the Cadeque6 types, the abstract operations,
    the colour discipline, or the regularity predicate can write

      [From KTDeque.Cadeque6 Require Import Correctness.]

    and have everything in scope:

    - Types ([Triple], [Cadeque], [Stored]) and flattening.
    - Abstract operations ([cad_push] / [cad_inject] / [cad_pop] /
      [cad_eject] / [cad_concat] / [cad_singleton] / [cad_is_empty] /
      [cad_rev] / [cad_size] / fold_left / fold_right) + every
      proved sequence and algebra law.
    - Colour discipline ([Color4], [color4_meet], [buf6_color],
      [triple_color], [stored_color]).
    - Regularity predicates ([cad_nonempty], [semiregular_local],
      [semiregular_cad], [semiregular_triple], [regular_cad],
      [top_level_paths_green], [preferred_path_tail], plus the
      §10.9 structural lemmas).
    - Operational layer: [normalize_only_empty_child] reshape
      primitive plus operational versions of all five public
      operations: [cad_push_op], [cad_inject_op], [cad_pop_op],
      [cad_eject_op], [cad_concat_op].  Each comes with a
      sequence law.  Push and inject have full [regular_cad]
      preservation; the others have partial preservation for the
      simpler cases.

    This file introduces no new definitions or theorems; it is
    purely a convenience.

    ## Cross-references

    - [Cadeque6/Model.v]        -- types + flattening.
    - [Cadeque6/OpsAbstract.v]  -- operations + algebra laws.
    - [Cadeque6/Color.v]        -- four-colour discipline.
    - [Cadeque6/Regularity.v]   -- non-emptiness + preferred-path
                                   + (semi)regular invariants.
    - [Cadeque6/Repair.v]       -- operational repair primitives
                                   + cad_*_op operations.
    - [Cadeque6/Examples.v]     -- worked examples (not exported here
                                   to avoid polluting the namespace).
    - [kb/spec/why-catenable.md] -- intuition layer.
*)

From KTDeque.Cadeque6 Require Export Model OpsAbstract Color Regularity Repair.
