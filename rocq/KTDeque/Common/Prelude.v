(** * Module: KTDeque.Common.Prelude -- project-wide notations and re-exports.

    This module re-exports the small set of stdlib modules used across the
    project, sets implicit-arguments globally, and declares hint databases.
    Implements the "Common/Prelude.v" entry from manual §16.

    Key design decisions:
    - Plain Rocq stdlib only (ADR-0004).
    - Hint databases declared here so other files can [Hint Resolve]/[Hint Rewrite] into them.

    Cross-references:
    - kb/architecture/decisions/adr-0004-rocq-encoding-style.md
    - kb/conventions/code-style.md
    - kb/conventions/proof-style.md
*)

From Stdlib Require Export List.
From Stdlib Require Export PeanoNat.
From Stdlib Require Export Lia.
From Stdlib Require Export Bool.

Export ListNotations.

(* Implicit arguments are on, project-wide.  Per Q20 default. *)
Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Set Asymmetric Patterns.

(** ** Hint databases (kb/conventions/proof-style.md)

    [ktdeque]    constants from Params.v + basic arithmetic.
    [seq]        sequence-simplification rules across modules.
    [heap]       heap_ext lemmas + alloc lemmas.
    [regularity] color predicates and structural lemmas.

    Each is created here so files that issue [Hint Resolve … : <db>] do not
    need to re-create it. *)
#[export] Hint Constants Opaque : ktdeque seq heap regularity.

(** ** Convenience notations *)

(** [option_map] is in stdlib; we re-export under a shorter name when used
    locally inside proofs.  Nothing project-wide here yet — additions land
    here as patterns recur. *)
