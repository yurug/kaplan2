(** * Module: KTDeque.DequePtr.PublicTheoremsAudit --
      [Print Assumptions] for the Gate-B kt4 bundle.

    Building this file is the audit step for Gate B: each [Print
    Assumptions] statement reports what axioms the corresponding theorem
    in [PublicTheorems.v] depends on.

    Expected output: only standard logical axioms (e.g. [eq_rect_r]) or
    no project-local axioms.  If a [Print Assumptions] line ever surfaces
    a project-local [Axiom], [Admitted], or [Parameter] that is not part
    of an intentionally abstract module signature, the Gate-B claim is
    invalidated and the audit must be re-run.

    To see the output during a build run:

        dune build rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo --verbose

    Or use the make target wired by the runbook:

        make wc-o1-kt4-assumptions

    See [kb/runbooks/minimum-release-gate.md] §"Gate B" for context. *)

From KTDeque.DequePtr Require Import PublicTheorems.

Print Assumptions push_kt4_preserves_regular_top.
Print Assumptions inject_kt4_preserves_regular_top.
Print Assumptions pop_kt4_preserves_regular_top.
Print Assumptions eject_kt4_preserves_regular_top.
Print Assumptions yellow_wrap_pr_preserves_regular_top.

Print Assumptions push_kt4_seq_thm.
Print Assumptions inject_kt4_seq_thm.
Print Assumptions pop_kt4_seq_thm.
Print Assumptions eject_kt4_seq_thm.

Print Assumptions empty_kchain_regular_top_thm.
