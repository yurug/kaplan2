(** Hand-written Deque4 used by the bench harness only.

    Operations: empty, is_empty, push, pop, inject, eject, to_list.
    Time complexity: amortized O(log n) per op (the hand-written cell
    layout cascades a recursive spill on overflow); O(n) for to_list.
    NOT worst-case O(1): for the WC O(1) deque, see the verified
    [KTDeque] library in `ocaml/extracted/`.

    This module re-exports the hand-written implementation; it exists
    so the bench drivers can compare the verified extraction against
    a different functional design point.  Not part of the public
    [ktdeque] opam package.

    Cross-references:
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
    - kb/spec/api-contracts.md (Section-4 API)
*)

include Deque4_handwritten
