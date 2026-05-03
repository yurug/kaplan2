(** Public Deque4 API: a Section-4 (non-catenable) double-ended queue.

    Operations: empty, is_empty, push, pop, inject, eject, to_list.
    Worst-case time complexity: O(1) for push, pop, inject, eject (per
    KT99); O(n) for to_list.

    This module re-exports the hand-written implementation by default.
    Switch to the extracted-from-Rocq form by editing the body below.

    Cross-references:
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
    - kb/spec/api-contracts.md (Section-4 API)
*)

include Deque4_handwritten
