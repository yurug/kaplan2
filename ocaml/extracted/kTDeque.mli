(** {1 KTDeque — a verified persistent real-time deque}

    A purely functional deque with worst-case O(1) per operation
    [push], [pop], [inject], [eject].  Every value of type
    {!kChain} is an immutable snapshot; an operation returns a new
    snapshot sharing structure with the old one, with no asymptotic
    penalty — you can fork the deque, mutate one branch, and the
    other branch is unaffected.

    This module is the OCaml extraction of the Rocq formalisation in
    [rocq/KTDeque/].  The sequence-preservation theorems live in
    [rocq/KTDeque/DequePtr/OpsKTSeq.v].  For *why* the algorithm is
    correct and elegant — why "no two reds adjacent" delivers
    worst-case O(1), why packets aggregate yellow runs into a single
    allocation — read [kb/spec/why-bounded-cascade.md] first.

    {2 Quick start}

    {[
      open KTDeque

      let push_or_fail x q =
        match push_kt2 (Coq_E.base x) q with
        | Some q' -> q'
        | None    -> failwith "regularity violated"

      let q = empty_kchain
      let q = push_or_fail 1 q
      let q = push_or_fail 2 q
      (* q now holds [2; 1] *)

      let xs = kchain_to_list q  (* [2; 1] *)
    ]}

    See also [ocaml/examples/hello.ml] for a fully runnable example.

    {2 Public API: where to look}

    Use one of the two operation families and the helpers below.
    Everything else is an internal extraction artefact (see
    {!section:internal} at the bottom of this file).

    Operations:
    - {!empty_kchain}, {!push_kt2}, {!pop_kt2}, {!inject_kt2},
      {!eject_kt2}, {!kchain_to_list} — the [kt2] family,
      [option]-returning, idiomatic with monadic [let*].
    - {!push_kt4}, {!pop_kt4}, {!inject_kt4}, {!eject_kt4} — the
      [kt4] family, returns flat sum types {!push_result} and
      {!pop_result}.  Equivalent semantics to [kt2] but saves one
      allocation per successful op.  Prefer for hot paths.

    Element wrapping:
    - {!Coq_E.base} — wrap a base value into the level-tagged
      element type {!Coq_E.t}.  Required because the verified deque
      stores level-l elements (sub-trees of paired-up base elements)
      rather than naked [\'a]; level-0 elements are exactly base
      values.
    - {!Coq_E.to_list} — flatten a level-l element back to a list of
      base values.

    {2 Why are there so many [push_*] functions?}

    The Rocq development proves several variants of each operation
    so that some lemmas can be stated against the variant most
    convenient for that proof, then transported to the production
    variant via equivalence theorems.  Specifically:

    - [push_chain] / [push_chain_naive]: partial naive push (no
      overflow handling).  Internal building block.
    - [push_chain_full] / [push_chain_rec]: recursive cascade.
      O(log n) per call — these are *proof artefacts*, not for
      production use.  See [kb/spec/why-bounded-cascade.md] §5.
    - [push_kt]: an early version with implicit colours.  Superseded.
    - [push_kt2]: explicit-colour, non-recursive, WC O(1).  This is
      the production code.
    - [push_kt3]: [push_kt2] with [yellow_wrap] inlined for the
      Yellow fast path; same semantics, smaller constant factor.
    - [push_kt4]: [push_kt3] with [option (X * Y)] return replaced
      by a flat 2-constructor sum type, saving one allocation per
      successful op.

    Use [push_kt2] for clarity, [push_kt4] for performance.  The
    other variants are not part of the supported public API.

    {2 A note for re-extraction}

    This [.mli] file is checked into git as a snapshot.  The body
    (every [type] and [val] declaration) is verbatim Coq extraction
    output; the surrounding [(** ... *)] documentation is hand-
    written.  When regenerating, please preserve the literate
    headers and per-binding doc comments.
*)

(** {1:internal Internal: extraction prelude}
    Coq's extracted module needs a small prelude of type aliases and
    helpers.  None of this is part of the user-facing API. *)

type __ = Obj.t

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



module Nat :
 sig
 end

type 'a xpow = __

val xflat : int -> 'a1 xpow -> 'a1 list

(** {1 Element abstraction}

    The verified deque stores [\'a Coq_E.t] values, not naked [\'a].
    A [\'a Coq_E.t] is a *level-l element*: at level 0 it is just an
    [\'a]; at level 1 it is a pair of two [\'a]s; at level [l] it is
    a balanced binary tree of [2^l] base values.  This is what makes
    the deque branch binarily as it descends through nested packets
    (see [kb/spec/why-bounded-cascade.md] §1 for the structural
    picture).

    User code only needs three of these functions:
    - {!Coq_E.base} to wrap an [\'a] into a level-0 [\'a Coq_E.t]
      before calling [push_kt2 / inject_kt2 / push_kt4 / inject_kt4];
    - {!Coq_E.to_list} to extract the underlying [\'a] values from
      whatever the deque returns at the top of pop / eject;
    - {!Coq_E.level} for diagnostics (the verified ops only ever
      return level-0 elements at the public surface, so [Coq_E.level
      e = 0] is a reasonable assertion).

    [pair] and [unpair] are internal — the deque uses them when
    cascading.

    [ElementTree] is the canonical instance; the deque uses it via
    the alias {!Coq_E}. *)

module ElementTree :
 sig
  type 'a t = (int, 'a xpow) sigT

  val to_list : 'a1 t -> 'a1 list

  val level : 'a1 t -> int

  val base : 'a1 -> 'a1 t

  val pair : 'a1 t -> 'a1 t -> 'a1 t

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
 end

(** {1 Buffer (Buf5) — internal storage at every level}

    A [\'x buf5] holds 0 to 5 elements at one chain level.  The buffer's
    *colour* is determined by its size:
    {ul
    {- 0 or 5 elements: Red — next op underflows or overflows;}
    {- 1 or 4 elements: Yellow — next op safe in at least one direction;}
    {- 2 or 3 elements: Green — next op safe in both directions.}}

    See [kb/spec/why-bounded-cascade.md] §2 for the regularity
    invariant that combines these colours.  User code never sees
    [buf5] directly. *)

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

(** {2 Internal: buffer-level operations}
    Building blocks for the chain-level operations above.  Not part
    of the public API. *)

val buf5_size : 'a1 buf5 -> int

val buf5_seq : ('a1 -> 'a2 list) -> 'a1 buf5 -> 'a2 list

val buf5_push_naive : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val buf5_inject_naive : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val buf5_pop_naive : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val buf5_eject_naive : 'a1 buf5 -> ('a1 buf5 * 'a1) option

module E :
 sig
  type 'a t = (int, 'a xpow) sigT

  val to_list : 'a1 t -> 'a1 list

  val level : 'a1 t -> int

  val base : 'a1 -> 'a1 t

  val pair : 'a1 t -> 'a1 t -> 'a1 t

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
 end

(** {1 Packet and Chain — the recursive shape}

    [\'a packet] is a *yellow run*: a nest of [PNode pre inner suf]
    layers terminated by [Hole].  In the C runtime, an entire packet
    is allocated as a single contiguous block — that aggregation is
    what keeps a chain repair O(1) instead of O(yellow-run-length).

    [\'a chain] is the older "implicit colour" representation, kept
    for cross-checks.  The {!kChain} type below is the production
    representation with explicit colour tags.  Use {!kChain} for new
    code. *)

type 'a packet =
| Hole
| PNode of 'a E.t buf5 * 'a packet * 'a E.t buf5

type 'a chain =
| Ending of 'a E.t buf5
| ChainCons of 'a packet * 'a chain

(** {2 Internal: chain-level building blocks (Chain, not kChain)}

    These work on the older implicit-colour {!chain} type.  The
    [_full] / [_rec] families are *recursive* (O(log n) per call) —
    they are proof artefacts used as targets for some Rocq lemmas,
    NOT for end-user consumption.  See [kb/spec/why-bounded-cascade.md]
    §5 for the proof-artefact-vs-production-code distinction.

    For the production WC O(1) ops, use the {!kt2} or {!kt4} family
    above. *)

val buf_seq_E : 'a1 E.t buf5 -> 'a1 list

val packet_seq : 'a1 packet -> 'a1 list -> 'a1 list

val chain_seq : 'a1 chain -> 'a1 list

val chain_to_list : 'a1 chain -> 'a1 list

val empty_chain : 'a1 chain

val push_chain : 'a1 E.t -> 'a1 chain -> 'a1 chain option

val inject_chain : 'a1 chain -> 'a1 E.t -> 'a1 chain option

val pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option

val make_red_push_chain : 'a1 chain -> 'a1 chain option

val make_red_inject_chain : 'a1 chain -> 'a1 chain option

val push_chain_full : 'a1 E.t -> 'a1 chain -> 'a1 chain option
(** {b Proof artefact}: recursive cascade, O(log n) per call.  Not
    for production use — use {!push_kt2} or {!push_kt4} instead. *)

val inject_chain_full : 'a1 chain -> 'a1 E.t -> 'a1 chain option
(** {b Proof artefact}: see {!push_chain_full}. *)

val push_chain_rec : 'a1 E.t -> 'a1 chain -> 'a1 chain option
(** {b Proof artefact}: see {!push_chain_full}. *)

val inject_chain_rec : 'a1 chain -> 'a1 E.t -> 'a1 chain option
(** {b Proof artefact}. *)

val pop_chain_rec : 'a1 chain -> ('a1 E.t * 'a1 chain) option
(** {b Proof artefact}. *)

val eject_chain_rec : 'a1 chain -> ('a1 chain * 'a1 E.t) option
(** {b Proof artefact}. *)

val make_green_pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val make_green_eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option

val pop_chain_full : 'a1 chain -> ('a1 E.t * 'a1 chain) option
(** {b Proof artefact}. *)

val eject_chain_full : 'a1 chain -> ('a1 chain * 'a1 E.t) option
(** {b Proof artefact}. *)

(** {1 Colours and regularity tags} *)

type color =
| Green
| Yellow
| Red
(** Buffer / packet colour.  See [kb/spec/why-bounded-cascade.md] §2
    for the regularity invariant ("no two Reds adjacent") that this
    type encodes. *)

val buf_color : 'a1 buf5 -> color
(** [buf_color b] is the colour of [b] determined by its size: B0/B5
    Red, B1/B4 Yellow, B2/B3 Green. *)

val color_meet : color -> color -> color
(** [color_meet c1 c2] is the meet under [Red >> Yellow >> Green];
    used to derive a packet's outer colour from its prefix and suffix
    buffer colours. *)

(** [Coq_E] is the deque's chosen ELEMENT instance — a transparent
    alias for {!ElementTree}.  All public deque ops accept and return
    [\'a Coq_E.t]; user code typically goes through [Coq_E.base] /
    [Coq_E.to_list] only.  The implementation under [Coq_E] is the
    same as under [ElementTree] (both are extractions of the same
    Rocq module), but the verified ops reference [Coq_E] specifically,
    so use it for type-equality with the deque's API surface. *)

module Coq_E :
 sig
  type 'a t = (int, 'a xpow) sigT
  (** Level-tagged element.  At level 0, isomorphic to [\'a]; at
      level [l > 0], a balanced tree of [2^l] base values. *)

  val to_list : 'a1 t -> 'a1 list
  (** [to_list e] flattens a level-l element to a list of [2^l] base
      values, in left-to-right order.  For a level-0 element built
      with [base x], returns [[x]]. *)

  val level : 'a1 t -> int
  (** [level e] is [l] such that [e] holds [2^l] base values. *)

  val base : 'a1 -> 'a1 t
  (** [base x] wraps a base value as a level-0 element.  This is the
      one constructor user code needs. *)

  val pair : 'a1 t -> 'a1 t -> 'a1 t
  (** Internal: combine two level-l elements into a level-(l+1)
      element.  Used by the cascade machinery. *)

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
  (** Internal: dual of {!pair}.  Returns [None] on a level-0
      element. *)
 end

(** {2 Internal: colour-dispatched buffer-level helpers}
    Used by the chain-level ops above.  [green_*] are partial on
    Red-sized inputs; [yellow_*] tolerate one direction of Yellow. *)

val green_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val green_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val yellow_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val yellow_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val green_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val green_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option

val yellow_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val yellow_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option

(** {2 Internal: small-buffer constructors and decomposers}
    Build B2/B3 buffers from optional plus-pair forms; case-split a
    buffer into "underflow / ok / overflow" branches.  Used inside
    {!make_small} and the concat helpers. *)

val prefix23 : 'a1 option -> ('a1 * 'a1) -> 'a1 buf5

val suffix23 : ('a1 * 'a1) -> 'a1 option -> 'a1 buf5

val suffix12 : 'a1 -> 'a1 option -> 'a1 buf5

type 'x bdecomp_pre =
| BD_pre_underflow of 'x option
| BD_pre_ok of 'x buf5
| BD_pre_overflow of 'x buf5 * 'x * 'x

type 'x bdecomp_suf =
| BD_suf_underflow of 'x option
| BD_suf_ok of 'x buf5
| BD_suf_overflow of 'x buf5 * 'x * 'x

val prefix_decompose : 'a1 buf5 -> 'a1 bdecomp_pre

val suffix_decompose : 'a1 buf5 -> 'a1 bdecomp_suf

type 'x bsandwich =
| BS_alone of 'x option
| BS_sandwich of 'x * 'x buf5 * 'x

val buffer_unsandwich : 'a1 buf5 -> 'a1 bsandwich

val prefix_rot : 'a1 -> 'a1 buf5 -> 'a1 buf5 * 'a1

val suffix_rot : 'a1 buf5 -> 'a1 -> 'a1 * 'a1 buf5

val buffer_halve : 'a1 buf5 -> 'a1 option * ('a1 * 'a1) buf5

(** {2 Internal: cross-buffer concat helpers}
    [{green,}_prefix_concat (b1, b2)] redistributes elements between
    two adjacent buffers so the result has acceptable colours.  Used
    inside [green_of_red] Cases 2 and 3. *)

val green_prefix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val green_suffix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val prefix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val suffix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

(** {2 Internal: rebalance primitives}
    {!make_small} (the depth-1 collapse), {!green_of_red} (the three-
    case red-to-green fix), {!ensure_green} (the fire-or-noop
    dispatch).  These are the heart of the WC-O(1) bound — see
    [kb/spec/why-bounded-cascade.md] §2-§3.  Public callers should
    use {!push_kt2} / {!push_kt4} etc., which compose these
    primitives correctly. *)

val buffer_push_chain : 'a1 Coq_E.t -> 'a1 Coq_E.t buf5 -> 'a1 chain

val buffer_inject_chain : 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t -> 'a1 chain

val pair_one : ('a1 Coq_E.t * 'a1 Coq_E.t) -> 'a1 Coq_E.t option

val pair_each_buf :
  ('a1 Coq_E.t * 'a1 Coq_E.t) buf5 -> 'a1 Coq_E.t buf5 option

val mk_ending_from_options :
  'a1 Coq_E.t option -> ('a1 Coq_E.t * 'a1 Coq_E.t) option -> 'a1 Coq_E.t
  option -> 'a1 chain

val make_small :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 chain option

val green_of_red : 'a1 chain -> 'a1 chain option

val pkt_outer_color : 'a1 packet -> color

val ensure_green : 'a1 chain -> 'a1 chain option

val make_yellow :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
  chain option

val make_red :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
  chain option

(** {2 Internal: superseded [kt] family}
    An early version with implicit colours, kept for proof
    cross-checks.  Use the [kt2]/[kt4] families above instead. *)

val push_kt : 'a1 Coq_E.t -> 'a1 chain -> 'a1 chain option

val inject_kt : 'a1 chain -> 'a1 Coq_E.t -> 'a1 chain option

val pop_kt : 'a1 chain -> ('a1 Coq_E.t * 'a1 chain) option

val eject_kt : 'a1 chain -> ('a1 chain * 'a1 Coq_E.t) option

(** {1 Public API: kt2 family ([option]-returning, recommended)}

    The verified worst-case O(1) deque, with [option] return types
    that integrate with monadic [let*].  All four ops:
    - return [Some _] on success;
    - return [None] only on a regularity-invariant violation (which,
      provably, cannot happen on a sequence of inputs starting from
      {!empty_kchain} — but the option is exposed because the
      extracted ops are total functions over arbitrary [kChain]
      values, not only the ones reachable from empty).

    Sequence semantics (proved in [OpsKTSeq.v]):
    {ul
    {- [push_kt2 x q = Some q'] implies
       [kchain_to_list q' = Coq_E.to_list x @ kchain_to_list q].}
    {- [inject_kt2 q x = Some q'] implies
       [kchain_to_list q' = kchain_to_list q @ Coq_E.to_list x].}
    {- [pop_kt2 q = Some (x, q')] implies
       [kchain_to_list q = Coq_E.to_list x @ kchain_to_list q'].}
    {- [eject_kt2 q = Some (q', x)] implies
       [kchain_to_list q = kchain_to_list q' @ Coq_E.to_list x].}}

    Cost (proved in [Footprint.v]): each op runs in worst-case O(1)
    primitive heap operations. *)

type 'a kChain =
| KEnding of 'a Coq_E.t buf5
| KCons of color * 'a packet * 'a kChain
(** A KT-style chain.  [KEnding b] is a single-buffer chain (typically
    a small deque); [KCons c p tl] adjoins a {!packet} [p] tagged
    with {!color} [c] to a tail chain.  The colour tag is contextual,
    not derivable from buffer sizes alone — see [OpsKT.v] header for
    why. *)

val empty_kchain : 'a1 kChain
(** The empty deque.  [kchain_to_list empty_kchain = []]. *)

val chain_to_kchain_g : 'a1 chain -> 'a1 kChain
(** Internal: lift a (Green) {!chain} into the colour-tagged
    {!kChain}.  All resulting [KCons] cells are tagged Green. *)

val kchain_to_chain : 'a1 kChain -> 'a1 chain
(** Internal: drop colour tags. *)

val kchain_to_list : 'a1 kChain -> 'a1 list
(** [kchain_to_list q] is the abstract sequence of [q], from front
    to back.  This is the *specification* of every operation: each
    op's effect on [kchain_to_list] is what its [_seq] lemma in
    [OpsKTSeq.v] proves. *)

val green_of_red_k : 'a1 kChain -> 'a1 kChain option
(** Internal: convert a Red-headed chain to a Green-headed chain in
    O(1).  The three structural cases are described in
    [kb/spec/why-bounded-cascade.md] §2 and [OpsKT.v]'s
    [green_of_red] section. *)

val ensure_green_k : 'a1 kChain -> 'a1 kChain option
(** Internal: if the chain top is tagged Red, fire {!green_of_red_k};
    otherwise, return as-is.  The WC-O(1) repair primitive — every
    public op ends with at most one [ensure_green_k] call. *)

val make_yellow_k :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option
(** Internal: prepend a Yellow-coloured packet to a chain, repairing
    the result via {!ensure_green_k} if necessary. *)

val make_red_k :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option
(** Internal: prepend a Red-coloured packet, then repair via
    {!ensure_green_k} (which fires {!green_of_red_k}). *)

val push_kt2 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option
(** [push_kt2 x q] prepends element [x] to the front of [q].  Returns
    [Some q'] with [kchain_to_list q' = Coq_E.to_list x @
    kchain_to_list q] on success.

    Worst-case O(1).  See [OpsKTSeq.v] [push_kt2_seq] for the proof.

    Use [Coq_E.base v] to wrap a base value [v : \'a] for this call. *)

val inject_kt2 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option
(** [inject_kt2 q x] appends element [x] to the back of [q].  Mirror
    of {!push_kt2}.  Worst-case O(1). *)

val pop_kt2 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option
(** [pop_kt2 q] removes and returns the front element of [q].
    Returns [None] if [q] is empty.  Worst-case O(1).

    The returned element [x : \'a Coq_E.t] is at level 0 by the
    sequence-preservation theorem; use [Coq_E.to_list x] to recover
    the underlying [\'a]. *)

val eject_kt2 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option
(** [eject_kt2 q] removes and returns the back element of [q].
    Mirror of {!pop_kt2}.  Worst-case O(1). *)

(** {1 Optimized variants: kt3 family}

    The [kt3] variants are operationally equivalent to [kt2] but
    inline [yellow_wrap] / [ensure_green_k] / [make_red_k] into the
    body of each op and special-case the common "tail is not Red"
    path.  Same return types as [kt2]; same correctness theorems
    (proved by [_kt3_seq] equivalences in [OpsKTSeq.v]).  Smaller
    constant factor in extracted OCaml code. *)

val yellow_wrap :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option
(** Internal: equivalent to [make_yellow_k] with {!ensure_green_k}
    inlined and the Yellow fast path special-cased. *)

val push_kt3 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option
(** [push_kt3 = push_kt2] semantically; faster constant factor. *)

val inject_kt3 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option
(** [inject_kt3 = inject_kt2] semantically. *)

val pop_kt3 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option
(** [pop_kt3 = pop_kt2] semantically. *)

val eject_kt3 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option
(** [eject_kt3 = eject_kt2] semantically. *)

(** {1 Public API: kt4 family (no-option, allocation-optimal)}

    The [kt4] variants replace the nested [option (X * Y)] return
    with a flat 2-constructor sum type: [push_result] for {!push_kt4}
    / {!inject_kt4}, [pop_result] for {!pop_kt4} / {!eject_kt4}.

    OCaml extracts [option (X * Y)] as a [Some] block holding a
    pointer to an [(X, Y)] tuple block — two allocations per
    successful op.  A flat sum is one block.  Hot loops that bench
    in the 25–80 ns/op range are allocation-bound; this saves one
    allocation and is the family used by the bench's headline
    numbers.

    Same correctness as [kt2]: the [_kt4 = _kt2] equivalence is
    proved at the bottom of [OpsKTSeq.v]. *)

type 'a push_result =
| PushFail
| PushOk of 'a kChain
(** Result of [push_kt4 / inject_kt4].  [PushFail] is the analogue
    of [None] (regularity-invariant violation; cannot happen on
    inputs reachable from {!empty_kchain}); [PushOk q'] is the
    analogue of [Some q']. *)

type 'a pop_result =
| PopFail
| PopOk of 'a Coq_E.t * 'a kChain
(** Result of [pop_kt4 / eject_kt4].  [PopFail] is "deque is empty";
    [PopOk (x, q')] is the popped element plus the remaining deque. *)

val yellow_wrap_pr :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  push_result
(** Internal: {!yellow_wrap} with the [push_result] return type. *)

val push_kt4 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 push_result
(** [push_kt4 x q]: same semantics as [push_kt2], allocation-optimal
    return.  Worst-case O(1). *)

val inject_kt4 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 push_result
(** [inject_kt4]: same semantics as [inject_kt2], allocation-optimal. *)

val pop_kt4 : 'a1 kChain -> 'a1 pop_result
(** [pop_kt4]: same semantics as [pop_kt2], allocation-optimal. *)

val eject_kt4 : 'a1 kChain -> 'a1 pop_result
(** [eject_kt4]: same semantics as [eject_kt2], allocation-optimal. *)
