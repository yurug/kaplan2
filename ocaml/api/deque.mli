(** Persistent real-time double-ended queue.

    A {e deque} ("double-ended queue", pronounced "deck") is a sequence
    you can grow and shrink at {b both} ends: {!push} / {!pop} act on the
    front, {!inject} / {!eject} on the back.  Picture an OCaml list that
    is just as cheap to extend or peel off on the right as on the left.

    Two properties make this particular implementation worth having.

    {2 Persistent (purely functional)}

    No operation mutates its argument.  Each returns a {e new} deque and
    leaves the old one fully valid, so you may keep, share, and reuse any
    past version freely.  For example, pushing two different elements onto
    the same [d] yields two independent deques that transparently share
    their common structure:

    {[
      let d  = Deque.of_list [1; 2] in
      let d1 = Deque.push 0 d in          (* [0; 1; 2]              *)
      let d2 = Deque.push 9 d in          (* [9; 1; 2] — d untouched *)
    ]}

    {2 Real-time (worst-case O(1))}

    Every individual {!push}, {!inject}, {!pop} and {!eject} costs a
    bounded, constant number of steps — {b worst case}, not amortised.

    The distinction matters.  An {e amortised}-O(1) structure is allowed
    the occasional expensive operation as long as the long-run average
    stays constant (a dynamic array doubling its backing store, say).
    Here there is no such operation: no call ever stalls to "catch up" on
    deferred work.  That makes the structure safe for latency-sensitive
    code — interactive loops, real-time systems, anything where a single
    slow call is unacceptable.  Achieving this {e and} persistence
    {e and} O(1) at once is the hard result Kaplan and Tarjan's design
    delivers, and the reason this structure exists.

    The implementation is not hand-written: it is {e extracted} from a
    proof in the Rocq proof assistant (formerly Coq) that mechanically
    checks the worst-case-O(1) bound, then wrapped unchanged behind this
    interface.  See {b Provenance} at the end for the paper reference.

    Need O(1) {b concatenation} of two whole deques as well?  Use
    {!Cadeque}; it adds [concat] at the price of a slightly larger
    constant factor on the other operations.

    {2 Elements}

    Elements are arbitrary OCaml values of any type.  The deque stores
    them by reference and never inspects, compares, or copies them.

    {2 Example}

    {[
      let d = Deque.of_list [1; 2; 3] in   (* front = 1, back = 3      *)
      let d = Deque.push 0 d in            (* front: [0; 1; 2; 3]      *)
      let d = Deque.inject d 4 in          (* back:  [0; 1; 2; 3; 4]   *)
      match Deque.pop d with
      | Some (x, d') -> assert (x = 0); ignore d'
      | None -> assert false
    ]}

    {2 Provenance}

    This module implements the non-catenable real-time deque of section 4
    of Haim Kaplan and Robert E. Tarjan, {e Purely Functional, Real-Time
    Deques with Catenation}, Journal of the ACM 46(5), 1999.  {!Cadeque}
    implements the catenable construction from section 6 of the same
    paper.  Both are machine-checked in the Rocq proof assistant; the
    proofs live in the [rocq/] subtree of the project's source
    repository,
    {{:https://github.com/yurug/kaplan2}https://github.com/yurug/kaplan2}. *)

type 'a t
(** A persistent deque of elements of type ['a]. *)

val empty : 'a t
(** The empty deque. *)

val is_empty : 'a t -> bool
(** [is_empty d] is [true] iff [d] has no elements.  O(1). *)

val push : 'a -> 'a t -> 'a t
(** [push x d] adds [x] at the {b front}.  O(1) worst case. *)

val inject : 'a t -> 'a -> 'a t
(** [inject d x] adds [x] at the {b back}.  O(1) worst case. *)

val pop : 'a t -> ('a * 'a t) option
(** [pop d] removes the {b front} element: [Some (x, d')] where [x] was
    the front and [d'] is the rest, or [None] if [d] is empty.  O(1)
    worst case. *)

val eject : 'a t -> ('a t * 'a) option
(** [eject d] removes the {b back} element: [Some (d', x)] where [x] was
    the back and [d'] is the rest, or [None] if [d] is empty.  O(1)
    worst case. *)

val peek_front : 'a t -> 'a option
(** The front element without removing it, or [None] if empty.  O(1). *)

val peek_back : 'a t -> 'a option
(** The back element without removing it, or [None] if empty.  O(1). *)

val length : 'a t -> int
(** Number of elements.  {b O(n)} — walks the whole structure; not a
    cached size.  For an emptiness test prefer {!is_empty}. *)

val to_list : 'a t -> 'a list
(** All elements, front to back.  O(n). *)

val of_list : 'a list -> 'a t
(** [of_list xs] builds a deque whose front-to-back order is [xs].
    O(n). *)

val iter : ('a -> unit) -> 'a t -> unit
(** [iter f d] applies [f] to each element, front to back.  O(n). *)

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(** Left fold over elements, front to back.  O(n). *)

val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
(** Right fold over elements, front to back.  O(n). *)

val to_seq : 'a t -> 'a Seq.t
(** Elements as a sequence, front to back.  O(n) total. *)

val of_seq : 'a Seq.t -> 'a t
(** Build a deque from a sequence (front-to-back order).  O(n). *)
