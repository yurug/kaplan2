(** Persistent real-time double-ended queue (Kaplan–Tarjan §4).

    A purely-functional deque: every operation returns a new deque and
    leaves its argument untouched, so a value can be shared and "forked"
    freely.  Each of {!push}, {!inject}, {!pop}, {!eject} runs in
    worst-case O(1) — not amortised — which is the property this
    structure exists for; it is the Rocq-verified [push_kt4] family
    (keystone [deque_wc_o1_*] in [rocq/KTDeque/DequePtr/DequeKeystone.v]),
    extracted to OCaml and wrapped here in an idiomatic interface.

    If you also need O(1) {b concatenation} of two deques, use
    {!Cadeque} instead.

    {2 Element convention}

    Elements are ordinary OCaml values of any type; the deque stores
    them by reference and never inspects them.

    {2 Example}

    {[
      let d = Deque.of_list [1; 2; 3] in        (* front = 1, back = 3 *)
      let d = Deque.push 0 d in                  (* [0; 1; 2; 3] *)
      match Deque.pop d with
      | Some (x, d') -> assert (x = 0); ignore d'
      | None -> assert false
    ]} *)

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
