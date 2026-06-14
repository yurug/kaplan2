(** Persistent real-time {b catenable} double-ended queue (Kaplan–Tarjan §6).

    Everything {!Deque} offers — purely-functional, worst-case O(1)
    {!push} / {!inject} / {!pop} / {!eject} — {b plus} worst-case O(1)
    {!concat}: joining two deques of any sizes is a constant-time
    operation, not O(n).  This is the Rocq-verified §6 structure
    (keystone [cat_keystone_*] + cost bound [cat_wc_o1] in
    [rocq/KTDeque/Catenable/]), extracted to OCaml and wrapped here.

    Use this when you need catenation; if you only ever push/pop at the
    ends, {!Deque} has a smaller constant factor.

    {2 Example}

    {[
      let a = Cadeque.of_list [1; 2; 3] in
      let b = Cadeque.of_list [4; 5; 6] in
      let c = Cadeque.concat a b in              (* O(1), [1;2;3;4;5;6] *)
      assert (Cadeque.to_list c = [1;2;3;4;5;6])
    ]} *)

type 'a t
(** A persistent catenable deque of elements of type ['a]. *)

val empty : 'a t
(** The empty catenable deque. *)

val is_empty : 'a t -> bool
(** [is_empty d] is [true] iff [d] has no elements.  O(1). *)

val push : 'a -> 'a t -> 'a t
(** [push x d] adds [x] at the {b front}.  O(1) worst case. *)

val inject : 'a t -> 'a -> 'a t
(** [inject d x] adds [x] at the {b back}.  O(1) worst case. *)

val pop : 'a t -> ('a * 'a t) option
(** Remove the {b front} element, or [None] if empty.  O(1) worst case. *)

val eject : 'a t -> ('a t * 'a) option
(** Remove the {b back} element, or [None] if empty.  O(1) worst case. *)

val concat : 'a t -> 'a t -> 'a t
(** [concat a b] is the deque whose elements are those of [a] followed
    by those of [b].  {b O(1) worst case} regardless of the sizes of
    [a] and [b] — the defining operation of this structure. *)

val peek_front : 'a t -> 'a option
(** The front element without removing it, or [None] if empty.  O(1). *)

val peek_back : 'a t -> 'a option
(** The back element without removing it, or [None] if empty.  O(1). *)

val length : 'a t -> int
(** Number of elements.  {b O(n)}.  For an emptiness test use
    {!is_empty}. *)

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
(** Build from a sequence (front-to-back order).  O(n). *)
