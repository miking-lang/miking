open Ustring.Op

type 'a t

val create_array : int -> (int -> 'a) -> 'a t
(** [Rope.create_* n f] returns a new rope of length [n] where the element at
    index [i] is initialized as the result of [f i]. *)

val empty_array : 'a t
(** [Rope.empty_*] returns the representation of an empty rope. *)

val length_array : 'a t -> int
(** [Rope.length_* s] returns the length of the rope. *)

val concat_array : 'a t -> 'a t -> 'a t
(** [Rope.concat_* l r] returns a new rope representing the result of
    concatenating [l] and [r]. *)

val get_array : 'a t -> int -> 'a
(** [Rope.get_* s i] returns the element at index [i] of rope [s]. *)

val set_array : 'a t -> int -> 'a -> 'a t
(** [Rope.set_* s i v] returns a new rope representing the result of setting
    the value of [s] at index [i] to [v]. *)

val cons_array : 'a -> 'a t -> 'a t
(** [Rope.cons_* v s] returns a new rope representing the result of prepending
    [v] to [s]. *)

val snoc_array : 'a t -> 'a -> 'a t
(** [Rope.snoc_* s v] returns a new rope representing the result of appending
    [v] to the end of [s]. *)

val split_at_array : 'a t -> int -> 'a t * 'a t
(** [Rope.split_at_* s i] returns a pair of ropes representing the intervals
    0..i and i..n of [s], where n is the length of [s]. *)

val sub_array : 'a t -> int -> int -> 'a t
(** [Rope.sub_* s off cnt] returns a sub-rope representing the interval
    off..off+x of [s], where x is the minimum of the length of [s] minus [off]
    and [cnt]. *)

val iter_array : ('a -> unit) -> 'a t -> unit
(** [Rope.iter_* f s] applies [f] to all elements in [s]. This function
    collapses [s].*)

val iteri_array : (int -> 'a -> unit) -> 'a t -> unit
(** [Rope.iteri_* f s] same as [Rope.iter_*] but [f] takes the index of the
    element as its first argument and the element as its second element. This
    function collapses [s] *)

val map_array_array : ('a -> 'b) -> 'a t -> 'b t
(** [Rope.map_*_* f s] returns a rope representing the result of applying a
    function [f] on all elements of [s]. This function collapses [s]. *)

val mapi_array_array : (int -> 'a -> 'b) -> 'a t -> 'b t
(** [Rope.mapi_*_* f s] is the same as [Rope.map_*_* f s], but the function [f]
   is applied to the index of the element as its first element, and the element
   as its second argument. This function collapses [s]. *)

val foldl_array : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
(** [Rope.foldl_* f acc s] returns the result of applying [f] on the
    accumulated value, which is initially [acc] and the elements of [s],
    starting from the leftmost element. This function collapses [s]. *)

val map_accuml_array_array : ('a -> 'b -> 'a * 'c) -> 'a -> 'b t -> 'a * 'c t
(** [Rope.map_accuml_* f acc s] is a combination of [Rope.map_*_*] and
   [Rope.foldl_* f acc s] that threads an accumulator through calls to [f]. This
   function collapses [s]. *)

val reverse_array : 'a t -> 'a t
(** [Rope.reverse_* s] returns a new rope containing the elements of [s] in
    reversed order. This function collapses [s]. *)

val combine_array_array : 'a t -> 'b t -> ('a * 'b) t
(** [Rope.combine_*_* l r] returns a new rope where each element is a pair
    such that the left value represents the corresponding element in [l] and
    the right value represents the corresponding element in [r]. This function
    collapses [l] and [r]. Raises exception [Invalid_argument "Rope.combine"]
    if the lengths of [l] and [r] are not equal. *)

val equal_array : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** [Rope.equal_* f l r] returns true if [l] and [r] have the same lengths and
    all their elements are equal according to the comparison function [f]. This
    function collapses [l] and [r]. *)

val foldr_array : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(** [Rope.foldr_* f s acc] returns the result of applying [f] on the
    accumulated value, initially [acc], and the elements of [s], starting from
    the rightmost element. This function collapses [s]. *)

val foldr2_array : ('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
(** [Rope.foldr2_* f l r acc] returns the result of applying [f] on an
    accumulated value and the elements of two ropes [l] and [r], starting from
    the rightmost element. This function collapses [l] and [r]. Raises
    exception [Invalid_argument "Rope.foldr2"] if the lengths of [l] and [r]
    are not equal. *)

module Convert : sig
  val to_array_array : 'a t -> 'a array
  (** [Rope.Convert.to_array_* s] converts the rope [s] into an array. This
      function collapses [s] and returns a reference to the underlying data. *)

  val of_array_array : 'a array -> 'a t
  (** [Rope.Convert.of_array_* a] converts the array [a] into a rope. The
      underlying data is a reference to [a] so no copying is performed. *)

  val to_list_array : 'a t -> 'a list
  (** [Rope.Convert.to_list_* s] converts the rope [s] into a list. This
      function collapses [s]. *)

  val of_list_array : 'a list -> 'a t
  (** [Rope.Convert.of_list_* l] converts the list [l] into a rope. *)

  val to_ustring_array : int t -> ustring
  (** [Rope.Convert.to_ustring_* s] converts a rope of integers [s] into a
      ustring. This function collapses [s]. *)

  val of_ustring_array : ustring -> int t
  (** [Rope.Convert.of_ustring_* u] converts the ustring [u] into a rope of
      integers. *)
end
