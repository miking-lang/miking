open Bigarray
open Ustring.Op

type ('a, 'b) ba = ('a, 'b, c_layout) Array1.t

type int_ba = (int, int_elt) ba

type float_ba = (float, float64_elt) ba

type 'a t

val create_array : int -> (int -> 'a) -> 'a array t
(** [Rope.create_* n f] returns a new rope of length [n] where the element at
    index [i] is initialized as the result of [f i]. *)

val create_int_bigarray : int -> (int -> int) -> int_ba t

val create_float_bigarray : int -> (int -> float) -> float_ba t

val empty_array : 'a array t
(** [Rope.empty_*] returns the representation of an empty rope. *)

val empty_int_bigarray : int_ba t

val empty_float_bigarray : float_ba t

val length_array : 'a array t -> int
(** [Rope.length_* s] returns the length of the rope. *)

val length_bigarray : ('a, 'b) ba t -> int

val concat_array : 'a array t -> 'a array t -> 'a array t
(** [Rope.concat_* l r] returns a new rope representing the result of
    concatenating [l] and [r]. *)

val concat_bigarray : ('a, 'b) ba t -> ('a, 'b) ba t -> ('a, 'b) ba t

val get_array : 'a array t -> int -> 'a
(** [Rope.get_* s i] returns the element at index [i] of rope [s]. *)

val get_bigarray : ('a, 'b) ba t -> int -> 'a

val set_array : 'a array t -> int -> 'a -> 'a array t
(** [Rope.set_* s i v] returns a new rope representing the result of setting
    the value of [s] at index [i] to [v]. *)

val set_bigarray : ('a, 'b) ba t -> int -> 'a -> ('a, 'b) ba t

val cons_array : 'a -> 'a array t -> 'a array t
(** [Rope.cons_* v s] returns a new rope representing the result of prepending
    [v] to [s]. *)

val cons_bigarray : 'a -> ('a, 'b) ba t -> ('a, 'b) ba t

val snoc_array : 'a array t -> 'a -> 'a array t
(** [Rope.snoc_* s v] returns a new rope representing the result of appending
    [v] to the end of [s]. *)

val snoc_bigarray : ('a, 'b) ba t -> 'a -> ('a, 'b) ba t

val split_at_array : 'a array t -> int -> 'a array t * 'a array t
(** [Rope.split_at_* s i] returns a pair of ropes representing the intervals
    0..i and i..n of [s], where n is the length of [s]. *)

val split_at_bigarray : ('a, 'b) ba t -> int -> ('a, 'b) ba t * ('a, 'b) ba t

val sub_array : 'a array t -> int -> int -> 'a array t
(** [Rope.sub_* s off cnt] returns a sub-rope representing the interval
    off..off+x of [s], where x is the minimum of the length of [s] minus [off]
    and [cnt]. *)

val sub_bigarray : ('a, 'b) ba t -> int -> int -> ('a, 'b) ba t

val iter_array : ('a -> unit) -> 'a array t -> unit
(** [Rope.iter_* f s] applies [f] to all elements in [s]. This function
    collapses [s].*)

val iter_bigarray : ('a -> unit) -> ('a, 'b) ba t -> unit

val iteri_array : (int -> 'a -> unit) -> 'a array t -> unit
(** [Rope.iteri_* f s] same as [Rope.iter_*] but [f] takes the index of the
    element as its first argument and the element as its second element. This
    function collapses [s] *)

val iteri_bigarray : (int -> 'a -> unit) -> ('a, 'b) ba t -> unit

val map_array_array : ('a -> 'b) -> 'a array t -> 'b array t
(** [Rope.map_*_* f s] returns a rope representing the result of applying a
    function [f] on all elements of [s]. This function collapses [s]. *)

val map_array_bigarray :
  ('b, 'c) kind -> ('a -> 'b) -> 'a array t -> ('b, 'c) ba t

val map_bigarray_array : ('a -> 'b) -> ('a, 'c) ba t -> 'b array t

val map_bigarray_bigarray :
  ('b, 'd) kind -> ('a -> 'b) -> ('a, 'c) ba t -> ('b, 'd) ba t

val mapi_array_array : (int -> 'a -> 'b) -> 'a array t -> 'b array t
(** [Rope.mapi_*_* f s] is the same as [Rope.map_*_* f s], but the function [f]
   is applied to the index of the element as its first element, and the element
   as its second argument. This function collapses [s]. *)

val mapi_array_bigarray :
  ('b, 'c) kind -> (int -> 'a -> 'b) -> 'a array t -> ('b, 'c) ba t

val mapi_bigarray_array : (int -> 'a -> 'b) -> ('a, 'c) ba t -> 'b array t

val mapi_bigarray_bigarray :
  ('b, 'd) kind -> (int -> 'a -> 'b) -> ('a, 'c) ba t -> ('b, 'd) ba t

val foldl_array : ('a -> 'b -> 'a) -> 'a -> 'b array t -> 'a
(** [Rope.foldl_* f acc s] returns the result of applying [f] on the
    accumulated value, which is initially [acc] and the elements of [s],
    starting from the leftmost element. This function collapses [s]. *)

val foldl_bigarray : ('a -> 'b -> 'a) -> 'a -> ('b, 'c) ba t -> 'a

val reverse_array : 'a array t -> 'a array t
(** [Rope.reverse_* s] returns a new rope containing the elements of [s] in
    reversed order. This function collapses [s]. *)

val reverse_bigarray : ('a, 'b) ba t -> ('a, 'b) ba t

val combine_array_array : 'a array t -> 'b array t -> ('a * 'b) array t
(** [Rope.combine_*_* l r] returns a new rope where each element is a pair
    such that the left value represents the corresponding element in [l] and
    the right value represents the corresponding element in [r]. This function
    collapses [l] and [r]. Raises exception [Invalid_argument "Rope.combine"]
    if the lengths of [l] and [r] are not equal. *)

val combine_array_bigarray : 'a array t -> ('b, 'c) ba t -> ('a * 'b) array t

val combine_bigarray_array : ('a, 'c) ba t -> 'b array t -> ('a * 'b) array t

val combine_bigarray_bigarray :
  ('a, 'c) ba t -> ('b, 'd) ba t -> ('a * 'b) array t

val equal_array : ('a -> 'a -> bool) -> 'a array t -> 'a array t -> bool
(** [Rope.equal_* f l r] returns true if [l] and [r] have the same lengths and
    all their elements are equal according to the comparison function [f]. This
    function collapses [l] and [r]. *)

val equal_bigarray :
  ('a -> 'a -> bool) -> ('a, 'b) ba t -> ('a, 'b) ba t -> bool

val foldr_array : ('a -> 'b -> 'b) -> 'a array t -> 'b -> 'b
(** [Rope.foldr_* f s acc] returns the result of applying [f] on the
    accumulated value, initially [acc], and the elements of [s], starting from
    the rightmost element. This function collapses [s]. *)

val foldr_bigarray : ('a -> 'b -> 'b) -> ('a, 'c) ba t -> 'b -> 'b

val foldr2_array :
  ('a -> 'b -> 'c -> 'c) -> 'a array t -> 'b array t -> 'c -> 'c
(** [Rope.foldr2_* f l r acc] returns the result of applying [f] on an
    accumulated value and the elements of two ropes [l] and [r], starting from
    the rightmost element. This function collapses [l] and [r]. Raises
    exception [Invalid_argument "Rope.foldr2"] if the lengths of [l] and [r]
    are not equal. *)

val foldr2_bigarray :
  ('a -> 'b -> 'c -> 'c) -> ('a, 'd) ba t -> ('b, 'e) ba t -> 'c -> 'c

module Convert : sig
  val to_array_array : 'a array t -> 'a array
  (** [Rope.Convert.to_array_* s] converts the rope [s] into an array. This
      function collapses [s]. *)

  val to_array_bigarray : ('a, 'b) ba t -> 'a array

  val of_array_array : 'a array -> 'a array t
  (** [Rope.Convert.of_array_* a] converts the array [a] into a rope. The
      underlying data is a reference to [a] so no copying is performed. *)

  val of_array_int_bigarray : int array -> int_ba t

  val of_array_float_bigarray : float array -> float_ba t

  val to_list_array : 'a array t -> 'a list
  (** [Rope.Convert.to_list_* s] converts the rope [s] into a list. This
      function collapses [s]. *)

  val to_list_bigarray : ('a, 'b) ba t -> 'a list

  val of_list_array : 'a list -> 'a array t
  (** [Rope.Convert.of_list_* l] converts the list [l] into a rope. *)

  val of_list_int_bigarray : int list -> int_ba t

  val of_list_float_bigarray : float list -> float_ba t

  val to_ustring_array : int array t -> ustring
  (** [Rope.Convert.to_ustring_* s] converts a rope of integers [s] into a
      ustring. This function collapses [s]. *)

  val to_ustring_bigarray : int_ba t -> ustring

  val of_ustring_array : ustring -> int array t
  (** [Rope.Convert.of_ustring_* u] converts the ustring [u] into a rope of
      integers. *)

  val of_ustring_bigarray : ustring -> int_ba t

  val to_int_bigarray_array : int array t -> int_ba
  (** [Rope.Convert.to_int_bigarray_* s] converts the rope of integers [s] into
      a Bigarray of integers. This function collapses [s]. *)

  val to_int_bigarray_bigarray : int_ba t -> int_ba

  val to_float_bigarray_array : float array t -> float_ba
  (** [Rope.Convert.to_int_bigarray_* s] converts the rope of floats [s] into
      a Bigarray of floats. This function collapses [s]. *)

  val to_float_bigarray_bigarray : float_ba t -> float_ba
end
