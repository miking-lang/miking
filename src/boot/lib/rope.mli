open Bigarray
open Ustring.Op

type ('a, 'b) ba = ('a, 'b, c_layout) Array1.t

type int_ba = (int, int_elt) ba

type float_ba = (float, float64_elt) ba

type 'a t

val make_array : int -> 'a -> 'a array t

val make_int_bigarray : int -> int -> (int, int_elt) ba t

val make_float_bigarray : int -> float -> (float, float64_elt) ba t

val empty_array : 'a array t

val empty_bigarray : ('a, 'b) kind -> ('a, 'b) ba t

val length_array : 'a array t -> int

val length_bigarray : ('a, 'b) ba t -> int

val concat_array : 'a array t -> 'a array t -> 'a array t

val concat_bigarray : ('a, 'b) ba t -> ('a, 'b) ba t -> ('a, 'b) ba t

val get_array : 'a array t -> int -> 'a

val get_bigarray : ('a, 'b) ba t -> int -> 'a

val set_array : 'a array t -> int -> 'a -> 'a array t

val set_bigarray : ('a, 'b) ba t -> int -> 'a -> ('a, 'b) ba t

val cons_array : 'a -> 'a array t -> 'a array t

val cons_bigarray : 'a -> ('a, 'b) ba t -> ('a, 'b) ba t

val snoc_array : 'a array t -> 'a -> 'a array t

val snoc_bigarray : ('a, 'b) ba t -> 'a -> ('a, 'b) ba t

val split_at_array : 'a array t -> int -> 'a array t * 'a array t

val split_at_bigarray : ('a, 'b) ba t -> int -> ('a, 'b) ba t * ('a, 'b) ba t

val sub_array : 'a array t -> int -> int -> 'a array t

val sub_bigarray : ('a, 'b) ba t -> int -> int -> ('a, 'b) ba t

val map_array_array : ('a -> 'b) -> 'a array t -> 'b array t

val map_array_bigarray :
  ('b, 'c) kind -> ('a -> 'b) -> 'a array t -> ('b, 'c) ba t

val map_bigarray_array : ('a -> 'b) -> ('a, 'c) ba t -> 'b array t

val map_bigarray_bigarray :
  ('b, 'd) kind -> ('a -> 'b) -> ('a, 'c) ba t -> ('b, 'd) ba t

val foldl_array : ('a -> 'b -> 'a) -> 'a -> 'b array t -> 'a

val foldl_bigarray : ('a -> 'b -> 'a) -> 'a -> ('b, 'c) ba t -> 'a

val reverse_array : 'a array t -> 'a array t

val reverse_bigarray : ('a, 'b) ba t -> ('a, 'b) ba t

val combine_array_array : 'a array t -> 'b array t -> ('a * 'b) array t

val combine_array_bigarray : 'a array t -> ('b, 'c) ba t -> ('a * 'b) array t

val combine_bigarray_array : ('a, 'c) ba t -> 'b array t -> ('a * 'b) array t

val combine_bigarray_bigarray :
  ('a, 'c) ba t -> ('b, 'd) ba t -> ('a * 'b) array t

val equal_array : ('a -> 'a -> bool) -> 'a array t -> 'a array t -> bool

val equal_bigarray :
  ('a -> 'a -> bool) -> ('a, 'b) ba t -> ('a, 'b) ba t -> bool

val foldr_array : ('a -> 'b -> 'b) -> 'a array t -> 'b -> 'b

val foldr_bigarray : ('a -> 'b -> 'b) -> ('a, 'c) ba t -> 'b -> 'b

val foldr2_array :
  ('a -> 'b -> 'c -> 'c) -> 'a array t -> 'b array t -> 'c -> 'c

val foldr2_bigarray :
  ('a -> 'b -> 'c -> 'c) -> ('a, 'd) ba t -> ('b, 'e) ba t -> 'c -> 'c

module Convert : sig
  val to_array_array : 'a array t -> 'a array

  val to_array_bigarray : ('a, 'b) ba t -> 'a array

  val of_array_array : 'a array -> 'a array t

  val of_int_array : int array -> int_ba t

  val of_float_array : float array -> float_ba t

  val to_list_array : 'a array t -> 'a list

  val to_list_bigarray : ('a, 'b) ba t -> 'a list

  val of_list_array : 'a list -> 'a array t

  val of_int_list : int list -> int_ba t

  val of_float_list : float list -> float_ba t

  val to_ustring_array : int array t -> ustring

  val to_ustring_bigarray : int_ba t -> ustring

  val of_ustring_array : ustring -> int array t

  val of_ustring_bigarray : ustring -> int_ba t
end
