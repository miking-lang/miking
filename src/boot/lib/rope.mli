open Ustring.Op

type kind

type 'a t

val make : int -> 'a -> 'a t

val empty : 'a t

val length : 'a t -> int

val concat : 'a t -> 'a t -> 'a t

val get : 'a t -> int -> 'a

val set : 'a t -> int -> 'a -> 'a t

val cons : 'a -> 'a t -> 'a t

val snoc : 'a t -> 'a -> 'a t

val split_at : 'a t -> int -> 'a t * 'a t

val sub : 'a t -> int -> int -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val foldl : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

val reverse : 'a t -> 'a t

val combine : 'a t -> 'b t -> ('a * 'b) t

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val foldr : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val foldr2 : ('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c

module Convert : sig
  val to_array : 'a t -> 'a array

  val of_array : 'a array -> 'a t

  val to_list : 'a t -> 'a list

  val of_list : 'a list -> 'a t

  val to_ustring : int t -> ustring

  val of_ustring : ustring -> int t
end
