open Ustring.Op

module Mseq : sig
  type 'a t

  val create : int -> (int -> 'a) -> 'a t

  val empty : 'a t

  val length : 'a t -> int

  val concat : 'a t -> 'a t -> 'a t

  val get : 'a t -> int -> 'a

  val set : 'a t -> int -> 'a -> 'a t

  val cons : 'a -> 'a t -> 'a t

  val snoc : 'a t -> 'a -> 'a t

  val reverse : 'a t -> 'a t

  val split_at : 'a t -> int -> 'a t * 'a t

  val subsequence : 'a t -> int -> int -> 'a t

  module Helpers : sig
    val of_list : 'a list -> 'a t

    val to_list : 'a t -> 'a list

    val of_array : 'a array -> 'a t

    val to_array : 'a t -> 'a array

    val of_ustring : ustring -> int t

    val to_ustring : int t -> ustring

    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

    val map : ('a -> 'b) -> 'a t -> 'b t

    val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

    val combine : 'a t -> 'b t -> ('a * 'b) t

    val fold_right2 :
      ('a -> 'b -> 'acc -> 'acc) -> 'a t -> 'b t -> 'acc -> 'acc
  end
end

module T : sig
  type 'a t =
    | Int of (int, Tensor.Num.int_elt) Tensor.Num.t
    | Float of (float, Tensor.Num.float_elt) Tensor.Num.t
    | NoNum of 'a Tensor.NoNum.t

  val int : (int, Tensor.Num.int_elt) Tensor.Num.t -> 'a t

  val float : (float, Tensor.Num.float_elt) Tensor.Num.t -> 'a t

  val no_num : 'a Tensor.NoNum.t -> 'a t
end

module Symb : sig
  type t

  val gensym : unit -> t

  val eqsym : t -> t -> bool

  val hash : t -> int

  module Helpers : sig
    val nosym : t

    val ustring_of_sym : t -> ustring

    val string_of_sym : t -> string
  end
end

module File : sig
  val read : ustring -> ustring

  val write : ustring -> ustring -> unit

  val exists : ustring -> bool

  val delete : ustring -> unit
end

module FloatConversion : sig
  val floorfi : float -> int

  val ceilfi : float -> int

  val roundfi : float -> int

  val string2float : ustring -> float
end
