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

    val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc

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

  module Num : sig
    val create_int :
         int Mseq.t
      -> (int Mseq.t -> int)
      -> (int, Tensor.Num.int_elt) Tensor.Num.t

    val create_float :
         int Mseq.t
      -> (int Mseq.t -> float)
      -> (float, Tensor.Num.float_elt) Tensor.Num.t

    val get_exn : ('a, 'b) Tensor.Num.t -> int Mseq.t -> 'a

    val set_exn : ('a, 'b) Tensor.Num.t -> int Mseq.t -> 'a -> unit

    val rank : ('a, 'b) Tensor.Num.t -> int

    val shape : ('a, 'b) Tensor.Num.t -> int Mseq.t

    val copy_exn : ('a, 'b) Tensor.Num.t -> ('a, 'b) Tensor.Num.t -> unit

    val reshape_exn :
      ('a, 'b) Tensor.Num.t -> int Mseq.t -> ('a, 'b) Tensor.Num.t

    val slice_exn :
      ('a, 'b) Tensor.Num.t -> int Mseq.t -> ('a, 'b) Tensor.Num.t

    val sub_exn : ('a, 'b) Tensor.Num.t -> int -> int -> ('a, 'b) Tensor.Num.t

    val iteri :
      (int -> ('a, 'b) Tensor.Num.t -> unit) -> ('a, 'b) Tensor.Num.t -> unit
  end

  module NoNum : sig
    val create : int Mseq.t -> (int Mseq.t -> 'a) -> 'a Tensor.NoNum.t

    val get_exn : 'a Tensor.NoNum.t -> int Mseq.t -> 'a

    val set_exn : 'a Tensor.NoNum.t -> int Mseq.t -> 'a -> unit

    val rank : 'a Tensor.NoNum.t -> int

    val shape : 'a Tensor.NoNum.t -> int Mseq.t

    val copy_exn : 'a Tensor.NoNum.t -> 'a Tensor.NoNum.t -> unit

    val reshape_exn : 'a Tensor.NoNum.t -> int Mseq.t -> 'a Tensor.NoNum.t

    val slice_exn : 'a Tensor.NoNum.t -> int Mseq.t -> 'a Tensor.NoNum.t

    val sub_exn : 'a Tensor.NoNum.t -> int -> int -> 'a Tensor.NoNum.t

    val iteri : (int -> 'a Tensor.NoNum.t -> unit) -> 'a Tensor.NoNum.t -> unit
  end
end

module Symb : sig
  type t

  val gensym : unit -> t

  val eqsym : t -> t -> bool

  val hash : t -> int

  val compare : t -> t -> int

  module Helpers : sig
    val nosym : t

    val ustring_of_sym : t -> ustring

    val string_of_sym : t -> string
  end
end

module File : sig
  val read : int Mseq.t -> int Mseq.t

  val write : int Mseq.t -> int Mseq.t -> unit

  val exists : int Mseq.t -> bool

  val delete : int Mseq.t -> unit
end

module FloatConversion : sig
  val floorfi : float -> int

  val ceilfi : float -> int

  val roundfi : float -> int

  val string2float : int Mseq.t -> float
end

module IO : sig
  val print : int Mseq.t -> unit

  val dprint : int Mseq.t -> unit

  val read_line : unit -> int Mseq.t
end

module RNG : sig
  val set_seed : int -> unit

  val int_u : int -> int -> int
end

module MSys : sig
  val exit : int -> unit

  val error : int Mseq.t -> exn

  val argv : int Mseq.t Mseq.t

  val command : int Mseq.t -> int
end

module Time : sig
  val get_wall_time_ms : unit -> float

  val sleep_ms : int -> unit
end

module Mmap : sig
  val empty : ('a -> 'a -> int) -> Obj.t

  val insert : 'a -> 'b -> Obj.t -> Obj.t

  val remove : 'a -> Obj.t -> Obj.t

  val find : 'a -> Obj.t -> 'b

  val find_or_else : (unit -> 'b) -> 'a -> Obj.t -> 'b

  val find_apply_or_else : ('b -> 'c) -> (unit -> 'c) -> 'a -> Obj.t -> 'c

  val bindings : Obj.t -> ('a * 'b) Mseq.t

  val size : Obj.t -> int

  val mem : 'a -> Obj.t -> bool

  val any : ('a -> 'b -> bool) -> Obj.t -> bool

  val map : ('b -> 'c) -> Obj.t -> Obj.t

  val map_with_key : ('a -> 'b -> 'c) -> Obj.t -> Obj.t

  val fold_with_key : ('c -> 'a -> 'b -> 'c) -> 'c -> Obj.t -> 'c

  val eq : ('b -> 'b -> bool) -> Obj.t -> Obj.t -> bool

  val cmp : ('b -> 'b -> int) -> Obj.t -> Obj.t -> int

  val key_cmp : Obj.t -> 'a -> 'a -> int
end
