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
    | CArrayIntBoot of (int, Tensor.CArray.int_elt) Tensor.CArray.t
    | CArrayFloatBoot of (float, Tensor.CArray.float_elt) Tensor.CArray.t
    | DenseBoot of 'a Tensor.Dense.t

  type ('a, 'b) u =
    | TCArrayInt :
        (int, Tensor.CArray.int_elt) Tensor.CArray.t
        -> (int, Tensor.CArray.int_elt) u
    | TCArrayFloat :
        (float, Tensor.CArray.float_elt) Tensor.CArray.t
        -> (float, Tensor.CArray.float_elt) u
    | TDense : 'a Tensor.Dense.t -> ('a, 'b) u

  val carray_int :
       (int, Tensor.CArray.int_elt) Tensor.CArray.t
    -> (int, Tensor.CArray.int_elt) u

  val carray_float :
       (float, Tensor.CArray.float_elt) Tensor.CArray.t
    -> (float, Tensor.CArray.float_elt) u

  val create_carray_int :
    int Mseq.t -> (int Mseq.t -> int) -> (int, Tensor.CArray.int_elt) u

  val create_carray_float :
    int Mseq.t -> (int Mseq.t -> float) -> (float, Tensor.CArray.float_elt) u

  val create_dense : int Mseq.t -> (int Mseq.t -> 'a) -> ('a, 'a) u

  val get_exn : ('a, 'b) u -> int Mseq.t -> 'a

  val set_exn : ('a, 'b) u -> int Mseq.t -> 'a -> unit

  val rank : ('a, 'b) u -> int

  val shape : ('a, 'b) u -> int Mseq.t

  val copy_exn : ('a, 'b) u -> ('a, 'b) u -> unit

  val reshape_exn : ('a, 'b) u -> int Mseq.t -> ('a, 'b) u

  val slice_exn : ('a, 'b) u -> int Mseq.t -> ('a, 'b) u

  val sub_exn : ('a, 'b) u -> int -> int -> ('a, 'b) u

  val iteri : (int -> ('a, 'b) u -> unit) -> ('a, 'b) u -> unit

  module CArray : sig
    val create_int :
         int Mseq.t
      -> (int Mseq.t -> int)
      -> (int, Tensor.CArray.int_elt) Tensor.CArray.t

    val create_float :
         int Mseq.t
      -> (int Mseq.t -> float)
      -> (float, Tensor.CArray.float_elt) Tensor.CArray.t

    val get_exn : ('a, 'b) Tensor.CArray.t -> int Mseq.t -> 'a

    val set_exn : ('a, 'b) Tensor.CArray.t -> int Mseq.t -> 'a -> unit

    val rank : ('a, 'b) Tensor.CArray.t -> int

    val shape : ('a, 'b) Tensor.CArray.t -> int Mseq.t

    val copy_exn : ('a, 'b) Tensor.CArray.t -> ('a, 'b) Tensor.CArray.t -> unit

    val reshape_exn :
      ('a, 'b) Tensor.CArray.t -> int Mseq.t -> ('a, 'b) Tensor.CArray.t

    val slice_exn :
      ('a, 'b) Tensor.CArray.t -> int Mseq.t -> ('a, 'b) Tensor.CArray.t

    val sub_exn :
      ('a, 'b) Tensor.CArray.t -> int -> int -> ('a, 'b) Tensor.CArray.t

    val iteri :
         (int -> ('a, 'b) Tensor.CArray.t -> unit)
      -> ('a, 'b) Tensor.CArray.t
      -> unit
  end

  module Dense : sig
    val create : int Mseq.t -> (int Mseq.t -> 'a) -> 'a Tensor.Dense.t

    val get_exn : 'a Tensor.Dense.t -> int Mseq.t -> 'a

    val set_exn : 'a Tensor.Dense.t -> int Mseq.t -> 'a -> unit

    val rank : 'a Tensor.Dense.t -> int

    val shape : 'a Tensor.Dense.t -> int Mseq.t

    val copy_exn : 'a Tensor.Dense.t -> 'a Tensor.Dense.t -> unit

    val reshape_exn : 'a Tensor.Dense.t -> int Mseq.t -> 'a Tensor.Dense.t

    val slice_exn : 'a Tensor.Dense.t -> int Mseq.t -> 'a Tensor.Dense.t

    val sub_exn : 'a Tensor.Dense.t -> int -> int -> 'a Tensor.Dense.t

    val iteri : (int -> 'a Tensor.Dense.t -> unit) -> 'a Tensor.Dense.t -> unit
  end

  module Helpers : sig
    open Bigarray

    val to_genarray_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Genarray.t

    val to_array1_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Array1.t

    val to_array2_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Array2.t

    val of_array1_clayout_int :
         (int, Tensor.CArray.int_elt, c_layout) Array1.t
      -> (int, Tensor.CArray.int_elt) u

    val of_array1_clayout_float :
         (float, Tensor.CArray.float_elt, c_layout) Array1.t
      -> (float, Tensor.CArray.float_elt) u

    val of_array2_clayout_int :
         (int, Tensor.CArray.int_elt, c_layout) Array2.t
      -> (int, Tensor.CArray.int_elt) u

    val of_array2_clayout_float :
         (float, Tensor.CArray.float_elt, c_layout) Array2.t
      -> (float, Tensor.CArray.float_elt) u
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

  val float2string : float -> int Mseq.t
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

module Thread : sig
  type 'a t

  type id

  val spawn : (unit -> 'a) -> 'a t

  val join : 'a t -> 'a

  val id : 'a t -> id

  val id_to_int : id -> int

  val self : unit -> id

  val wait : unit -> unit

  val notify : id -> unit

  val critical_section : (unit -> 'a) -> 'a

  val cpu_relax : unit -> unit
end

module Atomic : sig
  type 'a t = Int : int Atomic.t -> 'a t | NoInt : 'a Atomic.t -> 'a t

  module Int : sig
    val make : int -> int Atomic.t

    val get : int Atomic.t -> int

    val set : int Atomic.t -> int -> unit

    val exchange : int Atomic.t -> int -> int

    val compare_and_set : int Atomic.t -> int -> int -> bool

    val fetch_and_add : int Atomic.t -> int -> int
  end

  module NoInt : sig
    val make : 'a -> 'a Atomic.t

    val get : 'a Atomic.t -> 'a

    val set : 'a Atomic.t -> 'a -> unit

    val exchange : 'a Atomic.t -> 'a -> 'a
  end
end
