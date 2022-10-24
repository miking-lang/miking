open Ustring

module type TENSOR = sig
  type ('a, 'b) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val linear_get_exn : ('a, 'b) t -> int -> 'a

  val linear_set_exn : ('a, 'b) t -> int -> 'a -> unit

  val shape : ('a, 'b) t -> int array

  val rank : ('a, 'b) t -> int

  val size : ('a, 'b) t -> int

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val copy : ('a, 'b) t -> ('a, 'b) t

  val transpose_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t
end

module type GENERIC = sig
  include TENSOR

  val create : int array -> (int array -> 'a) -> ('a, 'b) t
end

module type BARRAY = sig
  include TENSOR

  val uninit_int : int array -> (int, Bigarray.int_elt) t

  val uninit_float : int array -> (float, Bigarray.float64_elt) t

  val create_int : int array -> (int array -> int) -> (int, Bigarray.int_elt) t

  val create_float :
    int array -> (int array -> float) -> (float, Bigarray.float64_elt) t

  val to_genarray_clayout :
    ('a, 'b) t -> ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t

  val of_genarray_clayout :
    ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t -> ('a, 'b) t
end

module type UOP = sig
  type ('a, 'b) t

  val iter_slice : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val to_data_array : ('a, 'b) t -> 'a array

  val to_ustring : ('a -> ustring) -> ('a, 'b) t -> ustring
end

module type BOP = sig
  type ('a, 'b) t1

  type ('c, 'd) t2

  val equal : ('a -> 'c -> bool) -> ('a, 'b) t1 -> ('c, 'd) t2 -> bool
end

module Generic : GENERIC

module Barray : BARRAY

module Uop (T : TENSOR) : UOP with type ('a, 'b) t = ('a, 'b) T.t

module Bop (T1 : TENSOR) (T2 : TENSOR) :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) T1.t
     and type ('c, 'd) t2 = ('c, 'd) T2.t

module Uop_generic : UOP with type ('a, 'b) t = ('a, 'b) Generic.t

module Uop_barray : UOP with type ('a, 'b) t = ('a, 'b) Barray.t

module Bop_generic_generic :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) Generic.t
     and type ('c, 'd) t2 = ('c, 'd) Generic.t

module Bop_barray_barray :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) Barray.t
     and type ('c, 'd) t2 = ('c, 'd) Barray.t

module Bop_generic_barray :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) Generic.t
     and type ('c, 'd) t2 = ('c, 'd) Barray.t

module Bop_barray_generic :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) Barray.t
     and type ('c, 'd) t2 = ('c, 'd) Generic.t
