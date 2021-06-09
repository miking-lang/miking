module CArray : sig
  type ('a, 'b) t = ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t

  type float_elt = Bigarray.float64_elt

  type int_elt = Bigarray.int_elt

  val create_int : int array -> (int array -> int) -> (int, int_elt) t

  val create_float : int array -> (int array -> float) -> (float, float_elt) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val rank : ('a, 'b) t -> int

  val shape : ('a, 'b) t -> int array

  val copy_exn : ('a, 'b) t -> ('a, 'b) t -> unit

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val iter_slice : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val data_to_array : ('a, 'b) t -> 'a array
end

module Dense : sig
  type 'a t

  val create : int array -> (int array -> 'a) -> 'a t

  val get_exn : 'a t -> int array -> 'a

  val set_exn : 'a t -> int array -> 'a -> unit

  val rank : 'a t -> int

  val shape : 'a t -> int array

  val size : 'a t -> int

  val copy_exn : 'a t -> 'a t -> unit

  val reshape_exn : 'a t -> int array -> 'a t

  val slice_exn : 'a t -> int array -> 'a t

  val sub_exn : 'a t -> int -> int -> 'a t

  val iter_slice : (int -> 'a t -> unit) -> 'a t -> unit

  val equal : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

  val of_array : 'a array -> 'a t

  val data_to_array : 'a t -> 'a array
end

val copy_num_nonum_exn : ('a, 'b) CArray.t -> 'a Dense.t -> unit

val copy_nonum_num_exn : 'a Dense.t -> ('a, 'b) CArray.t -> unit
