type ('a, 'b) tensor_ops =
  { rank: 'a -> int
  ; shape: 'a -> int array
  ; size: 'a -> int
  ; get_exn: 'a -> int array -> 'b
  ; set_exn: 'a -> int array -> 'b -> unit
  ; reshape_exn: 'a -> int array -> 'a
  ; slice_exn: 'a -> int array -> 'a }

val blit : ('a, 'b) tensor_ops -> ('c, 'b) tensor_ops -> 'a -> 'c -> unit

val equal :
     ('a, 'b) tensor_ops
  -> ('c, 'd) tensor_ops
  -> ('b -> 'd -> bool)
  -> 'a
  -> 'c
  -> bool

module CArray : sig
  type ('a, 'b) t = ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t

  type float_elt = Bigarray.float64_elt

  type int_elt = Bigarray.int_elt

  val create_int : int array -> (int array -> int) -> (int, int_elt) t

  val create_float : int array -> (int array -> float) -> (float, float_elt) t

  val transpose_int_exn : (int, int_elt) t -> int -> int -> (int, int_elt) t

  val transpose_float_exn :
    (float, float_elt) t -> int -> int -> (float, float_elt) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val rank : ('a, 'b) t -> int

  val shape : ('a, 'b) t -> int array

  val size : ('a, 'b) t -> int

  val blit_exn : ('a, 'b) t -> ('a, 'b) t -> unit

  val copy : ('a, 'b) t -> ('a, 'b) t

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val iter_slice : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val equal : ('a -> 'b -> bool) -> ('a, 'c) t -> ('b, 'd) t -> bool

  val data_to_array : ('a, 'b) t -> 'a array

  val ops : (('a, 'b) t, 'a) tensor_ops
end

module Dense : sig
  type 'a t

  val create : int array -> (int array -> 'a) -> 'a t

  val get_exn : 'a t -> int array -> 'a

  val set_exn : 'a t -> int array -> 'a -> unit

  val rank : 'a t -> int

  val shape : 'a t -> int array

  val size : 'a t -> int

  val blit_exn : 'a t -> 'a t -> unit

  val copy : 'a t -> 'a t

  val transpose_exn : 'a t -> int -> int -> 'a t

  val reshape_exn : 'a t -> int array -> 'a t

  val slice_exn : 'a t -> int array -> 'a t

  val sub_exn : 'a t -> int -> int -> 'a t

  val iter_slice : (int -> 'a t -> unit) -> 'a t -> unit

  val equal : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

  val of_array : 'a array -> 'a t

  val data_to_array : 'a t -> 'a array

  val ops : ('a t, 'a) tensor_ops
end
