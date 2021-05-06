module Num : sig
  type ('a, 'b) t

  type float_elt

  type int_elt

  type ('a, 'b) kind =
    | Float : (float, float_elt) kind
    | Int : (int, int_elt) kind

  val kind : ('a, 'b) t -> ('a, 'b) kind

  val float : (float, float_elt) kind

  val int : (int, int_elt) kind

  val create : ('a, 'b) kind -> int array -> (int array -> 'a) -> ('a, 'b) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val rank : ('a, 'b) t -> int

  val shape : ('a, 'b) t -> int array

  val copy_exn : ('a, 'b) t -> ('a, 'b) t -> unit

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val iteri : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val of_array : ('a, 'b) kind -> 'a array -> ('a, 'b) t

  val data_to_array : ('a, 'b) t -> 'a array
end

module NoNum : sig
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

  val iteri : (int -> 'a t -> unit) -> 'a t -> unit

  val equal : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

  val of_array : 'a array -> 'a t

  val data_to_array : 'a t -> 'a array
end

val copy_num_nonum_exn : ('a, 'b) Num.t -> 'a NoNum.t -> unit

val copy_nonum_num_exn : 'a NoNum.t -> ('a, 'b) Num.t -> unit
