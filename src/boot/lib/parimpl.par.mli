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
