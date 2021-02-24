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

    val compare_and_set : 'a Atomic.t -> 'a -> 'a -> bool
  end
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
