module Atomic = struct
  type 'a t = Int : int Atomic.t -> 'a t | NoInt : 'a Atomic.t -> 'a t

  module Int = struct
    let make = Atomic.make

    let get = Atomic.get

    let set = Atomic.set

    let exchange = Atomic.exchange

    let compare_and_set = Atomic.compare_and_set

    let fetch_and_add = Atomic.fetch_and_add
  end

  module NoInt = struct
    let make = Atomic.make

    let get = Atomic.get

    let set = Atomic.set

    let exchange = Atomic.exchange
  end
end
