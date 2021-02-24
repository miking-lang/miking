module A = struct
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
    let make v = Atomic.make v

    let get = Atomic.get

    let set = Atomic.set

    let exchange = Atomic.exchange

    let compare_and_set = Atomic.compare_and_set
  end
end

module ParThread = struct
  type 'a t = 'a Domain.t

  type id = Domain.id

  let spawn f = Domain.spawn f

  let join p = Domain.join p

  let id p = Domain.get_id p

  let id_to_int (id : id) = (id :> int)

  let self () = Domain.self ()

  let wait () = Domain.Sync.wait ()

  let notify p = Domain.Sync.notify p

  let critical_section f = Domain.Sync.critical_section f

  let cpu_relax () = Domain.Sync.cpu_relax ()
end
