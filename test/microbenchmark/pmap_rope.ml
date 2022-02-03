let workload = 20

let rec fibonacci n = if n < 3 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let mapf n =
  Rope.map_array_array
    (fun _ -> fibonacci workload)
    (Rope.create_array n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> mapf Map_n.n)
