let mapf n = Rope.map_array_array (( + ) 1) (Rope.create_array n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> mapf Map_n.n)
