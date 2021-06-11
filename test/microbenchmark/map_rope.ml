let mapf n =
  Rope.map_array_array (( + ) 1) (Rope.create_array Map.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> mapf)
