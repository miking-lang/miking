let mapf n = List.map (( + ) 1) (List.init n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> mapf Map_n.n)

(* let _ = List.iter print_int (mapf n) *)
