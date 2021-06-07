let mapf n = List.map (( + ) 1) (List.init Map.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> mapf Map.n)

(* let _ = List.iter print_int (mapf n) *)
