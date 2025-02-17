let iterf n = List.iter (fun _ -> ()) (List.init Iter.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> iterf)
