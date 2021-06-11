let iterf n =
  Rope.iter_array (fun _ -> ()) (Rope.create_array Iter.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> iterf)
