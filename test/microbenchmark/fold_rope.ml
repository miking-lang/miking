let foldf n = Rope.foldl_array ( + ) 0 (Rope.create_array Fold.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> foldf)
