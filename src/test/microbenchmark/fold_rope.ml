let foldf n = Rope.foldl_array ( + ) 0 (Rope.create_array n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> foldf Fold.n)
