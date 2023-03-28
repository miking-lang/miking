let foldf n = List.fold_left ( + ) 0 (List.init n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> foldf Fold.n)
