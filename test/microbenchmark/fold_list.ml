let foldf n = List.fold_left ( + ) 0 (List.init Fold.n (fun i -> i))

let _ = Benchmarkcommon.repeat (fun () -> foldf)
