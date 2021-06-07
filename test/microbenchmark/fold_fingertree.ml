let foldf n =
  BatFingerTree.fold_left ( + ) 0
    (BatFingerTree.of_list (List.init Fold.n (fun i -> i)))

let _ = Benchmarkcommon.repeat (fun () -> foldf)
