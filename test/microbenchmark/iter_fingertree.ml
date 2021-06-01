let iterf n =
  BatFingerTree.iter
    (fun _ -> ())
    (BatFingerTree.of_list (List.init Iter.n (fun i -> i)))

let _ = Benchmarkcommon.repeat (fun () -> iterf)
