let mapf n =
  BatFingerTree.map (( + ) 1)
    (BatFingerTree.of_list (List.init Map.n (fun i -> i)))

let _ = Benchmarkcommon.repeat (fun () -> mapf)
