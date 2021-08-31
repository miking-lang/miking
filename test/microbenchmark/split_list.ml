let rec sum acc s = match s with [] -> acc | h :: t -> sum (acc + h) t

let s = List.init 1000 (fun i -> i)

let _ = Benchmarkcommon.repeat (fun () -> sum 0 s)
