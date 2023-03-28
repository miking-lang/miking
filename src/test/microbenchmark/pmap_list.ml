(* Using a tail-recursive sequential map *)

let workload = 20

let rec fibonacci n = if n < 3 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let mapf n =
  List.rev (List.rev_map (fun _ -> fibonacci 20) (List.init n (fun i -> i)))

let _ = Benchmarkcommon.repeat (fun () -> mapf Map_n.n)
