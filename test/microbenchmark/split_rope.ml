let rec sum acc s =
  if Rope.length_array s == 0 then acc
  else
    let h = Rope.get_array s 0 in
    let t = Rope.sub_array s 1 (Rope.length_array s) in
    sum (acc + h) t

let s = Rope.create_array 1000 (fun i -> i)

let _ = Benchmarkcommon.repeat (fun () -> sum 0 s)
