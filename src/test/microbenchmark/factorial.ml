let rec fact n = if n = 0 then 1 else n * fact (n - 1)

let _ = Benchmarkcommon.repeat (fun () -> fact 100)

(* let _ = Printf.printf "%d\n" (fact 8)  *)
