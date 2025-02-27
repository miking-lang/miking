let n = 10000
let a = Array.make n 0

let bm () =
  a.(Random.int n) <- Random.int n;
  for i = 0 to n - 2 do
    a.(i) <- a.(i + 1)
  done;
  print_int a.(Random.int n)

let _ = Benchmarkcommon.repeat bm
