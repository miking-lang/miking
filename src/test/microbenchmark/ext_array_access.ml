let n = 10000
let a = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout n

let bm () =
  a.{Random.int n} <- Random.float (Float.of_int n);
  for i = 0 to n - 2 do
    a.{i} <- a.{i + 1}
  done;
  print_float a.{Random.int n}

let _ = Benchmarkcommon.repeat bm
