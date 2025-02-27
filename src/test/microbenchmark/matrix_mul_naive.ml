let mat_mul mat1 mat2 mat3 =
    for i = 0 to Bigarray.Array2.dim1 mat3 - 1 do
      for j = 0 to Bigarray.Array2.dim2 mat3 - 1 do
        mat3.{i, j} <- 0.
      done
    done ;
    for i = 0 to Bigarray.Array2.dim1 mat3 - 1 do
      for j = 0 to Bigarray.Array2.dim2 mat3 - 1 do
        for k = 0 to Bigarray.Array2.dim1 mat1 - 1 do
          mat3.{i, j} <- mat3.{i, j} +. mat1.{k, j} *. mat2.{i, k}
        done
      done
    done

let n = 100

let mat1 = Bigarray.Array2.create Bigarray.float64 Bigarray.c_layout n n
let mat2 = Bigarray.Array2.create Bigarray.float64 Bigarray.c_layout n n
let mat3 = Bigarray.Array2.create Bigarray.float64 Bigarray.c_layout n n
let acc = ref 0.

let benchmark () =
  Benchmarkcommon.repeat (fun () ->
      mat1.{Random.int n, Random.int n} <- Random.float 1.;
      mat2.{Random.int n, Random.int n} <- Random.float 1.;
      mat_mul mat1 mat2 mat3;
      acc := !acc +. mat3.{Random.int n, Random.int n});
  print_float !acc

let _ = benchmark ()
