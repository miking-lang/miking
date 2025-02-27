open Owl

let n = 100

let mat1 = Mat.empty n n
let mat2 = Mat.empty n n
let acc = ref 0.

let benchmark () =
  Benchmarkcommon.repeat (fun () ->
      let open Mat in
      mat1.%{Random.int n, Random.int n} <- Random.float 1.;
      mat2.%{Random.int n, Random.int n} <- Random.float 1.;
      let mat3 = mat1 *@ mat2 in
      acc := !acc +. mat3.%{Random.int n, Random.int n});
  print_float !acc

let _ = benchmark ()
