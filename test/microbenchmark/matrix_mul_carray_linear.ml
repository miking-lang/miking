let mat_mul mat1 mat2 mat3 : unit =
  let open Bigarray.Array2 in
  let m1 = dim1 mat1
  and n1 = dim2 mat1
  and m2 = dim1 mat2
  and n2 = dim2 mat2
  and m3 = dim1 mat3
  and n3 = dim2 mat3 in
  if n1 = m2 && m1 = m3 && n2 = n3 then (
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        mat3.{i, j} <- 0.
      done
    done ;
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        for k = 0 to m1 - 1 do
          mat3.{i, j} <- mat3.{i, j} +. (mat1.{k, j} *. mat2.{i, k})
        done
      done
    done )
  else failwith "Invalid input"

let _ =
  let open Bigarray in
  (* Benchmark *)
  Matrix_mul_common.benchmark
    (Array2.of_array Float64 C_layout)
    Array2.get Array2.set mat_mul ()

(* Test *)
(* Matrix_mul_common.test_bigarray mat_mul *)
(*
      Expected:
      15., 18., 21.,
      42., 54., 66.,
      69., 90., 111.,
*)
