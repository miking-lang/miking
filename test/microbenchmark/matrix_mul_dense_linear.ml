type mat = float array * int * int

let mat_mul (mat1 : mat) (mat2 : mat) (mat3 : mat) : unit =
  let mat1, m1, n1 = mat1 and mat2, m2, n2 = mat2 and mat3, m3, n3 = mat3 in
  if n1 = m2 && m1 = m3 && n2 = n3 then (
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        mat3.((n3 * i) + j) <- 0.
      done
    done ;
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        for k = 0 to m1 - 1 do
          mat3.((n3 * i) + j) <-
            mat3.((n3 * i) + j) +. (mat1.((n1 * k) + j) *. mat2.((n2 * i) + k))
        done
      done
    done )
  else failwith "Invalid input"

let _ =
  let from_matrix mat =
    let m = Array.length mat and n = Array.length mat.(0) in
    let a = Array.make (n * m) 0. in
    for i = 0 to m - 1 do
      for j = 0 to n - 1 do
        a.((n * i) + j) <- mat.(i).(j)
      done
    done ;
    (a, m, n)
  in
  (* Benchmark *)
  Matrix_mul_common.benchmark from_matrix
    (fun (arr, _, n) i j -> arr.((n * i) + j))
    (fun (arr, _, n) i j v -> arr.((n * i) + j) <- v)
    mat_mul ()

(* Test *)
(* Matrix_mul_common.test (fun mat1 mat2 mat3 -> *)
(*     let open Bigarray in *)
(*     mat_mul (fun mat1 mat2 mat3 -> *)
(*         (from_matrix mat1) (from_matrix mat2) (from_matrix mat3) ) ) *)
(*
      Expected:
      15., 18., 21.,
      42., 54., 66.,
      69., 90., 111.,
*)
