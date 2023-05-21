let mat_mul (mat1 : float array array) (mat2 : float array array)
    (mat3 : float array array) : unit =
  let open Array in
  let m1 = length mat1
  and n1 = length mat1.(0)
  and m2 = length mat2
  and n2 = length mat2.(0)
  and m3 = length mat3
  and n3 = length mat3.(0) in
  if n1 = m2 && m1 = m3 && n2 = n3 then (
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        mat3.(i).(j) <- 0.
      done
    done ;
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        for k = 0 to m1 - 1 do
          mat3.(i).(j) <- mat3.(i).(j) +. (mat1.(k).(j) *. mat2.(i).(k))
        done
      done
    done )
  else failwith "Invalid input"

let _ =
  (* Benchmark *)
  Matrix_mul_common.benchmark Fun.id
    (fun mat i j -> mat.(i).(j))
    (fun mat i j v -> mat.(i).(j) <- v)
    mat_mul ()

(* Test *)
(* Matrix_mul_common.test_array mat_mul *)
(*
      Expected:
      15., 18., 21.,
      42., 54., 66.,
      69., 90., 111.,
*)
