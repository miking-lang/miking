let mat_mul mat1 mat2 mat3 : unit =
  let open Bigarray.Genarray in
  match (dims mat1, dims mat2, dims mat3) with
  | [|m1; n1|], [|m2; n2|], [|m3; n3|] when n1 = m2 && m1 = m3 && n2 = n3 ->
      for i = 0 to m3 - 1 do
        for j = 0 to n3 - 1 do
          set mat3 [|i; j|] 0.
        done
      done ;
      for i = 0 to m3 - 1 do
        for j = 0 to n3 - 1 do
          for k = 0 to m1 - 1 do
            set mat3 [|i; j|]
              (get mat3 [|i; j|] +. (get mat1 [|k; j|] *. get mat2 [|i; k|]))
          done
        done
      done
  | _ ->
      failwith "Invalid input"

let _ =
  let open Bigarray in
  (* Benchmark *)
  Matrix_mul_common.benchmark
    (fun arr -> genarray_of_array2 (Array2.of_array Float64 C_layout arr))
    (fun mat i j -> Genarray.get mat [|i; j|])
    (fun mat i j v -> Genarray.set mat [|i; j|] v)
    mat_mul ()

(* Test *)
(* Matrix_mul_common.test_bigarray (fun mat1 mat2 mat3 -> *)
(*     mat_mul (genarray_of_array2 mat1) (genarray_of_array2 mat2) *)
(*       (genarray_of_array2 mat3) ) *)
(*
      Expected:
      15., 18., 21.,
      42., 54., 66.,
      69., 90., 111.,
*)
