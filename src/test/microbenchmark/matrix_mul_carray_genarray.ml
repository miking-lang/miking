open Bigarray

let mat_mul mat1 mat2 mat3 : unit =
  let m1, n1, mat1 = mat1 and m2, n2, mat2 = mat2 and m3, n3, mat3 = mat3 in
  if n1 = m2 && m1 = m3 && n2 = n3 then (
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        Genarray.set mat3 [|i; j|] 0.
      done
    done ;
    for i = 0 to m3 - 1 do
      for j = 0 to n3 - 1 do
        for k = 0 to m1 - 1 do
          Genarray.set mat3 [|i; j|]
            (Genarray.get mat3 [|i; j|] +.
               (Genarray.get mat1 [|k; j|] *. Genarray.get mat2 [|i; k|]))
        done
      done
    done )
  else failwith "Invalid input"

let n = 100

let mat1 = (n, n, Genarray.create float64 c_layout [|n; n|])
let mat2 = (n, n, Genarray.create float64 c_layout [|n; n|])
let mat3 = (n, n, Genarray.create float64 c_layout [|n; n|])
let acc = ref 0.

let benchmark () =
  let (_,_,a1) = mat1 in
  let (_,_,a2) = mat2 in
  let (_,_,a3) = mat3 in
  Benchmarkcommon.repeat (fun () ->
      Genarray.set a1 [|Random.int n; Random.int n|] (Random.float 1.);
      Genarray.set a2 [|Random.int n; Random.int n|] (Random.float 1.);
      mat_mul mat1 mat2 mat3;
      acc := !acc +. (Genarray.get a3 [|Random.int n; Random.int n|]));
  print_float !acc

let _ = benchmark ()
