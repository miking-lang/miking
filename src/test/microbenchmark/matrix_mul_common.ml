let n = 10

let create_benchmark_data () =
  let mat1 =
    Array.init n (fun _ ->
        Array.init n (fun _ -> float_of_int (Random.int 10)) )
  in
  let mat2 = Array.init n (fun i -> Array.copy mat1.(i)) in
  let mat3 = Array.init n (fun i -> Array.copy mat1.(i)) in
  (mat1, mat2, mat3)

let benchmark mat_to_mat get set mat_mul () =
  let mat1, mat2, mat3 = create_benchmark_data () in
  let mat1, mat2, mat3 = (mat_to_mat mat1, mat_to_mat mat2, mat_to_mat mat2) in
  let n = pred n in
  let random_set mat _ =
    set mat (Random.int n) (Random.int n) (float_of_int (Random.int 10))
  in
  let random_get mat _ = get mat (Random.int n) (Random.int n) in
  let sum = ref 0. in
  Benchmarkcommon.repeat (fun () ->
      random_set mat1 () ;
      random_set mat2 () ;
      mat_mul mat1 mat2 mat3 ;
      sum := !sum +. random_get mat3 () ) ;
  print_float !sum

let test_mat = [|[|0.; 1.; 2.|]; [|3.; 4.; 5.|]; [|6.; 7.; 8.|]|]

let test_array mat_mul =
  let n = Array.length test_mat in
  let mat1 = Array.copy test_mat in
  let mat2 = Array.init n (fun i -> Array.copy mat1.(i)) in
  let mat3 = Array.make_matrix n n 0. in
  mat_mul mat1 mat2 mat3 ;
  for i = 0 to Array.length mat3 - 1 do
    for j = 0 to Array.length mat3.(0) - 1 do
      print_float mat3.(i).(j) ;
      print_string ", "
    done ;
    print_newline ()
  done

let test_bigarray mat_mul =
  let open Bigarray in
  let n = Array.length test_mat in
  let mat1 = Array2.of_array Float64 C_layout test_mat in
  let mat2 = Array2.of_array Float64 C_layout test_mat in
  let mat3 = Array2.create Float64 C_layout n n in
  mat_mul mat1 mat2 mat3 ;
  for i = 0 to Array2.dim1 mat3 - 1 do
    for j = 0 to Array2.dim2 mat3 - 1 do
      print_float mat3.{i, j} ;
      print_string ", "
    done ;
    print_newline ()
  done
