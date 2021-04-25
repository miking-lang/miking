let tensor_shape_and_index_does_not_match =
  "Tensor shape and index does not match"

let tensor_shape_mismatch = "Tensor shape mismatch"

let tensor_shape_and_ofs_and_len_does_not_match =
  "Tensor shape and ofs and len does not match"

let prod = Array.fold_left ( * ) 1

let sum = Array.fold_left ( + ) 0

let row_major_ofs shape is =
  let n = Array.length shape in
  let d = Array.length is in
  let tmp_ofs = ref 0 in
  let tmp = ref 0 in
  for k = 0 to d - 1 do
    tmp := 1 ;
    for l = k + 1 to n - 1 do
      tmp := !tmp * shape.(l)
    done ;
    tmp_ofs := !tmp_ofs + (!tmp * is.(k))
  done ;
  !tmp_ofs

let inverse_row_major_ofs shape i =
  let d = Array.length shape in
  let is = Array.make d 0 in
  let ofs = ref i in
  for k = 0 to d - 1 do
    let l = d - 1 - k in
    let n = shape.(l) in
    let j = !ofs mod n in
    is.(l) <- j ;
    ofs := !ofs / n
  done ;
  is

let mk_iteri rank shape slice f t =
  if rank t = 0 then f (-1) t
  else
    let n = (shape t).(0) in
    for i = 0 to n - 1 do
      f i (slice t [|i|])
    done

module NoNum = struct
  type 'a t =
    {data: 'a array; shape: int array; rank: int; left_ofs: int; size: int}

  let rank t = t.rank

  let shape t = t.shape

  let create shape f =
    let rank = Array.length shape in
    let size = prod shape in
    let data = Array.init size (fun i -> f (inverse_row_major_ofs shape i)) in
    let left_ofs = 0 in
    {data; rank; shape; left_ofs; size}

  let is_valid_index shape is =
    let valid = ref true in
    Array.iteri (fun i n -> valid := !valid && n >= 0 && n < shape.(i)) is ;
    !valid

  let get_exn t is =
    if Array.length is = rank t && is_valid_index t.shape is then
      let ofs = row_major_ofs t.shape is + t.left_ofs in
      t.data.(ofs)
    else raise (Invalid_argument tensor_shape_and_index_does_not_match)

  let set_exn t is v =
    if is_valid_index t.shape is then
      let ofs = row_major_ofs t.shape is + t.left_ofs in
      t.data.(ofs) <- v
    else raise (Invalid_argument tensor_shape_and_index_does_not_match)

  let copy_exn t1 t2 =
    if shape t1 = shape t2 then
      if rank t1 = 0 then t2.data.(0) <- t1.data.(0)
      else
        let o1 = t1.left_ofs in
        let o2 = t2.left_ofs in
        Array.blit t1.data o1 t2.data o2 t1.size
    else raise (Invalid_argument tensor_shape_mismatch)

  let reshape_exn t shape =
    if t.size = sum shape then
      let rank = Array.length shape in
      {t with shape; rank}
    else raise (Invalid_argument tensor_shape_mismatch)

  let slice_exn t slice =
    if Array.length slice = 0 then t
    else if is_valid_index t.shape slice then
      let n = Array.length slice in
      let left_ofs = row_major_ofs t.shape slice + t.left_ofs in
      let rank = t.rank - n in
      let shape = if rank > 0 then Array.sub t.shape n rank else [||] in
      let size = prod shape in
      {t with left_ofs; rank; shape; size}
    else raise (Invalid_argument tensor_shape_and_index_does_not_match)

  let sub_exn t ofs len =
    if t.rank > 0 && ofs >= 0 && ofs + len <= t.shape.(0) then (
      let left_ofs = row_major_ofs t.shape [|ofs|] + t.left_ofs in
      let shape = Array.copy t.shape in
      shape.(0) <- len ;
      {t with left_ofs; size= prod shape; shape} )
    else raise (Invalid_argument tensor_shape_and_ofs_and_len_does_not_match)

  let iteri f t = mk_iteri rank shape slice_exn f t

  let equal eq t1 t2 =
    if shape t1 = shape t2 then (
      let n = t1.size in
      let v1 = reshape_exn t1 [|n|] in
      let v2 = reshape_exn t2 [|n|] in
      let tmp = ref true in
      let i = ref 0 in
      while !tmp do
        tmp := eq (get_exn v1 [|!i|]) (get_exn v2 [|!i|]) ;
        incr i
      done ;
      !tmp )
    else false

  let of_array a =
    let data = Array.copy a in
    let size = Array.length a in
    let shape = [|size|] in
    let rank = 1 in
    let left_ofs = 0 in
    {data; shape; rank; left_ofs; size}

  let data_to_array t = Array.sub t.data t.left_ofs t.size
end

module Num = struct
  type float_elt = Bigarray.float64_elt

  type int_elt = Bigarray.int_elt

  type ('a, 'b) kind =
    | Float : (float, float_elt) kind
    | Int : (int, int_elt) kind

  type ('a, 'b) t = ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t

  let to_ba_kind : type a b. (a, b) kind -> (a, b) Bigarray.kind = function
    | Float ->
        Bigarray.Float64
    | Int ->
        Bigarray.Int

  let of_ba_kind : type a b. (a, b) Bigarray.kind -> (a, b) kind = function
    | Bigarray.Float64 ->
        Float
    | Bigarray.Int ->
        Int
    | _ ->
        failwith "Unsupported Bigarray.kind"

  let populate f t shape =
    let n = prod shape in
    if n = 0 then Bigarray.Genarray.set t [||] (f [||])
    else
      for ofs = 0 to n - 1 do
        let is = inverse_row_major_ofs shape ofs in
        Bigarray.Genarray.set t is (f is)
      done

  let create :
      type a b. (a, b) kind -> int array -> (int array -> a) -> (a, b) t =
    function
    | Float ->
        fun shape f ->
          let t =
            Bigarray.Genarray.create Bigarray.float64 Bigarray.c_layout shape
          in
          populate f t shape ; t
    | Int ->
        fun shape f ->
          let t =
            Bigarray.Genarray.create Bigarray.int Bigarray.c_layout shape
          in
          populate f t shape ; t

  let kind t = Bigarray.Genarray.kind t |> of_ba_kind

  let int = Int

  let float = Float

  let get_exn = Bigarray.Genarray.get

  let set_exn = Bigarray.Genarray.set

  let rank = Bigarray.Genarray.num_dims

  let shape = Bigarray.Genarray.dims

  let copy_exn = Bigarray.Genarray.blit

  let reshape_exn = Bigarray.reshape

  let slice_exn = Bigarray.Genarray.slice_left

  let sub_exn = Bigarray.Genarray.sub_left

  let iteri f t = mk_iteri rank shape slice_exn f t

  let of_array kind a =
    a
    |> Bigarray.Array1.of_array (to_ba_kind kind) Bigarray.c_layout
    |> Bigarray.genarray_of_array1

  let data_to_array t =
    let n = prod (shape t) in
    let v = reshape_exn t [|n|] in
    let a = Array.make n (get_exn v [|0|]) in
    Array.iteri (fun i _ -> a.(i) <- get_exn v [|i|]) a ;
    a
end
