let prod = Array.fold_left ( * ) 1

let cartesian_to_linear_idx shape idx =
  let rank = Array.length shape in
  let n = Array.length idx in
  let tmp_ofs = ref 0 in
  let tmp = ref 0 in
  for k = 0 to n - 1 do
    tmp := 1 ;
    for l = k + 1 to rank - 1 do
      tmp := !tmp * shape.(l)
    done ;
    tmp_ofs := !tmp_ofs + (!tmp * idx.(k))
  done ;
  !tmp_ofs

let linear_to_cartesian_idx shape idx =
  let rank = Array.length shape in
  let tmp = Array.make rank 0 in
  let ofs = ref idx in
  for k = 0 to rank - 1 do
    let l = rank - 1 - k in
    let n = shape.(l) in
    let j = !ofs mod n in
    tmp.(l) <- j ;
    ofs := !ofs / n
  done ;
  tmp

let mk_iter_slice rank shape slice f t =
  if rank t = 0 then f (-1) t
  else
    let n = (shape t).(0) in
    for i = 0 to n - 1 do
      f i (slice t [|i|])
    done

let mk_transpose shape create get t dim0 dim1 =
  let shape' = shape t in
  let rank = Array.length shape' in
  if dim0 >= 0 && dim0 < rank && dim1 >= 0 && dim1 < rank then (
    let tmp = shape'.(dim0) in
    shape'.(dim0) <- shape'.(dim1) ;
    shape'.(dim1) <- tmp ;
    create shape' (fun idx ->
        let tmp = idx.(dim0) in
        idx.(dim0) <- idx.(dim1) ;
        idx.(dim1) <- tmp ;
        get t idx ) )
  else raise (Invalid_argument "Tensor.transpose")

let blit n shape1 shape2 reshape1 reshape2 get1 set2 t1 t2 =
  if shape1 t1 <> shape2 t2 then
    let t1' = reshape1 t1 [|n|] in
    let t2' = reshape2 t2 [|n|] in
    for i = 0 to n - 1 do
      set2 t2' [|i|] (get1 t1' [|i|])
    done
  else raise (Invalid_argument "Tensor.blit")

module Dense = struct
  type 'a t =
    {data: 'a array; shape: int array; rank: int; stride: int; size: int}

  let rank t = t.rank

  let shape t = Array.copy t.shape

  let size t = t.size

  let create shape f =
    let rank = Array.length shape in
    let size = prod shape in
    let data =
      Array.init size (fun i -> f (linear_to_cartesian_idx shape i))
    in
    let stride = 0 in
    {data; rank; shape; stride; size}

  let is_valid_index shape idx =
    let valid = ref true in
    Array.iteri (fun i n -> valid := !valid && n >= 0 && n < shape.(i)) idx ;
    !valid

  let get_exn t idx =
    if Array.length idx = rank t && is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.stride in
      t.data.(linear_idx)
    else raise (Invalid_argument "Tensor.Dense.get_exn")

  let set_exn t idx v =
    if is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.stride in
      t.data.(linear_idx) <- v
    else raise (Invalid_argument "Tensor.Dense.set_exn")

  let blit_exn t1 t2 =
    if shape t1 = shape t2 then
      if rank t1 = 0 then t2.data.(0) <- t1.data.(0)
      else
        let o1 = t1.stride in
        let o2 = t2.stride in
        Array.blit t1.data o1 t2.data o2 t1.size
    else raise (Invalid_argument "Tensor.Dense.blit_exn")

  let transpose_exn (t : 'a t) = mk_transpose shape create get_exn t

  let reshape_exn t shape =
    if t.size = prod shape then
      let rank = Array.length shape in
      {t with shape; rank}
    else raise (Invalid_argument "Tensor.Dense.reshape_exn")

  let slice_exn t slice =
    if Array.length slice = 0 then t
    else if is_valid_index t.shape slice then
      let n = Array.length slice in
      let stride = cartesian_to_linear_idx t.shape slice + t.stride in
      let rank = t.rank - n in
      let shape = if rank > 0 then Array.sub t.shape n rank else [||] in
      let size = prod shape in
      {t with stride; rank; shape; size}
    else raise (Invalid_argument "Tensor.Dense.slice_exn")

  let sub_exn t ofs len =
    if t.rank > 0 && ofs >= 0 && ofs + len <= t.shape.(0) then (
      let stride = cartesian_to_linear_idx t.shape [|ofs|] + t.stride in
      let shape = Array.copy t.shape in
      shape.(0) <- len ;
      {t with stride; size= prod shape; shape} )
    else raise (Invalid_argument "Tensor.Dense.sub_exn")

  let iter_slice f t = mk_iter_slice rank shape slice_exn f t

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
    let stride = 0 in
    {data; shape; rank; stride; size}

  let data_to_array t = Array.sub t.data t.stride t.size
end

module CArray = struct
  type float_elt = Bigarray.float64_elt

  type int_elt = Bigarray.int_elt

  type ('a, 'b) t = ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t

  let get_exn = Bigarray.Genarray.get

  let set_exn = Bigarray.Genarray.set

  let rank = Bigarray.Genarray.num_dims

  let shape = Bigarray.Genarray.dims

  let blit_exn = Bigarray.Genarray.blit

  let reshape_exn = Bigarray.reshape

  let slice_exn = Bigarray.Genarray.slice_left

  let sub_exn = Bigarray.Genarray.sub_left

  let populate f t shape =
    let n = prod shape in
    if n = 0 then Bigarray.Genarray.set t [||] (f [||])
    else
      let t' = Bigarray.array1_of_genarray (reshape_exn t [|n|]) in
      for linear_idx = 0 to n - 1 do
        let idx = linear_to_cartesian_idx shape linear_idx in
        t'.{linear_idx} <- f idx
      done

  let create_int shape f =
    let t = Bigarray.Genarray.create Bigarray.int Bigarray.c_layout shape in
    populate f t shape ; t

  let create_float shape f =
    let t =
      Bigarray.Genarray.create Bigarray.float64 Bigarray.c_layout shape
    in
    populate f t shape ; t

  let transpose_int_exn = mk_transpose shape create_int get_exn

  let transpose_float_exn = mk_transpose shape create_float get_exn

  let iter_slice f t = mk_iter_slice rank shape slice_exn f t

  let data_to_array t =
    let n = prod (shape t) in
    let v = reshape_exn t [|n|] in
    let a = Array.make n (get_exn v [|0|]) in
    Array.iteri (fun i _ -> a.(i) <- get_exn v [|i|]) a ;
    a
end

let blit_num_nonum_exn t1 t2 =
  try
    blit (Dense.size t2) CArray.shape Dense.shape CArray.reshape_exn
      Dense.reshape_exn CArray.get_exn Dense.set_exn t1 t2
  with Invalid_argument _ ->
    raise (Invalid_argument "Tensor.blit_num_nonum_exn")

let blit_nonum_num_exn t1 t2 =
  try
    blit (Dense.size t1) Dense.shape CArray.shape Dense.reshape_exn
      CArray.reshape_exn Dense.get_exn CArray.set_exn t1 t2
  with Invalid_argument _ ->
    raise (Invalid_argument "Tensor.blit_nonum_num_exn")
