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

(* let linear_to_cartesian_idx shape idx =
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
  tmp *)

type ('a, 'b) tensor_ops =
  { rank: 'a -> int
  ; shape: 'a -> int array
  ; size: 'a -> int
  ; get_exn: 'a -> int array -> 'b
  ; set_exn: 'a -> int array -> 'b -> unit
  ; reshape_exn: 'a -> int array -> 'a
  ; slice_exn: 'a -> int array -> 'a }

let iter_slice ops f t =
  if ops.rank t = 0 then f (-1) t
  else
    let n = (ops.shape t).(0) in
    for i = 0 to n - 1 do
      f i (ops.slice_exn t [|i|])
    done

let transpose ops create t dim0 dim1 =
  let shape' = ops.shape t in
  let rank = Array.length shape' in
  if dim0 >= 0 && dim0 < rank && dim1 >= 0 && dim1 < rank then (
    let tmp = shape'.(dim0) in
    shape'.(dim0) <- shape'.(dim1) ;
    shape'.(dim1) <- tmp ;
    create shape' (fun idx ->
        let idx' = Array.copy idx in
        let tmp = idx'.(dim0) in
        idx'.(dim0) <- idx'.(dim1) ;
        idx'.(dim1) <- tmp ;
        ops.get_exn t idx' ) )
  else raise (Invalid_argument "Tensor.transpose")

let blit ops1 ops2 t1 t2 =
  let n = ops1.size t1 in
  if ops1.shape t1 <> ops2.shape t2 then
    let t1' = ops1.reshape_exn t1 [|n|] in
    let t2' = ops2.reshape_exn t2 [|n|] in
    for i = 0 to n - 1 do
      ops2.set_exn t2' [|i|] (ops1.get_exn t1' [|i|])
    done
  else raise (Invalid_argument "Tensor.blit")

let equal ops1 ops2 eq t1 t2 =
  if ops1.shape t1 = ops2.shape t2 then (
    let n = ops1.size t1 in
    let v1 = ops1.reshape_exn t1 [|n|] in
    let v2 = ops2.reshape_exn t2 [|n|] in
    let tmp = ref true in
    let i = ref 0 in
    while !tmp do
      tmp := eq (ops1.get_exn v1 [|!i|]) (ops2.get_exn v2 [|!i|]) ;
      incr i
    done ;
    !tmp )
  else false

module Dense = struct
  type 'a t =
    {data: 'a array; shape: int array; rank: int; stride: int; size: int}

  let rank t = t.rank

  let shape t = Array.copy t.shape

  let size t = t.size

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

  let ops = {rank; shape; size; get_exn; set_exn; reshape_exn; slice_exn}

  (* Adoped from OCaml Bigarray implementation *)
  let rec loop t idx0 idx f dim shape =
    if dim = Array.length idx then
      if idx = idx0 then () else set_exn t idx (f idx)
    else
      for j = 0 to pred shape.(dim) do
        idx.(dim) <- j ;
        loop t idx0 idx f (succ dim) shape
      done

  let create shape f =
    let stride = 0 in
    let rank = Array.length shape in
    let size = prod shape in
    if size = 0 then
      let data = [||] in
      {data; rank; shape; stride; size}
    else
      let idx = Array.make rank 0 in
      let x0 = f idx in
      let data = Array.make size x0 in
      let t = {data; rank; shape; stride; size} in
      if rank = 0 then t
      else (
        loop t (Array.copy idx) idx f 0 shape ;
        t )

  let blit_exn t1 t2 =
    if shape t1 = shape t2 then
      if rank t1 = 0 then t2.data.(0) <- t1.data.(0)
      else
        let o1 = t1.stride in
        let o2 = t2.stride in
        Array.blit t1.data o1 t2.data o2 t1.size
    else raise (Invalid_argument "Tensor.Dense.blit_exn")

  let copy t =
    let data = Array.init t.size (fun i -> t.data.(i + t.stride)) in
    let shape = t.shape in
    let rank = t.rank in
    let stride = 0 in
    let size = t.size in
    {data; shape; rank; stride; size}

  let transpose_exn (t : 'a t) = transpose ops create t

  let iter_slice f t = iter_slice ops f t

  let equal eq t1 t2 = equal ops ops eq t1 t2

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

  let size t = prod (shape t)

  let blit_exn = Bigarray.Genarray.blit

  let copy t =
    let t' =
      Bigarray.Genarray.create (Bigarray.Genarray.kind t) Bigarray.c_layout
        (shape t)
    in
    blit_exn t t' ; t'

  let reshape_exn = Bigarray.reshape

  let slice_exn = Bigarray.Genarray.slice_left

  let sub_exn = Bigarray.Genarray.sub_left

  let create (type a b) (kind : (a, b) Bigarray.kind) shape (f : int array -> a)
      : (a, b) t =
    if Array.length shape = 0 then (
      let t = Bigarray.Genarray.create kind Bigarray.c_layout shape in
      Bigarray.Genarray.set t shape (f shape) ;
      t )
    else Bigarray.Genarray.init kind Bigarray.c_layout shape f

  let create_int = create Bigarray.int

  let create_float = create Bigarray.float64

  let ops = {rank; shape; size; get_exn; set_exn; reshape_exn; slice_exn}

  let transpose_int_exn = transpose ops create_int

  let transpose_float_exn = transpose ops create_float

  let iter_slice f t = iter_slice ops f t

  let equal eq t1 t2 = equal ops ops eq t1 t2

  let data_to_array t =
    let n = prod (shape t) in
    let v = reshape_exn t [|n|] in
    let a = Array.make n (get_exn v [|0|]) in
    Array.iteri (fun i _ -> a.(i) <- get_exn v [|i|]) a ;
    a
end
