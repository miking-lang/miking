open Ustring.Op

module type TENSOR = sig
  type ('a, 'b) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val linear_get_exn : ('a, 'b) t -> int -> 'a

  val linear_set_exn : ('a, 'b) t -> int -> 'a -> unit

  val shape : ('a, 'b) t -> int array

  val rank : ('a, 'b) t -> int

  val size : ('a, 'b) t -> int

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val copy : ('a, 'b) t -> ('a, 'b) t

  val transpose_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t
end

module type GENERIC = sig
  include TENSOR

  val create : int array -> (int array -> 'a) -> ('a, 'b) t
end

module type BARRAY = sig
  open Bigarray

  include TENSOR

  val uninit_int : int array -> (int, int_elt) t

  val uninit_float : int array -> (float, float64_elt) t

  val create_int : int array -> (int array -> int) -> (int, int_elt) t

  val create_float :
    int array -> (int array -> float) -> (float, float64_elt) t

  val to_genarray_clayout : ('a, 'b) t -> ('a, 'b, c_layout) Genarray.t

  val of_genarray_clayout : ('a, 'b, c_layout) Genarray.t -> ('a, 'b) t
end

module type UOP = sig
  type ('a, 'b) t

  val iter_slice : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val to_data_array : ('a, 'b) t -> 'a array

  val to_ustring : ('a -> ustring) -> ('a, 'b) t -> ustring
end

module type BOP = sig
  type ('a, 'b) t1

  type ('c, 'd) t2

  val equal : ('a -> 'c -> bool) -> ('a, 'b) t1 -> ('c, 'd) t2 -> bool
end

let prod = Array.fold_left ( * ) 1

let cartesian_to_linear_idx shape idx =
  let rank = Array.length shape in
  let n = Array.length idx in
  let tmp_ofs = ref 0 in
  let tmp = ref 1 in
  for k = rank - 1 downto n do
    tmp := !tmp * shape.(k)
  done ;
  for k = n - 1 downto 0 do
    tmp_ofs := !tmp_ofs + (!tmp * idx.(k)) ;
    tmp := !tmp * shape.(k)
  done ;
  !tmp_ofs

let linear_to_cartesian_idx shape linear_idx =
  let rank = Array.length shape in
  let idx = Array.make rank 0 in
  let tmp_k = ref linear_idx in
  for i = rank - 1 downto 0 do
    let d = shape.(i) in
    idx.(i) <- !tmp_k mod d ;
    tmp_k := !tmp_k / d
  done ;
  idx

let transpose create shape get_exn t dim0 dim1 =
  let shape' = shape t in
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
        get_exn t idx' ) )
  else raise (Invalid_argument "Tensor.transpose")

module Generic : GENERIC = struct
  type ('a, _) t =
    {data: 'a array; shape: int array; rank: int; offset: int; size: int}

  let rank t = t.rank

  let shape t = Array.copy t.shape

  let size t = t.size

  let is_valid_index shape idx =
    let valid = ref true in
    Array.iteri (fun i n -> valid := !valid && n >= 0 && n < shape.(i)) idx ;
    !valid

  let get_exn t idx =
    if Array.length idx = rank t && is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.offset in
      t.data.(linear_idx)
    else raise (Invalid_argument "Tensor.Op_mseq_generic.get_exn")

  let set_exn t idx v =
    if is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.offset in
      t.data.(linear_idx) <- v
    else raise (Invalid_argument "Tensor.Op_mseq_generic.set_exn")

  let linear_get_exn t linear_idx =
    if linear_idx >= 0 && linear_idx < t.size then
      t.data.(linear_idx + t.offset)
    else raise (Invalid_argument "Tensor.Op_mseq_generic.linear_get_exn")

  let linear_set_exn t linear_idx v =
    if linear_idx >= 0 && linear_idx < t.size then
      t.data.(linear_idx + t.offset) <- v
    else raise (Invalid_argument "Tensor.Op_mseq_generic.linear_set_exn")

  let reshape_exn t shape =
    if t.size = prod shape then
      let rank = Array.length shape in
      {t with shape; rank}
    else raise (Invalid_argument "Tensor.Dense.reshape_exn")

  let slice_exn t slice =
    if Array.length slice = 0 then t
    else if is_valid_index t.shape slice then
      let n = Array.length slice in
      let offset = cartesian_to_linear_idx t.shape slice + t.offset in
      let rank = t.rank - n in
      let shape = if rank > 0 then Array.sub t.shape n rank else [||] in
      let size = prod shape in
      {t with offset; rank; shape; size}
    else raise (Invalid_argument "Tensor.Dense.slice_exn")

  let sub_exn t ofs len =
    if t.rank > 0 && ofs >= 0 && ofs + len <= t.shape.(0) then (
      let offset = cartesian_to_linear_idx t.shape [|ofs|] + t.offset in
      let shape = Array.copy t.shape in
      shape.(0) <- len ;
      {t with offset; size= prod shape; shape} )
    else raise (Invalid_argument "Tensor.Dense.sub_exn")

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
    let offset = 0 in
    let rank = Array.length shape in
    let size = prod shape in
    if size = 0 then
      let data = [||] in
      {data; rank; shape; offset; size}
    else
      let idx = Array.make rank 0 in
      let x0 = f idx in
      let data = Array.make size x0 in
      let t = {data; rank; shape; offset; size} in
      if rank = 0 then t
      else (
        loop t (Array.copy idx) idx f 0 shape ;
        t )

  let copy t =
    let data = Array.init t.size (fun i -> t.data.(i + t.offset)) in
    let shape = t.shape in
    let rank = t.rank in
    let offset = 0 in
    let size = t.size in
    {data; shape; rank; offset; size}

  let transpose_exn t dim0 dim1 = transpose create shape get_exn t dim0 dim1
end

module Barray : BARRAY = struct
  open Bigarray

  type ('a, 'b) t = ('a, 'b, c_layout) Genarray.t

  let get_exn = Genarray.get

  let set_exn = Genarray.set

  let rank = Genarray.num_dims

  let shape = Genarray.dims

  let linear_get_exn t linear_idx =
    get_exn t (linear_to_cartesian_idx (shape t) linear_idx)

  let linear_set_exn t linear_idx v =
    set_exn t (linear_to_cartesian_idx (shape t) linear_idx) v

  let size t = prod (shape t)

  let blit_exn = Genarray.blit

  let copy t =
    let t' = Genarray.create (Genarray.kind t) c_layout (shape t) in
    blit_exn t t' ; t'

  let reshape_exn = reshape

  let slice_exn = Genarray.slice_left

  let sub_exn = Genarray.sub_left

  let create (type a b) (kind : (a, b) Bigarray.kind) shape (f : int array -> a)
      : (a, b) t =
    if Array.length shape = 0 then (
      let t = Genarray.create kind c_layout shape in
      Genarray.set t shape (f shape) ;
      t )
    else Genarray.init kind c_layout shape f

  let uninit_int = Genarray.create Bigarray.int c_layout

  let uninit_float = Genarray.create Bigarray.float64 c_layout

  let create_int = create Bigarray.int

  let create_float = create Bigarray.float64

  let transpose_exn t dim0 dim1 =
    transpose (create (Genarray.kind t)) shape get_exn t dim0 dim1

  let to_genarray_clayout t = t

  let of_genarray_clayout t = t
end

module Uop (T : TENSOR) : UOP with type ('a, 'b) t = ('a, 'b) T.t = struct
  type ('a, 'b) t = ('a, 'b) T.t

  let iter_slice f t =
    if T.rank t = 0 then f 0 t
    else
      let n = (T.shape t).(0) in
      for i = 0 to n - 1 do
        f i (T.slice_exn t [|i|])
      done

  let to_data_array t =
    let n = T.size t in
    let t' = T.reshape_exn t [|n|] in
    Array.init n (fun i -> T.get_exn t' [|i|])

  let to_ustring el2str =
    let rec recur indent t =
      let rank = T.rank t in
      if rank = 0 then el2str (T.get_exn t [||])
      else if rank = 1 then (
        let elems = ref (us "") in
        let n = (T.shape t).(0) in
        for i = 0 to n - 1 do
          let e = if i < n - 1 then us ", " else us "" in
          elems := !elems ^. recur (us "") (T.slice_exn t [|i|]) ^. e
        done ;
        us "[" ^. !elems ^. us "]" )
      else
        let n = (T.shape t).(0) in
        let newindent = indent ^. us "\t" in
        let elems = ref (us "") in
        for i = 0 to n - 1 do
          let e = if i < n - 1 then us ",\n" ^. newindent else us "" in
          elems := !elems ^. recur newindent (T.slice_exn t [|i|]) ^. e
        done ;
        us "[\n" ^. newindent ^. !elems ^. us "\n" ^. indent ^. us "]"
    in
    recur (us "")
end

module Bop (T1 : TENSOR) (T2 : TENSOR) :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) T1.t
     and type ('c, 'd) t2 = ('c, 'd) T2.t = struct
  type ('a, 'b) t1 = ('a, 'b) T1.t

  type ('c, 'd) t2 = ('c, 'd) T2.t

  let equal eq t1 t2 =
    if T1.shape t1 = T2.shape t2 then (
      let n = T1.size t1 in
      let v1 = T1.reshape_exn t1 [|n|] in
      let v2 = T2.reshape_exn t2 [|n|] in
      let tmp = ref true in
      let i = ref 0 in
      while !tmp && !i < n do
        tmp := eq (T1.get_exn v1 [|!i|]) (T2.get_exn v2 [|!i|]) ;
        incr i
      done ;
      !tmp )
    else false
end

module Uop_generic = Uop (Generic)
module Uop_barray = Uop (Barray)
module Bop_generic_generic = Bop (Generic) (Generic)
module Bop_barray_barray = Bop (Barray) (Barray)
module Bop_generic_barray = Bop (Generic) (Barray)
module Bop_barray_generic = Bop (Barray) (Generic)
