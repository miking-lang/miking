open Ustring.Op

module Mseq = struct
  type 'a t =
    | FingerTree of 'a BatFingerTree.t
    | List of 'a List.t
    | Rope of 'a array Rope.t

  let create_rope len f = Rope (Rope.create_array len f)

  let create_list len f = List (List.init len f)

  let empty_rope = Rope Rope.empty_array

  let empty_list = List []

  let create = create_rope

  let empty = empty_rope

  let length = function
    | Rope s ->
        Rope.length_array s
    | List s ->
        List.length s
    | _ ->
        failwith "Not implemented"

  let concat s1 s2 =
    match (s1, s2) with
    | Rope s1, Rope s2 ->
        Rope (Rope.concat_array s1 s2)
    | List s1, List s2 ->
        List (s1 @ s2)
    | _ ->
        failwith "Not implemented"

  let get = function
    | Rope s ->
        Rope.get_array s
    | List s ->
        List.nth s
    | _ ->
        failwith "Not implemented"

  let set s i v =
    match s with
    | Rope s ->
        Rope (Rope.set_array s i v)
    | List s ->
        let rec set i v s acc =
          match (i, s) with
          | _, [] ->
              failwith "Out of bounds access in sequence"
          | 0, _ :: xs ->
              List.rev acc @ (v :: xs)
          | i, x :: xs ->
              set (i - 1) v xs (x :: acc)
        in
        List (set i v s [])
    | _ ->
        failwith "Not implemented"

  let cons v = function
    | Rope s ->
        Rope (Rope.cons_array v s)
    | List s ->
        List (v :: s)
    | _ ->
        failwith "Not implemented"

  let snoc s v =
    match s with
    | Rope s ->
        Rope (Rope.snoc_array s v)
    | List s ->
        List (s @ [v])
    | _ ->
        failwith "Not implemented"

  let reverse = function
    | Rope s ->
        Rope (Rope.reverse_array s)
    | List s ->
        List (List.rev s)
    | _ ->
        failwith "Not implemented"

  let split_at s i =
    match s with
    | Rope s ->
        let s1, s2 = Rope.split_at_array s i in
        (Rope s1, Rope s2)
    | List s ->
        let rec split_at_rev l r = function
          | 0 ->
              (l, r)
          | i ->
              split_at_rev (List.hd r :: l) (List.tl r) (i - 1)
        in
        let l, r = split_at_rev [] s i in
        (List (List.rev l), List r)
    | _ ->
        failwith "Not implemented"

  let subsequence s a b =
    match s with
    | Rope s ->
        Rope (Rope.sub_array s a b)
    | List s ->
        let rec subsequence_rev acc s i =
          match s with
          | _ :: xs when i < a ->
              subsequence_rev acc xs (i + 1)
          | x :: xs when i < b ->
              subsequence_rev (x :: acc) xs (i + 1)
          | _ ->
              acc
        in
        List (subsequence_rev [] s 0 |> List.rev)
    | _ ->
        failwith "Not implemented"

  module Helpers = struct
    let of_list l = Rope (Rope.Convert.of_list_array l)

    let of_list_rope l = Rope (Rope.Convert.of_list_array l)

    let of_list_list l = List l

    let to_list = function
      | Rope s ->
          Rope.Convert.to_list_array s
      | List s ->
          s
      | _ ->
          failwith "Not implemented"

    let of_array a = Rope (Rope.Convert.of_array_array a)

    let of_array_rope a = Rope (Rope.Convert.of_array_array a)

    let of_array_list a = List (Array.to_list a)

    let to_array = function
      | Rope s ->
          Rope.Convert.to_array_array s
      | List s ->
          Array.of_list s
      | _ ->
          failwith "Not implemented"

    let of_ustring u = Rope (Rope.Convert.of_ustring_array u)

    let of_ustring_rope u = Rope (Rope.Convert.of_ustring_array u)

    let of_ustring_list u = List (Array.to_list (ustring2array u))

    let to_ustring = function
      | Rope s ->
          Rope.Convert.to_ustring_array s
      | List s ->
          Array.of_list s |> array2ustring
      | _ ->
          failwith "Not implemented"

    let equal f s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.equal_array f s1 s2
      | List s1, List s2 ->
          let rec equal f s1 s2 =
            match (s1, s2) with
            | [], [] ->
                true
            | [], _ | _, [] ->
                false
            | x :: xs, y :: ys ->
                f x y && equal f xs ys
          in
          equal f s1 s2
      | _ ->
          failwith "Not implemented"

    let map f = function
      | Rope s ->
          Rope (Rope.map_array_array f s)
      | List s ->
          List (List.map f s)
      | _ ->
          failwith "Not implemented"

    let fold_left f a = function
      | Rope s ->
          Rope.foldl_array f a s
      | List s ->
          List.fold_left f a s
      | _ ->
          failwith "Not implemented"

    let fold_right f s a =
      match s with
      | Rope s ->
          Rope.foldr_array f s a
      | List s ->
          List.fold_right f s a
      | _ ->
          failwith "Not implemented"

    let combine s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope (Rope.combine_array_array s1 s2)
      | List s1, List s2 ->
          List (List.combine s1 s2)
      | _ ->
          failwith "Not implemented"

    let fold_right2 f s1 s2 a =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.foldr2_array f s1 s2 a
      | List s1, List s2 ->
          List.fold_right (fun (a, b) acc -> f a b acc) (List.combine s1 s2) a
      | _ ->
          failwith "Not implemented"
  end
end

module T = struct
  type 'a t =
    | CArrayIntBoot of (int, Tensor.CArray.int_elt) Tensor.CArray.t
    | CArrayFloatBoot of (float, Tensor.CArray.float_elt) Tensor.CArray.t
    | DenseBoot of 'a Tensor.Dense.t

  type ('a, 'b) u =
    | TCArrayInt :
        (int, Tensor.CArray.int_elt) Tensor.CArray.t
        -> (int, Tensor.CArray.int_elt) u
    | TCArrayFloat :
        (float, Tensor.CArray.float_elt) Tensor.CArray.t
        -> (float, Tensor.CArray.float_elt) u
    | TDense : 'a Tensor.Dense.t -> ('a, 'b) u

  let carray_int t = TCArrayInt t

  let carray_float t = TCArrayFloat t

  let to_arr = Mseq.Helpers.to_array

  let of_arr = Mseq.Helpers.of_array

  module CArray = struct
    let create_int shape f =
      Tensor.CArray.create_int (to_arr shape) (fun ids -> f (of_arr ids))

    let create_float shape f =
      Tensor.CArray.create_float (to_arr shape) (fun ids -> f (of_arr ids))

    let get_exn t ids = Tensor.CArray.get_exn t (to_arr ids)

    let set_exn t ids v = Tensor.CArray.set_exn t (to_arr ids) v

    let rank = Tensor.CArray.rank

    let shape t = Tensor.CArray.shape t |> of_arr

    let copy_exn = Tensor.CArray.copy_exn

    let reshape_exn t shape = Tensor.CArray.reshape_exn t (to_arr shape)

    let slice_exn t shape = Tensor.CArray.slice_exn t (to_arr shape)

    let sub_exn = Tensor.CArray.sub_exn

    let iteri = Tensor.CArray.iteri
  end

  module Dense = struct
    let create shape f =
      Tensor.Dense.create (to_arr shape) (fun ids -> f (of_arr ids))

    let get_exn t ids = Tensor.Dense.get_exn t (to_arr ids)

    let set_exn t ids v = Tensor.Dense.set_exn t (to_arr ids) v

    let rank = Tensor.Dense.rank

    let shape t = Tensor.Dense.shape t |> of_arr

    let copy_exn = Tensor.Dense.copy_exn

    let reshape_exn t shape = Tensor.Dense.reshape_exn t (to_arr shape)

    let slice_exn t shape = Tensor.Dense.slice_exn t (to_arr shape)

    let sub_exn = Tensor.Dense.sub_exn

    let iteri = Tensor.Dense.iteri
  end

  let create_carray_int shape f = TCArrayInt (CArray.create_int shape f)

  let create_carray_float shape f = TCArrayFloat (CArray.create_float shape f)

  let create_dense shape f = TDense (Dense.create shape f)

  let get_exn (type a b) (t : (a, b) u) is : a =
    match t with
    | TCArrayInt t' ->
        CArray.get_exn t' is
    | TCArrayFloat t' ->
        CArray.get_exn t' is
    | TDense t' ->
        Dense.get_exn t' is

  let set_exn (type a b) (t : (a, b) u) is (v : a) =
    match t with
    | TCArrayInt t' ->
        CArray.set_exn t' is v
    | TCArrayFloat t' ->
        CArray.set_exn t' is v
    | TDense t' ->
        Dense.set_exn t' is v

  let rank (type a b) (t : (a, b) u) =
    match t with
    | TCArrayInt t' ->
        CArray.rank t'
    | TCArrayFloat t' ->
        CArray.rank t'
    | TDense t' ->
        Dense.rank t'

  let shape (type a b) (t : (a, b) u) =
    match t with
    | TCArrayInt t' ->
        CArray.shape t'
    | TCArrayFloat t' ->
        CArray.shape t'
    | TDense t' ->
        Dense.shape t'

  let copy_exn (type a b) (t1 : (a, b) u) (t2 : (a, b) u) =
    match (t1, t2) with
    | TCArrayInt t1', TCArrayInt t2' ->
        CArray.copy_exn t1' t2'
    | TCArrayFloat t1', TCArrayFloat t2' ->
        CArray.copy_exn t1' t2'
    | TDense t1', TDense t2' ->
        Dense.copy_exn t1' t2'
    | TDense t1', TCArrayInt t2' ->
        Tensor.copy_nonum_num_exn t1' t2'
    | TDense t1', TCArrayFloat t2' ->
        Tensor.copy_nonum_num_exn t1' t2'
    | TCArrayInt t1', TDense t2' ->
        Tensor.copy_num_nonum_exn t1' t2'
    | TCArrayFloat t1', TDense t2' ->
        Tensor.copy_num_nonum_exn t1' t2'

  let reshape_exn (type a b) (t : (a, b) u) shape : (a, b) u =
    match t with
    | TCArrayInt t' ->
        TCArrayInt (CArray.reshape_exn t' shape)
    | TCArrayFloat t' ->
        TCArrayFloat (CArray.reshape_exn t' shape)
    | TDense t' ->
        TDense (Dense.reshape_exn t' shape)

  let slice_exn (type a b) (t : (a, b) u) is : (a, b) u =
    match t with
    | TCArrayInt t' ->
        TCArrayInt (CArray.slice_exn t' is)
    | TCArrayFloat t' ->
        TCArrayFloat (CArray.slice_exn t' is)
    | TDense t' ->
        TDense (Dense.slice_exn t' is)

  let sub_exn (type a b) (t : (a, b) u) ofs len : (a, b) u =
    match t with
    | TCArrayInt t' ->
        TCArrayInt (CArray.sub_exn t' ofs len)
    | TCArrayFloat t' ->
        TCArrayFloat (CArray.sub_exn t' ofs len)
    | TDense t' ->
        TDense (Dense.sub_exn t' ofs len)

  let iteri (type a b) (f : int -> (a, b) u -> unit) (t : (a, b) u) =
    match t with
    | TCArrayInt t' ->
        let f' i t = f i (TCArrayInt t) in
        CArray.iteri f' t'
    | TCArrayFloat t' ->
        let f' i t = f i (TCArrayFloat t) in
        CArray.iteri f' t'
    | TDense t' ->
        let f' i t = f i (TDense t) in
        Dense.iteri f' t'

  module Helpers = struct
    open Bigarray

    let to_genarray_clayout (type a b) (t : (a, b) u) :
        (a, b, c_layout) Genarray.t =
      match t with
      | TCArrayInt t' ->
          t'
      | TCArrayFloat t' ->
          t'
      | TDense _ ->
          raise (Invalid_argument "Intrinsics.T.Helpers.to_genarray_clayout")

    let to_array1_clayout (type a b) (t : (a, b) u) : (a, b, c_layout) Array1.t
        =
      match t with
      | TCArrayInt t' ->
          t' |> array1_of_genarray
      | TCArrayFloat t' ->
          t' |> array1_of_genarray
      | TDense _ ->
          raise (Invalid_argument "Intrinsics.T.Helpers.to_array1_clayout")

    let to_array2_clayout (type a b) (t : (a, b) u) : (a, b, c_layout) Array2.t
        =
      match t with
      | TCArrayInt t' ->
          t' |> array2_of_genarray
      | TCArrayFloat t' ->
          t' |> array2_of_genarray
      | TDense _ ->
          raise (Invalid_argument "Intrinsics.T.Helpers.to_array2_clayout")

    let of_array1_clayout_int arr = arr |> genarray_of_array1 |> carray_int

    let of_array1_clayout_float arr = arr |> genarray_of_array1 |> carray_float

    let of_array2_clayout_int arr = arr |> genarray_of_array2 |> carray_int

    let of_array2_clayout_float arr = arr |> genarray_of_array2 |> carray_float
  end
end

module Symb = struct
  type t = int

  let symid = ref 0

  let gensym _ = incr symid ; !symid

  let eqsym l r = l = r

  let hash s = s

  let compare = Stdlib.compare

  module Helpers = struct
    let nosym = -1

    let ustring_of_sym = ustring_of_int

    let string_of_sym s = Ustring.to_utf8 (ustring_of_sym s)
  end
end

module File = struct
  let read f =
    f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Ustring.read_file
    |> Mseq.Helpers.of_ustring

  let write f d =
    let f = f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 in
    let d = d |> Mseq.Helpers.to_ustring in
    Ustring.write_file f d

  let exists f =
    f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Sys.file_exists

  let delete f = f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Sys.remove
end

module FloatConversion = struct
  let floorfi f = f |> Float.floor |> int_of_float

  let ceilfi f = f |> Float.ceil |> int_of_float

  let roundfi f = f |> Float.round |> int_of_float

  let string2float s = s |> Mseq.Helpers.to_ustring |> float_of_ustring

  let float2string r = r |> ustring_of_float |> Mseq.Helpers.of_ustring
end

module IO = struct
  let print s = s |> Mseq.Helpers.to_ustring |> uprint_string

  let dprint _ = ()

  let read_line _ =
    let line = try read_line () with End_of_file -> "" in
    line |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array
end

module RNG = struct
  let is_seeded = ref false

  let set_seed seed =
    Random.init seed ;
    is_seeded := true

  let int_u lower upper =
    if !is_seeded then ()
    else (
      Random.self_init () ;
      is_seeded := true ) ;
    lower + Random.int (upper - lower)
end

module MSys = struct
  let exit = exit

  let error m =
    Printf.eprintf "ERROR: %s\n"
      (m |> Mseq.Helpers.to_ustring |> Ustring.to_utf8) ;
    exit 1

  let argv =
    Sys.argv |> Mseq.Helpers.of_array
    |> Mseq.Helpers.map (fun a ->
           a |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array )

  let command s = Sys.command (s |> Mseq.Helpers.to_ustring |> Ustring.to_utf8)
end

module Time = struct
  let get_wall_time_ms _ = Unix.gettimeofday () *. 1000.

  let sleep_ms ms = Thread.delay (float_of_int ms /. 1000.)
end

module Mmap = struct
  let empty cmp =
    let cmp x y = cmp (Obj.obj x) (Obj.obj y) in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.empty, cmp)

  let insert k v mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.add (Obj.repr k) v m, cmp)

  let remove k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.remove (Obj.repr k) m, cmp)

  let find k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.find (Obj.repr k) m

  let find_or_else f k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with Some v -> v | None -> f ()

  let find_apply_or_else f felse k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with
    | Some v ->
        f v
    | None ->
        felse ()

  let bindings mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    let binds = MapModule.bindings m in
    Mseq.Helpers.of_list (List.map (fun (k, v) -> (Obj.obj k, v)) binds)

  let size mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.cardinal m

  let mem k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.mem (Obj.repr k) m

  let any p mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.exists (fun k v -> p (Obj.obj k) v) m

  let map f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.map f m, cmp)

  let map_with_key f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.mapi (fun k v -> f (Obj.obj k) v) m, cmp)

  let fold_with_key f z mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.fold (fun k v acc -> f acc (Obj.obj k) v) m z

  let eq veq m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.equal veq m1 m2

  let cmp vcmp m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.compare vcmp m1 m2

  let key_cmp mCmpPair k1 k2 =
    let _, cmp = Obj.obj mCmpPair in
    (cmp : Obj.t -> Obj.t -> int) (Obj.repr k1) (Obj.repr k2)
end
