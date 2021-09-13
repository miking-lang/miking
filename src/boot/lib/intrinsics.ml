open Ustring.Op

module Mseq = struct
  type 'a t = List of 'a List.t | Rope of 'a Rope.t

  let create_rope n f = Rope (Rope.create_array n f)

  let create_list n f = List (List.init n f)

  let empty_rope = Rope Rope.empty_array

  let empty_list = List []

  let create = create_rope

  let empty = empty_rope

  let length = function
    | Rope s ->
        Rope.length_array s
    | List s ->
        List.length s

  let concat s1 s2 =
    match (s1, s2) with
    | Rope s1, Rope s2 ->
        Rope (Rope.concat_array s1 s2)
    | List s1, List s2 ->
        List (s1 @ s2)
    | _ ->
        raise (Invalid_argument "Mseq.concat")

  let get = function Rope s -> Rope.get_array s | List s -> List.nth s

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

  let cons v = function
    | Rope s ->
        Rope (Rope.cons_array v s)
    | List s ->
        List (v :: s)

  let snoc s v =
    match s with
    | Rope s ->
        Rope (Rope.snoc_array s v)
    | List s ->
        List (s @ [v])

  let reverse = function
    | Rope s ->
        Rope (Rope.reverse_array s)
    | List s ->
        List (List.rev s)

  let head = function Rope s -> Rope.get_array s 0 | List s -> List.hd s

  let tail = function
    | Rope s ->
        Rope (Rope.sub_array s 1 (Rope.length_array s))
    | List s ->
        List (List.tl s)

  let null = function
    | Rope s ->
        Rope.length_array s == 0
    | List s -> (
      match s with [] -> true | _ -> false )

  let iter f = function
    | Rope s ->
        Rope.iter_array f s
    | List s ->
        List.iter f s

  let iteri f = function
    | Rope s ->
        Rope.iteri_array f s
    | List s ->
        List.iteri f s

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

  let subsequence s a n =
    match s with
    | Rope s ->
        Rope (Rope.sub_array s a n)
    | List s ->
        let rec subsequence_rev acc s i j =
          match s with
          | _ :: xs when i < a ->
              subsequence_rev acc xs (i + 1) j
          | x :: xs when j < n ->
              subsequence_rev (x :: acc) xs (i + 1) (j + 1)
          | _ ->
              acc
        in
        List (subsequence_rev [] s 0 0 |> List.rev)

  let map f = function
    | Rope s ->
        Rope (Rope.map_array_array f s)
    | List s ->
        List (List.map f s)

  let mapi f = function
    | Rope s ->
        Rope (Rope.mapi_array_array f s)
    | List s ->
        List (List.mapi f s)

  module Helpers = struct
    let of_list_rope l = Rope (Rope.Convert.of_list_array l)

    let of_list_list l = List l

    let to_list = function
      | Rope s ->
          Rope.Convert.to_list_array s
      | List s ->
          s

    let of_array_rope a = Rope (Rope.Convert.of_array_array a)

    let of_array_list a = List (Array.to_list a)

    let to_array = function
      | Rope s ->
          Rope.Convert.to_array_array s
      | List s ->
          Array.of_list s

    let of_ustring_rope u = Rope (Rope.Convert.of_ustring_array u)

    let of_ustring_list u = List (ustring2list u)

    let to_ustring = function
      | Rope s ->
          Rope.Convert.to_ustring_array s
      | List s ->
          list2ustring s

    let equal f s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.equal_array f s1 s2
      | List s1, List s2 ->
          List.equal f s1 s2
      | _ ->
          raise (Invalid_argument "Mseq.equal")

    let fold_left f a = function
      | Rope s ->
          Rope.foldl_array f a s
      | List s ->
          List.fold_left f a s

    let fold_right f a = function
      | Rope s ->
          Rope.foldr_array f s a
      | List s ->
          List.fold_right f s a

    let combine s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope (Rope.combine_array_array s1 s2)
      | List s1, List s2 ->
          List (List.combine s1 s2)
      | _ ->
          raise (Invalid_argument "Mseq.combine")

    let fold_right2 f s1 s2 a =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.foldr2_array f s1 s2 a
      | List s1, List s2 ->
          List.fold_right2 f s1 s2 a
      | _ ->
          raise (Invalid_argument "Mseq.fold_right2")

    let of_list = of_list_rope

    let of_array = of_array_rope

    let of_ustring = of_ustring_rope
  end
end

module T = struct
  open Bigarray

  type 'a t =
    | TBootInt of (int, int_elt) Tensor.Barray.t
    | TBootFloat of (float, float64_elt) Tensor.Barray.t
    | TBootGen of ('a, 'a) Tensor.Generic.t

  type ('a, 'b) u =
    | TInt : (int, int_elt) Tensor.Barray.t -> (int, int_elt) u
    | TFloat : (float, float64_elt) Tensor.Barray.t -> (float, float64_elt) u
    | TGen : ('a, 'b) Tensor.Generic.t -> ('a, 'b) u

  module type OP_MSEQ = sig
    type ('a, 'b) t

    val get_exn : ('a, 'b) t -> int Mseq.t -> 'a

    val set_exn : ('a, 'b) t -> int Mseq.t -> 'a -> unit

    val shape : ('a, 'b) t -> int Mseq.t

    val reshape_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t

    val slice_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t
  end

  let to_arr = Mseq.Helpers.to_array

  let of_arr = Mseq.Helpers.of_array

  module Op_mseq (T : Tensor.TENSOR) :
    OP_MSEQ with type ('a, 'b) t = ('a, 'b) T.t = struct
    type ('a, 'b) t = ('a, 'b) T.t

    let get_exn t idx = T.get_exn t (to_arr idx)

    let set_exn t idx = T.set_exn t (to_arr idx)

    let shape t = of_arr (T.shape t)

    let reshape_exn t shape = T.reshape_exn t (to_arr shape)

    let slice_exn t idx = T.slice_exn t (to_arr idx)
  end

  module Op_mseq_generic = Op_mseq (Tensor.Generic)
  module Op_mseq_barray = Op_mseq (Tensor.Barray)

  let create_int shape f =
    Tensor.Barray.create_int (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_float shape f =
    Tensor.Barray.create_float (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_generic shape f =
    Tensor.Generic.create (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_int_packed shape f = TInt (create_int shape f)

  let create_float_packed shape f = TFloat (create_float shape f)

  let create_generic_packed shape f = TGen (create_generic shape f)

  let get_exn (type a b) (t : (a, b) u) idx : a =
    match t with
    | TInt t' ->
        Op_mseq_barray.get_exn t' idx
    | TFloat t' ->
        Op_mseq_barray.get_exn t' idx
    | TGen t' ->
        Op_mseq_generic.get_exn t' idx

  let set_exn (type a b) (t : (a, b) u) idx (v : a) : unit =
    match t with
    | TInt t' ->
        Op_mseq_barray.set_exn t' idx v
    | TFloat t' ->
        Op_mseq_barray.set_exn t' idx v
    | TGen t' ->
        Op_mseq_generic.set_exn t' idx v

  let shape (type a b) (t : (a, b) u) : int Mseq.t =
    match t with
    | TInt t' ->
        Op_mseq_barray.shape t'
    | TFloat t' ->
        Op_mseq_barray.shape t'
    | TGen t' ->
        Op_mseq_generic.shape t'

  let slice_exn (type a b) (t : (a, b) u) idx : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Op_mseq_barray.slice_exn t' idx)
    | TFloat t' ->
        TFloat (Op_mseq_barray.slice_exn t' idx)
    | TGen t' ->
        TGen (Op_mseq_generic.slice_exn t' idx)

  let reshape_exn (type a b) (t : (a, b) u) idx : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Op_mseq_barray.reshape_exn t' idx)
    | TFloat t' ->
        TFloat (Op_mseq_barray.reshape_exn t' idx)
    | TGen t' ->
        TGen (Op_mseq_generic.reshape_exn t' idx)

  let sub_exn (type a b) (t : (a, b) u) start len : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.sub_exn t' start len)
    | TFloat t' ->
        TFloat (Tensor.Barray.sub_exn t' start len)
    | TGen t' ->
        TGen (Tensor.Generic.sub_exn t' start len)

  let copy (type a b) (t : (a, b) u) : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.copy t')
    | TFloat t' ->
        TFloat (Tensor.Barray.copy t')
    | TGen t' ->
        TGen (Tensor.Generic.copy t')

  let transpose_exn (type a b) (t : (a, b) u) dim0 dim1 : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.transpose_exn t' dim0 dim1)
    | TFloat t' ->
        TFloat (Tensor.Barray.transpose_exn t' dim0 dim1)
    | TGen t' ->
        TGen (Tensor.Generic.transpose_exn t' dim0 dim1)

  let iter_slice (type a b) (f : int -> (a, b) u -> unit) (t : (a, b) u) : unit
      =
    match t with
    | TInt t' ->
        Tensor.Uop_barray.iter_slice (fun i t -> f i (TInt t)) t'
    | TFloat t' ->
        Tensor.Uop_barray.iter_slice (fun i t -> f i (TFloat t)) t'
    | TGen t' ->
        Tensor.Uop_generic.iter_slice (fun i t -> f i (TGen t)) t'

  let rank (type a b) (t : (a, b) u) : int =
    match t with
    | TInt t' ->
        Tensor.Barray.rank t'
    | TFloat t' ->
        Tensor.Barray.rank t'
    | TGen t' ->
        Tensor.Generic.rank t'

  let equal (type a b c d) (eq : a -> b -> bool) (t1 : (a, c) u) (t2 : (b, d) u)
      : bool =
    match (t1, t2) with
    | TInt t1', TInt t2' ->
        Tensor.Bop_barray_barray.equal eq t1' t2'
    | TFloat t1', TInt t2' ->
        Tensor.Bop_barray_barray.equal eq t1' t2'
    | TGen t1', TInt t2' ->
        Tensor.Bop_generic_barray.equal eq t1' t2'
    | _, TFloat t2' -> (
      match t1 with
      | TInt t1' ->
          Tensor.Bop_barray_barray.equal eq t1' t2'
      | TFloat t1' ->
          Tensor.Bop_barray_barray.equal eq t1' t2'
      | TGen t1' ->
          Tensor.Bop_generic_barray.equal eq t1' t2' )
    | _, TGen t2' -> (
      match t1 with
      | TInt t1' ->
          Tensor.Bop_barray_generic.equal eq t1' t2'
      | TFloat t1' ->
          Tensor.Bop_barray_generic.equal eq t1' t2'
      | TGen t1' ->
          Tensor.Bop_generic_generic.equal eq t1' t2' )

  let to_string (type a b) (el2str : a -> int Mseq.t) (t : (a, b) u) :
      int Mseq.t =
    let el2str x = Mseq.Helpers.to_ustring (el2str x) in
    ( match t with
    | TInt t' ->
        Tensor.Uop_barray.to_ustring el2str t'
    | TFloat t' ->
        Tensor.Uop_barray.to_ustring el2str t'
    | TGen t' ->
        Tensor.Uop_generic.to_ustring el2str t' )
    |> Mseq.Helpers.of_ustring

  module Helpers = struct
    let to_genarray_clayout (type a b) (t : (a, b) u) :
        (a, b, c_layout) Genarray.t =
      match t with
      | TInt t' ->
          Tensor.Barray.to_genarray_clayout t'
      | TFloat t' ->
          Tensor.Barray.to_genarray_clayout t'
      | TGen _ ->
          raise
            (Invalid_argument "Intrinsics.T.Helpers.to_genarray_clayout_int")

    let to_array1_clayout t = to_genarray_clayout t |> array1_of_genarray

    let to_array2_clayout t = to_genarray_clayout t |> array2_of_genarray

    let of_genarray_clayout (type a b) (a : (a, b, c_layout) Genarray.t) :
        (a, b) u =
      match Genarray.kind a with
      | Bigarray.Int ->
          TInt (Tensor.Barray.of_genarray_clayout a)
      | Bigarray.Float64 ->
          TFloat (Tensor.Barray.of_genarray_clayout a)
      | _ ->
          raise (Invalid_argument "Intrinsics.T.Helpers.of_genarray_clayout")

    let of_array1_clayout t = genarray_of_array1 t |> of_genarray_clayout

    let of_array2_clayout t = genarray_of_array2 t |> of_genarray_clayout
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

  let dprint v =
    let v = Obj.repr v in
    let string_of_tag t =
      let res = ref (string_of_int t) in
      if t = Obj.lazy_tag then res := !res ^ " (lazy)" ;
      if t = Obj.closure_tag then res := !res ^ " (closure)" ;
      if t = Obj.object_tag then res := !res ^ " (object)" ;
      if t = Obj.infix_tag then res := !res ^ " (infix)" ;
      if t = Obj.forward_tag then res := !res ^ " (forward)" ;
      if t = Obj.no_scan_tag then res := !res ^ " (no_scan)" ;
      if t = Obj.abstract_tag then res := !res ^ " (abstract)" ;
      if t = Obj.string_tag then res := !res ^ " (string)" ;
      if t = Obj.double_tag then res := !res ^ " (double)" ;
      if t = Obj.double_array_tag then res := !res ^ " (double_array)" ;
      if t = Obj.custom_tag then res := !res ^ " (custom)" ;
      if t = Obj.int_tag then res := !res ^ " (int)" ;
      if t = Obj.out_of_heap_tag then res := !res ^ " (out_of_heap)" ;
      if t = Obj.unaligned_tag then res := !res ^ " (unaligned)" ;
      !res
    in
    let rec work indent v =
      if Obj.is_int v then string_of_int (Obj.obj v) ^ "\n"
      else if Obj.tag v = Obj.double_tag then
        string_of_float (Obj.obj v) ^ "\n"
      else if Obj.tag v = Obj.closure_tag then "<closure>\n"
      else
        let istr = String.make indent ' ' in
        let children =
          List.init (Obj.size v) (fun i ->
              istr ^ ", " ^ work (indent + 2) (Obj.field v i) )
        in
        "{ tag: "
        ^ string_of_tag (Obj.tag v)
        ^ ", size: "
        ^ string_of_int (Obj.size v)
        ^ "\n" ^ String.concat "" children ^ istr ^ "}\n"
    in
    print_string (work 0 v)

  let flush_stdout () = flush stdout

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
    |> Mseq.map (fun a ->
           a |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array )

  let command s = Sys.command (s |> Mseq.Helpers.to_ustring |> Ustring.to_utf8)
end

module Time = struct
  let get_wall_time_ms _ = Unix.gettimeofday () *. 1000.

  let sleep_ms ms = Thread.delay (float_of_int ms /. 1000.)
end

module ConTag = struct
  let constructor_tag obj =
    if Obj.is_int obj then Obj.obj obj + Obj.custom_tag else Obj.tag obj
end

module Mmap = struct
  module type Map = sig
    type k

    type v

    include Map.S with type key := k

    val theMap : v t

    val cmp : k -> k -> int
  end

  type ('a, 'b) t = (module Map with type k = 'a and type v = 'b)

  let empty (type a b) (cmp : a -> a -> int) : (a, b) t =
    let module Ord = struct
      let compare = cmp

      type t = a
    end in
    let module MapModule = Map.Make (Ord) in
    let module M = struct
      type k = a

      type v = b

      include MapModule

      let theMap = empty

      let cmp = cmp
    end in
    (module M)

  let insert (type a b) (k : a) (v : b) (m : (a, b) t) : (a, b) t =
    let open (val m) in
    let module M = struct
      include (val m)

      let theMap = add k v theMap
    end in
    (module M)

  let remove (type k v) (k : k) (m : (k, v) t) : (k, v) t =
    let open (val m) in
    let module M = struct
      include (val m)

      let theMap = remove k theMap
    end in
    (module M)

  let find (type k v) (k : k) (m : (k, v) t) : v =
    let open (val m) in
    find k theMap

  let find_or_else (type k v) (f : unit -> v) (k : k) (m : (k, v) t) : v =
    let open (val m) in
    match find_opt k theMap with Some v -> v | None -> f ()

  let find_apply_or_else (type k v v') (f : v -> v') (felse : unit -> v')
      (k : k) (m : (k, v) t) : v' =
    let open (val m) in
    match find_opt k theMap with Some v -> f v | None -> felse ()

  let bindings (type k v) (m : (k, v) t) : (k * v) Mseq.t =
    let open (val m) in
    Mseq.Helpers.of_list (bindings theMap)

  let size (type k v) (m : (k, v) t) : int =
    let open (val m) in
    cardinal theMap

  let mem (type k v) (k : k) (m : (k, v) t) : bool =
    let open (val m) in
    mem k theMap

  let any (type k v) (p : k -> v -> bool) (m : (k, v) t) : bool =
    let open (val m) in
    exists p theMap

  let map (type k v v') (f : v -> v') (m : (k, v) t) : (k, v') t =
    let open (val m) in
    let module M = struct
      include (val m)

      type v = v'

      let theMap = map f theMap
    end in
    (module M)

  let map_with_key (type k v v') (f : k -> v -> v') (m : (k, v) t) : (k, v') t
      =
    let open (val m) in
    let module M = struct
      include (val m)

      type v = v'

      let theMap = mapi f theMap
    end in
    (module M)

  let fold_with_key (type k v a) (f : a -> k -> v -> a) (a : a) (m : (k, v) t)
      : a =
    let open (val m) in
    fold (fun k v a -> f a k v) theMap a

  let eq (type k v) (veq : v -> v -> bool) (m1 : (k, v) t) (m2 : (k, v) t) :
      bool =
    let open (val m1) in
    let binds1 : (k * v) Seq.t = to_seq theMap in
    let open (val m2) in
    let binds2 : (k * v) Seq.t = to_seq theMap in
    let rec work b1 b2 =
      match b1, b2 with
      | (Seq.Nil, Seq.Nil) -> true
      | (Seq.Cons _, Seq.Nil) | (Seq.Nil, Seq.Cons _) -> false
      | (Seq.Cons ((k1, v1), b1), Seq.Cons ((k2, v2), b2)) ->
         if cmp k1 k2 = 0 then
           if veq v1 v2 then
             work (b1 ()) (b2 ())
           else false
         else false
    in work (binds1 ()) (binds2 ())

  let cmp (type k v) (vcmp : v -> v -> int) (m1 : (k, v) t) (m2 : (k, v) t) :
    int =
    let open (val m1) in
    let binds1 : (k * v) Seq.t = to_seq theMap in
    let open (val m2) in
    let binds2 : (k * v) Seq.t = to_seq theMap in
    let rec work b1 b2 =
      match b1, b2 with
      | (Seq.Nil, Seq.Nil) -> 0
      | (Seq.Nil, Seq.Cons _) -> -1
      | (Seq.Cons _, Seq.Nil) -> 1
      | (Cons ((k1, v1), b1), Cons ((k2, v2), b2)) ->
        let key_diff = cmp k1 k2 in
        if key_diff = 0 then
          let val_diff = vcmp v1 v2 in
          if val_diff = 0 then
            work (b1 ()) (b2 ())
          else val_diff
        else key_diff
    in work (binds1 ()) (binds2 ())

  let key_cmp (type k v) (m : (k, v) t) (k1 : k) (k2 : k) : int =
    let open (val m) in
    cmp k1 k2
end
