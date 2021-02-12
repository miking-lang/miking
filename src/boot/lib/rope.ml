open Bigarray
open Ustring.Op

type ('a, 'b) ba = ('a, 'b, c_layout) Array1.t

type int_ba = (int, int_elt) ba

type float_ba = (float, float64_elt) ba

type 'a u = Leaf of 'a | Concat of {lhs: 'a u; rhs: 'a u; len: int}

type 'a t = 'a u ref

let rec _bigarray_kind (s : ('a, 'b) ba u) : ('a, 'c) kind =
  match s with
  | Leaf a ->
      Array1.kind a
  | Concat {lhs; _} ->
      _bigarray_kind lhs

let _uninit_bigarray (k : ('a, 'b) kind) (n : int) : ('a, 'b) ba =
  Array1.create k c_layout n

let _make_bigarray (k : ('a, 'b) kind) (n : int) (v : 'a) : ('a, 'b) ba t =
  let a = _uninit_bigarray k n in
  Array1.fill a v ; ref (Leaf a)

let make_array (n : int) (v : 'a) : 'a array t = ref (Leaf (Array.make n v))

let make_int_bigarray (n : int) (v : int) : int_ba t = _make_bigarray Int n v

let make_float_bigarray (n : int) (v : float) : float_ba t =
  _make_bigarray Float64 n v

let empty_array = Obj.magic (ref (Leaf [||]))

let _empty_bigarray (k : ('a, 'b) kind) : ('a, 'b) ba t =
  ref (Leaf (_uninit_bigarray k 0))

let empty_int_bigarray : int_ba t = _empty_bigarray Int

let empty_float_bigarray : float_ba t = _empty_bigarray Float64

let _length_array (s : 'a array u) : int =
  match s with Leaf a -> Array.length a | Concat {len; _} -> len

let length_array (s : 'a array t) : int = _length_array !s

let _length_bigarray (s : ('a, 'b) ba u) : int =
  match s with Leaf a -> Array1.dim a | Concat {len; _} -> len

let length_bigarray (s : ('a, 'b) ba t) : int = _length_bigarray !s

let rec _get_array (s : 'a array u) (i : int) : 'a =
  match s with
  | Leaf a ->
      a.(i)
  | Concat {lhs; rhs; _} ->
      let n = _length_array lhs in
      if i < n then _get_array lhs i else _get_array rhs (i - n)

let get_array (s : 'a array t) (i : int) : 'a = _get_array !s i

let rec _get_bigarray (s : ('a, 'b) ba u) (i : int) : 'a =
  match s with
  | Leaf a ->
      Array1.unsafe_get a i
  | Concat {lhs; rhs; _} ->
      let n = _length_bigarray lhs in
      if i < n then _get_bigarray lhs i else _get_bigarray rhs (i - n)

let get_bigarray (s : ('a, 'b) ba t) (i : int) : 'a = _get_bigarray !s i

let _collapse_array (s : 'a array t) : 'a array =
  let rec collapse dst s i =
    match s with
    | Leaf a ->
        let n = Array.length a in
        Array.blit a 0 dst i n ; i + n
    | Concat {lhs; rhs; _} ->
        collapse dst rhs (collapse dst lhs i)
  in
  match !s with
  | Leaf a ->
      a
  | Concat {len; _} ->
      (* NOTE(larshum, 2021-02-12): the implementation guarantees that Concat
       * nodes are non-empty. *)
      let dst = Array.make len (get_array s 0) in
      let _ = collapse dst !s 0 in
      s := Leaf dst ;
      dst

let _collapse_bigarray (s : ('a, 'b) ba t) : ('a, 'b) ba =
  let rec collapse dst s i =
    match s with
    | Leaf a ->
        let n = Array1.dim a in
        let dst_sub = Array1.sub dst i n in
        Array1.blit a dst_sub ; i + n
    | Concat {lhs; rhs; _} ->
        collapse dst rhs (collapse dst lhs i)
  in
  match !s with
  | Leaf a ->
      a
  | Concat {len; _} ->
      let dst = Array1.create (_bigarray_kind !s) c_layout len in
      let _ = collapse dst !s 0 in
      s := Leaf dst ;
      dst

let concat_array (l : 'a array t) (r : 'a array t) : 'a array t =
  let ln = length_array l in
  let rn = length_array r in
  if ln = 0 then r
  else if rn = 0 then l
  else ref (Concat {lhs= !l; rhs= !r; len= ln + rn})

let concat_bigarray (l : ('a, 'b) ba t) (r : ('a, 'b) ba t) : ('a, 'b) ba t =
  let ln = length_bigarray l in
  let rn = length_bigarray r in
  if ln = 0 then r
  else if rn = 0 then l
  else ref (Concat {lhs= !l; rhs= !r; len= ln + rn})

let set_array (s : 'a array t) (idx : int) (v : 'a) : 'a array t =
  let rec helper s i =
    match s with
    | Leaf a ->
        let a' = Array.copy a in
        a'.(i) <- v ; Leaf a'
    | Concat {lhs; rhs; len} ->
        let n = _length_array lhs in
        if i < n then Concat {lhs= helper lhs i; rhs; len}
        else Concat {lhs; rhs= helper rhs (i - n); len}
  in
  ref (helper !s idx)

let set_bigarray (s : ('a, 'b) ba t) (idx : int) (v : 'a) : ('a, 'b) ba t =
  let k = _bigarray_kind !s in
  let rec helper s i =
    match s with
    | Leaf a ->
        let n = Array1.dim a in
        let a' = _uninit_bigarray k n in
        Array1.blit a a' ; Array1.unsafe_set a' i v ; Leaf a'
    | Concat {lhs; rhs; len} ->
        let n = _length_bigarray lhs in
        if i < n then Concat {lhs= helper lhs i; rhs; len}
        else Concat {lhs; rhs= helper rhs (i - n); len}
  in
  ref (helper !s idx)

let cons_array (v : 'a) (s : 'a array t) : 'a array t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= Leaf [|v|]; rhs= !s; len= n + 1})

let cons_bigarray (v : 'a) (s : ('a, 'b) ba t) : ('a, 'b) ba t =
  let n = length_bigarray s in
  let a = _uninit_bigarray (_bigarray_kind !s) 1 in
  Array1.unsafe_set a 0 v ;
  if n = 0 then ref (Leaf a)
  else ref (Concat {lhs= Leaf a; rhs= !s; len= n + 1})

let snoc_array (s : 'a array t) (v : 'a) : 'a array t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= !s; rhs= Leaf [|v|]; len= n + 1})

let snoc_bigarray (s : ('a, 'b) ba t) (v : 'a) : ('a, 'b) ba t =
  let n = length_bigarray s in
  let a = _uninit_bigarray (_bigarray_kind !s) 1 in
  Array1.unsafe_set a 0 v ;
  if n = 0 then ref (Leaf a)
  else ref (Concat {lhs= Leaf a; rhs= !s; len= n + 1})

let split_at_array (s : 'a array t) (idx : int) : 'a array t * 'a array t =
  let n = length_array s in
  if idx = 0 then (empty_array, s)
  else if idx = n then (s, empty_array)
  else
    let fst = get_array s 0 in
    let lhs = Array.make idx fst in
    let rhs = Array.make (n - idx) fst in
    let rec fill s i =
      match s with
      | Leaf a ->
          let n = Array.length a in
          ( if i + n < idx then Array.blit a 0 lhs i n
          else if not (i < idx) then Array.blit a 0 rhs (i - idx) n
          else
            let lhs_copy_length = idx - i in
            Array.blit a 0 lhs i lhs_copy_length ;
            Array.blit a lhs_copy_length rhs 0 (n - lhs_copy_length) ) ;
          i + n
      | Concat {lhs; rhs; _} ->
          fill rhs (fill lhs i)
    in
    let _ = fill !s 0 in
    (ref (Leaf lhs), ref (Leaf rhs))

let split_at_bigarray (s : ('a, 'b) ba t) (idx : int) :
    ('a, 'b) ba t * ('a, 'b) ba t =
  let k = _bigarray_kind !s in
  let n = length_bigarray s in
  if idx = 0 then (_empty_bigarray k, s)
  else if idx = n then (s, _empty_bigarray k)
  else
    let lhs = _uninit_bigarray k idx in
    let rhs = _uninit_bigarray k (n - idx) in
    let rec fill s i =
      match s with
      | Leaf a ->
          let n = Array1.dim a in
          ( if i + n < idx then
            let dst = Array1.sub lhs i n in
            Array1.blit a dst
          else if not (i < idx) then
            let dst = Array1.sub rhs (i - idx) n in
            Array1.blit a dst
          else
            let lhs_copy_length = idx - i in
            let lsrc = Array1.sub a 0 lhs_copy_length in
            let rsrc = Array1.sub a lhs_copy_length (n - lhs_copy_length) in
            let ldst = Array1.sub lhs i lhs_copy_length in
            let rdst = Array1.sub rhs 0 (n - lhs_copy_length) in
            Array1.blit lsrc ldst ; Array1.blit rsrc rdst ) ;
          i + n
      | Concat {lhs; rhs; _} ->
          fill rhs (fill lhs i)
    in
    let _ = fill !s 0 in
    (ref (Leaf lhs), ref (Leaf rhs))

let sub_array (s : 'a array t) (from : int) (len : int) : 'a array t =
  let n = length_array s in
  if n = 0 then empty_array
  else
    let dst = Array.make len (get_array s 0) in
    let rec fill s i =
      match s with
      | Leaf a ->
          let n = Array.length a in
          let src_offset = max (from - i) 0 in
          let dst_offset = max (i - from) 0 in
          let copy_len = min (n - src_offset) (len - dst_offset) in
          Array.blit a src_offset dst dst_offset copy_len ;
          i + n
      | Concat {lhs; rhs; _} ->
          let n = _length_array lhs in
          if i + n < from then fill rhs (i + n)
          else if from + len < i + n then fill lhs i
          else fill rhs (fill lhs i)
    in
    let _ = fill !s 0 in
    ref (Leaf dst)

let sub_bigarray (s : ('a, 'b) ba t) (from : int) (len : int) : ('a, 'b) ba t =
  let k = _bigarray_kind !s in
  let dst = _uninit_bigarray k len in
  let rec fill s i =
    match s with
    | Leaf a ->
        let n = Array1.dim a in
        let src_offset = max (from - i) 0 in
        let dst_offset = max (i - from) 0 in
        let copy_len = min (n - src_offset) (len - dst_offset) in
        let src_sub = Array1.sub a src_offset copy_len in
        let dst_sub = Array1.sub dst dst_offset copy_len in
        Array1.blit src_sub dst_sub ;
        i + n
    | Concat {lhs; rhs; _} ->
        let n = _length_bigarray lhs in
        if i + n < from then fill rhs (i + n)
        else if from + len < i + n then fill lhs i
        else fill rhs (fill lhs i)
  in
  let _ = fill !s 0 in
  ref (Leaf dst)

let map_array_array (f : 'a -> 'b) (s : 'a array t) : 'b array t =
  let a = _collapse_array s in
  ref (Leaf (Array.map f a))

let map_array_bigarray (k : ('b, 'c) kind) (f : 'a -> 'b) (s : 'a array t) :
    ('b, 'c) ba t =
  let a = _collapse_array s in
  let n = Array.length a in
  let dst = _uninit_bigarray k n in
  for i = 0 to n - 1 do
    Array1.unsafe_set dst i (f a.(i))
  done ;
  ref (Leaf dst)

let map_bigarray_array (f : 'a -> 'b) (s : ('a, 'c) ba t) : 'b array t =
  let a = _collapse_bigarray s in
  let n = Array1.dim a in
  if n = 0 then ref (Leaf [||])
  else
    let dst = Array.make n (f (Array1.unsafe_get a 0)) in
    for i = 0 to n - 1 do
      dst.(i) <- f (Array1.unsafe_get a i)
    done ;
    ref (Leaf dst)

let map_bigarray_bigarray (k : ('b, 'd) kind) (f : 'a -> 'b)
    (s : ('a, 'c) ba t) : ('b, 'd) ba t =
  let a = _collapse_bigarray s in
  let n = Array1.dim a in
  let dst = _uninit_bigarray k n in
  for i = 0 to n - 1 do
    Array1.unsafe_set dst i (f (Array1.unsafe_get a i))
  done ;
  ref (Leaf dst)

let foldl_array (f : 'a -> 'b -> 'a) (acc : 'a) (s : 'b array t) : 'a =
  let a = _collapse_array s in
  Array.fold_left f acc a

let foldl_bigarray (f : 'a -> 'b -> 'a) (acc : 'a) (s : ('b, 'c) ba t) : 'a =
  let a = _collapse_bigarray s in
  let r = ref acc in
  let n = Array1.dim a in
  for i = 0 to n - 1 do
    r := f !r (Array1.unsafe_get a i)
  done ;
  !r

let reverse_array (s : 'a array t) : 'a array t =
  let a = _collapse_array s in
  let a' = Array.copy a in
  let n = Array.length a' in
  for i = 0 to n - 1 do
    a'.(i) <- a.(n - i - 1)
  done ;
  ref (Leaf a')

let reverse_bigarray (s : ('a, 'b) ba t) : ('a, 'b) ba t =
  let a = _collapse_bigarray s in
  let n = Array1.dim a in
  let a' = _uninit_bigarray (_bigarray_kind !s) n in
  for i = 0 to n - 1 do
    Array1.unsafe_set a' i (Array1.unsafe_get a (n - i - 1))
  done ;
  ref (Leaf a')

let combine_array_array (l : 'a array t) (r : 'b array t) : ('a * 'b) array t =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    ref (Leaf (Array.map2 (fun x y -> (x, y)) a1 a2))

let combine_array_bigarray (l : 'a array t) (r : ('b, 'c) ba t) :
    ('a * 'b) array t =
  let ln = length_array l in
  let rn = length_bigarray r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else if ln = 0 then empty_array
  else
    let a1, a2 = (_collapse_array l, _collapse_bigarray r) in
    let dst = Array.make ln (a1.(0), Array1.unsafe_get a2 0) in
    for i = 0 to ln - 1 do
      dst.(i) <- (a1.(i), Array1.unsafe_get a2 i)
    done ;
    ref (Leaf dst)

let combine_bigarray_array (l : ('a, 'c) ba t) (r : 'b array t) :
    ('a * 'b) array t =
  let ln = length_bigarray l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else if ln = 0 then empty_array
  else
    let a1, a2 = (_collapse_bigarray l, _collapse_array r) in
    let dst = Array.make ln (Array1.unsafe_get a1 0, a2.(0)) in
    for i = 0 to ln - 1 do
      dst.(i) <- (Array1.unsafe_get a1 i, a2.(i))
    done ;
    ref (Leaf dst)

let combine_bigarray_bigarray (l : ('a, 'c) ba t) (r : ('b, 'd) ba t) :
    ('a * 'b) array t =
  let ln = length_bigarray l in
  let rn = length_bigarray r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else if ln = 0 then empty_array
  else
    let a1, a2 = (_collapse_bigarray l, _collapse_bigarray r) in
    let dst = Array.make ln (Array1.unsafe_get a1 0, Array1.unsafe_get a2 0) in
    for i = 0 to ln - 1 do
      dst.(i) <- (Array1.unsafe_get a1 i, Array1.unsafe_get a2 i)
    done ;
    ref (Leaf dst)

let equal_array (f : 'a -> 'a -> bool) (l : 'a array t) (r : 'a array t) : bool
    =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then false
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    let r = ref true in
    Array.iter2 (fun x y -> if f x y then () else r := false) a1 a2 ;
    !r

let equal_bigarray (f : 'a -> 'a -> bool) (l : ('a, 'b) ba t)
    (r : ('a, 'b) ba t) : bool =
  let ln = length_bigarray l in
  let rn = length_bigarray r in
  if ln != rn then false
  else
    let a1, a2 = (_collapse_bigarray l, _collapse_bigarray r) in
    let r = ref true in
    for i = 0 to ln - 1 do
      if f (Array1.unsafe_get a1 i) (Array1.unsafe_get a2 i) then ()
      else r := false
    done ;
    !r

let foldr_array (f : 'a -> 'b -> 'b) (s : 'a array t) (acc : 'b) : 'b =
  let a = _collapse_array s in
  Array.fold_right f a acc

let foldr_bigarray (f : 'a -> 'b -> 'b) (s : ('a, 'c) ba t) (acc : 'b) : 'b =
  let a = _collapse_bigarray s in
  let n = Array1.dim a in
  let r = ref acc in
  for i = n - 1 downto 0 do
    r := f (Array1.unsafe_get a i) !r
  done ;
  !r

let foldr2_array (f : 'a -> 'b -> 'c -> 'c) (l : 'a array t) (r : 'b array t)
    (acc : 'c) : 'c =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.foldr2")
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    let r = ref acc in
    for i = ln - 1 downto 0 do
      r := f a1.(i) a2.(i) !r
    done ;
    !r

let foldr2_bigarray (f : 'a -> 'b -> 'c -> 'c) (l : ('a, 'd) ba t)
    (r : ('b, 'e) ba t) (acc : 'c) : 'c =
  let ln = length_bigarray l in
  let rn = length_bigarray r in
  if ln != rn then raise (Invalid_argument "Rope.foldr2")
  else
    let a1, a2 = (_collapse_bigarray l, _collapse_bigarray r) in
    let r = ref acc in
    for i = ln - 1 downto 0 do
      r := f (Array1.unsafe_get a1 i) (Array1.unsafe_get a2 i) !r
    done ;
    !r

module Convert = struct
  let to_array_array (s : 'a array t) : 'a array = _collapse_array s

  let to_array_bigarray (s : ('a, 'b) ba t) : 'a array =
    let a = _collapse_bigarray s in
    let n = Array1.dim a in
    if n = 0 then [||]
    else
      let dst = Array.make n (Array1.unsafe_get a 0) in
      for i = 0 to n - 1 do
        dst.(i) <- Array1.unsafe_get a i
      done ;
      dst

  let of_array_array (a : 'a array) : 'a array t = ref (Leaf a)

  let of_array_int_bigarray (a : int array) : int_ba t =
    let n = Array.length a in
    let dst = _uninit_bigarray Int n in
    for i = 0 to n - 1 do
      Array1.unsafe_set dst i a.(i)
    done ;
    ref (Leaf dst)

  let of_array_float_bigarray (a : float array) : float_ba t =
    let n = Array.length a in
    let dst = _uninit_bigarray Float64 n in
    for i = 0 to n - 1 do
      Array1.unsafe_set dst i a.(i)
    done ;
    ref (Leaf dst)

  let to_list_array (s : 'a array t) : 'a list =
    Array.to_list (to_array_array s)

  let to_list_bigarray (s : ('a, 'b) ba t) : 'a list =
    Array.to_list (to_array_bigarray s)

  let of_list_array (l : 'a list) : 'a array t =
    of_array_array (Array.of_list l)

  let of_list_int_bigarray (l : int list) : int_ba t =
    of_array_int_bigarray (Array.of_list l)

  let of_list_float_bigarray (l : float list) : float_ba t =
    of_array_float_bigarray (Array.of_list l)

  let to_ustring_array (s : int array t) : ustring =
    array2ustring (to_array_array s)

  let to_ustring_bigarray (s : int_ba t) : ustring =
    array2ustring (to_array_bigarray s)

  let of_ustring_array (u : ustring) : int array t =
    of_array_array (ustring2array u)

  let of_ustring_bigarray (u : ustring) : int_ba t =
    of_array_int_bigarray (ustring2array u)

  let to_int_bigarray_array (s : int array t) : int_ba =
    _collapse_bigarray (map_array_bigarray Int (fun x -> x) s)

  let to_int_bigarray_bigarray (s : int_ba t) : int_ba = _collapse_bigarray s

  let to_float_bigarray_array (s : float array t) : float_ba =
    _collapse_bigarray (map_array_bigarray Float64 (fun x -> x) s)

  let to_float_bigarray_bigarray (s : float_ba t) : float_ba =
    _collapse_bigarray s
end
