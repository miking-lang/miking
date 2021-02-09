open Bigarray
open Ustring.Op

type kind = Array | IntBigarray | FloatBigarray | Unknown

type 'a u =
  | Concat of {lhs: 'a u; rhs: 'a u; len: int}
  | Leaf of Obj.t
  | Empty

type 'a t = {v: 'a u ref; k: kind}

type collapsed = {a: Obj.t; k: kind}

let infer_kind (v : 'a) : kind =
  let tag = Obj.tag (Obj.repr v) in
  if tag = Obj.int_tag then IntBigarray
  else if tag = Obj.double_tag then FloatBigarray
  else Array

let uninit_bigarray (k : kind) (n : int) : Obj.t =
  match k with
  | IntBigarray ->
      Obj.repr (Array1.create Int c_layout n)
  | FloatBigarray ->
      Obj.repr (Array1.create Float64 c_layout n)
  | Array ->
      failwith "Got Array kind in uninit_bigarray"
  | Unknown ->
      failwith "Got Unknown kind in uninit_bigarray"

let init (n : int) (v : 'a) : Obj.t =
  let k = infer_kind v in
  match k with
  | Array ->
      Obj.repr (Array.make n v)
  | _ ->
      let a = uninit_bigarray k n in
      Array1.fill (Obj.obj a) (Obj.magic v) ;
      Obj.repr a

let make (n : int) (v : 'a) : 'a t =
  let k = infer_kind v in
  {v= ref (Leaf (init n v)); k}

let empty = Obj.magic {v= ref Empty; k= Unknown}

let length_array (s : 'a u) : int =
  match s with
  | Concat {len; _} ->
      len
  | Leaf a ->
      Array.length (Obj.obj a)
  | Empty ->
      0

let length_bigarray (s : 'a u) : int =
  match s with
  | Concat {len; _} ->
      len
  | Leaf a ->
      Array1.dim (Obj.obj a)
  | Empty ->
      0

let length (s : 'a t) : int =
  let {v; k} = s in
  match k with
  | Array ->
      length_array !v
  | Unknown ->
      0
  | _ ->
      length_bigarray !v

let rec get_array (s : 'a u) (idx : int) : 'a =
  match s with
  | Concat {lhs; rhs; _} ->
      let n = length_array lhs in
      if idx < n then get_array lhs idx else get_array rhs (idx - n)
  | Leaf a ->
      (Obj.obj a).(idx)
  | Empty ->
      failwith "get_array: index out of range"

let collapse_array (s : 'a u) : Obj.t =
  match s with
  | Concat {len; _} ->
      let fst = get_array s 0 in
      let dst = Array.make len fst in
      let rec fill_dst s idx =
        match s with
        | Concat {lhs; rhs; _} ->
            fill_dst rhs (fill_dst lhs idx)
        | Leaf src ->
            let n = Array.length (Obj.obj src) in
            Array.blit (Obj.obj src) 0 dst idx n ;
            idx + n
        | Empty ->
            idx
      in
      let _ = fill_dst s 0 in
      Obj.repr dst
  | Leaf a ->
      Obj.repr (Array.copy (Obj.obj a))
  | Empty ->
      Obj.repr [||]

let collapse_bigarray (k : kind) (s : 'a u) : Obj.t =
  let n = length_bigarray s in
  match s with
  | Concat _ ->
      let dst = uninit_bigarray k n in
      let rec fill_dst s idx =
        match s with
        | Concat {lhs; rhs; _} ->
            fill_dst rhs (fill_dst lhs idx)
        | Leaf src ->
            let n = Array1.dim (Obj.obj src) in
            let dst_sub = Array1.sub (Obj.obj dst) idx n in
            Array1.blit (Obj.obj src) dst_sub ;
            idx + n
        | Empty ->
            idx
      in
      let _ = fill_dst s 0 in
      dst
  | Leaf a ->
      let acpy = uninit_bigarray k n in
      Array1.blit (Obj.obj a) (Obj.obj acpy) ;
      acpy
  | Empty ->
      uninit_bigarray k 0

let collapse (s : 'a t) : collapsed =
  let {v; k} = s in
  match (!v, k) with
  | Leaf a, _ ->
      {a; k}
  | v', Array ->
      let a = collapse_array v' in
      v := Leaf a ;
      {a; k}
  | _, Unknown ->
      {a= Obj.repr [||]; k}
  | v', _ ->
      let a = collapse_bigarray k v' in
      v := Leaf a ;
      {a; k}

let concat (a : 'a t) (b : 'a t) : 'a t =
  let {a= a1; k= k1}, {a= a2; k= k2} = (collapse a, collapse b) in
  match (k1, k2) with
  | Array, Array ->
      let len = Array.length (Obj.obj a1) + Array.length (Obj.obj a2) in
      {v= ref (Concat {lhs= Leaf a1; rhs= Leaf a2; len}); k= k1}
  | IntBigarray, IntBigarray | FloatBigarray, FloatBigarray ->
      let len = Array1.dim (Obj.obj a1) + Array1.dim (Obj.obj a2) in
      {v= ref (Concat {lhs= Leaf a1; rhs= Leaf a2; len}); k= k1}
  | _, Unknown ->
      {v= ref (Leaf a1); k= k1}
  | Unknown, _ ->
      {v= ref (Leaf a2); k= k2}
  | _ ->
      failwith "concat: arrays of different types"

let rec get_bigarray (s : 'a u) (idx : int) : 'a =
  match s with
  | Concat {lhs; rhs; _} ->
      let n = length_bigarray lhs in
      if idx < n then get_bigarray lhs idx else get_bigarray rhs (idx - n)
  | Leaf a ->
      Array1.unsafe_get (Obj.obj a) idx
  | Empty ->
      failwith "get_bigarray: index out of range"

let get (s : 'a t) (idx : int) : 'a =
  let {a; k} = collapse s in
  match k with
  | Array ->
      get_array (Leaf a) idx
  | Unknown ->
      failwith "get: unknown array type"
  | _ ->
      get_bigarray (Leaf a) idx

let get_collapsed (s : collapsed) (idx : int) : 'a =
  let {a; k} = s in
  match k with
  | Array ->
      (Obj.obj a).(idx)
  | Unknown ->
      failwith "get_collapsed: applied on value of kind Unknown"
  | _ ->
      Array1.unsafe_get (Obj.obj a) idx

let set (s : 'a t) (idx : int) (v : 'a) : 'a t =
  let {a; k} = collapse s in
  let _ =
    match k with
    | Array ->
        (Obj.obj a).(idx) <- v
    | _ ->
        Array1.unsafe_set (Obj.obj a) idx v
  in
  {v= ref (Leaf a); k}

let cons (v : 'a) (s : 'a t) : 'a t =
  let {v= v2; k} = s in
  let singleton = Leaf (init 1 v) in
  let v' = Concat {lhs= singleton; rhs= !v2; len= length s + 1} in
  match k with
  | Unknown ->
      let elem_kind = infer_kind v in
      {v= ref v'; k= elem_kind}
  | k ->
      {v= ref v'; k}

let snoc (s : 'a t) (v : 'a) : 'a t =
  let {v= v2; k} = s in
  let singleton = Leaf (init 1 v) in
  let v' = Concat {lhs= !v2; rhs= singleton; len= length s + 1} in
  match k with
  | Unknown ->
      let elem_kind = infer_kind v in
      {v= ref v'; k= elem_kind}
  | k ->
      {v= ref v'; k}

let split_at_array (s : 'a u) (idx : int) : 'a u * 'a u =
  let fst = get_array s 0 in
  let lhs = Array.make idx fst in
  let rhs = Array.make (length_array s - idx) fst in
  let rec fill_dst s dstidx =
    match s with
    | Concat {lhs; rhs; _} ->
        fill_dst rhs (fill_dst lhs dstidx)
    | Leaf a ->
        let n = Array.length (Obj.obj a) in
        let _ =
          if dstidx + n < idx then Array.blit (Obj.obj a) 0 lhs dstidx n
          else if not (dstidx < idx) then
            Array.blit (Obj.obj a) 0 rhs (dstidx - idx) n
          else
            let lhs_copy_length = idx - dstidx in
            Array.blit (Obj.obj a) 0 lhs dstidx lhs_copy_length ;
            Array.blit (Obj.obj a) lhs_copy_length rhs 0 (n - lhs_copy_length)
        in
        dstidx + n
    | Empty ->
        dstidx
  in
  let _ = fill_dst s 0 in
  (Leaf (Obj.repr lhs), Leaf (Obj.repr rhs))

let split_at_bigarray (k : kind) (s : 'a u) (idx : int) : 'a u * 'a u =
  let lhs = uninit_bigarray k idx in
  let rhs = uninit_bigarray k (length_bigarray s - idx) in
  let rec fill_dst s dstidx =
    match s with
    | Concat {lhs; rhs; _} ->
        fill_dst rhs (fill_dst lhs dstidx)
    | Leaf a ->
        let n = Array1.dim (Obj.obj a) in
        let _ =
          if dstidx + n < idx then
            let dst = Array1.sub (Obj.obj lhs) dstidx (n - dstidx) in
            Array1.blit (Obj.obj a) dst
          else if not (dstidx < idx) then
            let dst =
              Array1.sub (Obj.obj rhs) (dstidx - idx) (n - (dstidx - idx))
            in
            Array1.blit (Obj.obj a) dst
          else
            let lhs_copy_length = idx - dstidx in
            let lhsSrcSlice = Array1.sub (Obj.obj a) 0 lhs_copy_length in
            let lhsDstSlice =
              Array1.sub (Obj.obj lhs) dstidx lhs_copy_length
            in
            let rhsSrcSlice =
              Array1.sub (Obj.obj a) lhs_copy_length (n - lhs_copy_length)
            in
            let rhsDstSlice =
              Array1.sub (Obj.obj rhs) 0 (n - lhs_copy_length)
            in
            Array1.blit lhsSrcSlice lhsDstSlice ;
            Array1.blit rhsSrcSlice rhsDstSlice
        in
        dstidx + n
    | Empty ->
        dstidx
  in
  let _ = fill_dst s 0 in
  (Leaf lhs, Leaf rhs)

let split_at (s : 'a t) (idx : int) : 'a t * 'a t =
  let {v; k} = s in
  if idx = 0 then (empty, s)
  else if idx = length s then (s, empty)
  else
    let lhs, rhs =
      match k with
      | Array ->
          split_at_array !v idx
      | _ ->
          split_at_bigarray k !v idx
    in
    ({v= ref lhs; k}, {v= ref rhs; k})

let sub_array (s : 'a u) (fromidx : int) (toidx : int) : 'a u =
  let len = toidx - fromidx in
  let v = get_array s fromidx in
  let sub = Array.make len v in
  let rec fill_dst s dstidx =
    match s with
    | Concat {lhs; rhs; _} ->
        fill_dst rhs (fill_dst lhs dstidx)
    | Leaf a ->
        let n = Array.length (Obj.obj a) in
        let src_offset = if dstidx < fromidx then fromidx - dstidx else 0 in
        let copy_length = min (n - src_offset) len in
        Array.blit (Obj.obj a) src_offset sub dstidx copy_length ;
        dstidx + n
    | Empty ->
        dstidx
  in
  let _ = fill_dst s 0 in
  Leaf (Obj.repr sub)

let sub_bigarray (k : kind) (s : 'a u) (fromidx : int) (toidx : int) : 'a u =
  let len = toidx - fromidx in
  let sub = uninit_bigarray k len in
  let rec fill_dst s dstidx =
    match s with
    | Concat {lhs; rhs; _} ->
        fill_dst rhs (fill_dst lhs dstidx)
    | Leaf a ->
        let n = Array1.dim (Obj.obj a) in
        let src_offset = if dstidx < fromidx then fromidx - dstidx else 0 in
        let copy_length = min (n - src_offset) len in
        let src = Array1.sub (Obj.obj a) src_offset copy_length in
        let dst = Array1.sub (Obj.obj sub) dstidx copy_length in
        Array1.blit src dst ; dstidx + n
    | Empty ->
        dstidx
  in
  let _ = fill_dst s 0 in
  Leaf (Obj.repr sub)

let sub (s : 'a t) (fromidx : int) (toidx : int) : 'a t =
  let {v; k} = s in
  let sub_res =
    match k with
    | Array ->
        sub_array !v fromidx toidx
    | IntBigarray | FloatBigarray ->
        sub_bigarray k !v fromidx toidx
    | Unknown ->
        failwith "sub: cannot construct subarray of unknown"
  in
  {v= ref sub_res; k}

let map_array_array (f : 'a -> 'b) (src : Obj.t) : 'b u =
  Leaf (Obj.repr (Array.map f (Obj.obj src)))

let map_array_bigarray (f : 'a -> 'b) (src : Obj.t) (dst : Obj.t) : 'b u =
  let n = Array.length (Obj.obj src) in
  for i = 0 to n - 1 do
    Array1.unsafe_set (Obj.obj dst) i (f (Obj.obj src).(i))
  done ;
  Leaf dst

let map_bigarray_array (f : 'a -> 'b) (src : Obj.t) (dst : Obj.t) : 'b u =
  let n = Array1.dim (Obj.obj src) in
  for i = 0 to n - 1 do
    (Obj.obj dst).(i) <- f (Array1.unsafe_get (Obj.obj src) i)
  done ;
  Leaf dst

let map_bigarray_bigarray (f : 'a -> 'b) (src : Obj.t) (dst : Obj.t) : 'b u =
  let n = Array1.dim (Obj.obj src) in
  for i = 0 to n - 1 do
    Array1.unsafe_set (Obj.obj dst) i (f (Array1.unsafe_get (Obj.obj src) i))
  done ;
  Leaf dst

let infer_output_kind (f : 'a -> 'b) (s : 'a t) : kind =
  if length s = 0 then Unknown
  else
    let fst = get s 0 in
    infer_kind (f fst)

let map (f : 'a -> 'b) (s : 'a t) : 'b t =
  let output_kind = infer_output_kind f s in
  let {a; k= input_kind} = collapse s in
  let n = length s in
  let value =
    match (input_kind, output_kind) with
    | Array, Array ->
        map_array_array f a
    | Array, _ ->
        map_array_bigarray f a (Obj.repr (uninit_bigarray output_kind n))
    | IntBigarray, Array | FloatBigarray, Array ->
        map_bigarray_array f a (Obj.repr (Array.make n (get s 0)))
    | IntBigarray, IntBigarray
    | IntBigarray, FloatBigarray
    | FloatBigarray, IntBigarray
    | FloatBigarray, FloatBigarray ->
        map_bigarray_bigarray f a (Obj.repr (uninit_bigarray output_kind n))
    | Unknown, Unknown ->
        Empty
    | _ ->
        failwith "Rope.map: internal error"
  in
  {v= ref value; k= output_kind}

let foldl_array (f : 'a -> 'b -> 'a) (acc : 'a) (src : Obj.t) : 'a =
  Array.fold_left f acc (Obj.obj src)

let foldl_bigarray (f : 'a -> 'b -> 'a) (acc : 'a) (src : Obj.t) : 'a =
  let n = Array1.dim (Obj.obj src) in
  let acc = ref acc in
  for i = 0 to n - 1 do
    acc := f !acc (Array1.unsafe_get (Obj.obj src) i)
  done ;
  !acc

let foldl (f : 'a -> 'b -> 'a) (acc : 'a) (s : 'b t) : 'a =
  let {a; k} = collapse s in
  match k with
  | Unknown ->
      acc
  | Array ->
      foldl_array f acc a
  | _ ->
      foldl_bigarray f acc a

let reverse_array (src : 'a array) : 'a u =
  let n = Array.length src in
  for i = 0 to (n / 2) - 1 do
    let tmp = src.(i) in
    src.(i) <- src.(n - i - 1) ;
    src.(n - i - 1) <- tmp
  done ;
  Leaf (Obj.repr src)

let reverse_bigarray (src : Obj.t) : 'a u =
  let n = Array1.dim (Obj.obj src) in
  for i = 0 to (n / 2) - 1 do
    let i2 = n - i - 1 in
    let tmp = Array1.unsafe_get (Obj.obj src) i in
    let _ =
      Array1.unsafe_set (Obj.obj src) i (Array1.unsafe_get (Obj.obj src) i2)
    in
    Array1.unsafe_set (Obj.obj src) i2 tmp
  done ;
  Leaf src

let reverse (s : 'a t) : 'a t =
  let n = length s in
  if n < 2 then s
  else
    let {a; k} = collapse s in
    let v =
      match k with
      | Array ->
          ref (reverse_array (Obj.obj a))
      | IntBigarray | FloatBigarray ->
          ref (reverse_bigarray a)
      | _ ->
          failwith "reverse: invalid kind"
    in
    {v; k}

let combine (l : 'a t) (r : 'b t) : ('a * 'b) t =
  let n = length l in
  if n != length r then failwith "combine: sequences of different lengths"
  else if n = 0 then {v= ref Empty; k= Unknown}
  else
    let c1, c2 = (collapse l, collapse r) in
    let a = Array.make n (get_collapsed c1 0, get_collapsed c2 0) in
    for i = 1 to n - 1 do
      a.(i) <- (get_collapsed c1 i, get_collapsed c2 i)
    done ;
    {v= ref (Leaf (Obj.repr a)); k= Array}

let equal (f : 'a -> 'a -> bool) (l : 'a t) (r : 'a t) : bool =
  let n = length l in
  if n != length r then false
  else
    let c1, c2 = (collapse l, collapse r) in
    let r = ref true in
    for i = 0 to n - 1 do
      if f (get_collapsed c1 i) (get_collapsed c2 i) then () else r := false
    done ;
    !r

let foldr (f : 'a -> 'b -> 'b) (s : 'a t) (acc : 'b) : 'b =
  let n = length s in
  let c = collapse s in
  let r = ref acc in
  for i = n - 1 downto 0 do
    r := f (get_collapsed c i) !r
  done ;
  !r

let foldr2 (f : 'a -> 'b -> 'c -> 'c) (l : 'a t) (r : 'b t) (acc : 'c) : 'c =
  let n = length l in
  if n != length r then failwith "foldr2: sequences of different length"
  else
    let c1, c2 = (collapse l, collapse r) in
    let r = ref acc in
    for i = n - 1 downto 0 do
      r := f (get_collapsed c1 i) (get_collapsed c2 i) !r
    done ;
    !r

module Convert = struct
  let to_array (s : 'a t) : 'a array =
    let {a; k} = collapse s in
    match k with
    | Unknown ->
        [||]
    | Array ->
        Obj.obj a
    | _ ->
        let n = Array1.dim (Obj.obj a) in
        let a' = Array.make n (Array1.unsafe_get (Obj.obj a) 0) in
        for i = 1 to n - 1 do
          a'.(i) <- Array1.unsafe_get (Obj.obj a) i
        done ;
        a'

  let of_array (a : 'a array) : 'a t =
    if Array.length a = 0 then {v= ref Empty; k= Unknown}
    else
      let k = infer_kind a.(0) in
      let v =
        match k with
        | Array ->
            ref (Leaf (Obj.repr a))
        | IntBigarray ->
            ref (Leaf (Obj.repr (Array1.of_array Int c_layout (Obj.magic a))))
        | FloatBigarray ->
            ref
              (Leaf (Obj.repr (Array1.of_array Float64 c_layout (Obj.magic a))))
        | _ ->
            failwith "of_array: unsupported source type"
      in
      {v; k}

  let to_list (s : 'a t) : 'a list = Array.to_list (to_array s)

  let of_list (l : 'a list) : 'a t = of_array (Array.of_list l)

  let to_ustring (s : int t) : ustring = array2ustring (to_array s)

  let of_ustring (u : ustring) : int t = of_array (ustring2array u)
end
