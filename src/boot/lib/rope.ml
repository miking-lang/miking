open Ustring.Op

(* The tree of a rope is either a Leaf or a Concat node.

   A Leaf node consists of an element container. They represent a part of the
   sequence.

   A Concat node represents the concatentation of two ropes. It contains the
   two recursive tree structures and a length field corresponding to the
   combined length of the two ropes, so that we can look up the length in
   constant time. *)
type 'a u = Leaf of 'a array | Concat of {lhs: 'a u; rhs: 'a u; len: int}

(* A rope is represented as a reference to its tree data structure. This lets
   us collapse the tree before performing an operation on it, which in turn
   allows constant time concatenation. *)
type 'a t = 'a u ref

let create_array (n : int) (f : int -> 'a) : 'a t = ref (Leaf (Array.init n f))

let empty_array = Obj.magic (ref (Leaf [||]))

let _length_array (s : 'a u) : int =
  match s with Leaf a -> Array.length a | Concat {len; _} -> len

let length_array (s : 'a t) : int = _length_array !s

let rec _get_array (s : 'a u) (i : int) : 'a =
  match s with
  | Leaf a ->
      a.(i)
  | Concat {lhs; rhs; _} ->
      let n = _length_array lhs in
      if i < n then _get_array lhs i else _get_array rhs (i - n)

let get_array (s : 'a t) (i : int) : 'a = _get_array !s i

let _collapse_array (s : 'a t) : 'a array =
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

let concat_array (l : 'a t) (r : 'a t) : 'a t =
  let ln = length_array l in
  let rn = length_array r in
  if ln = 0 then r
  else if rn = 0 then l
  else ref (Concat {lhs= !l; rhs= !r; len= ln + rn})

let set_array (s : 'a t) (idx : int) (v : 'a) : 'a t =
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

let cons_array (v : 'a) (s : 'a t) : 'a t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= Leaf [|v|]; rhs= !s; len= n + 1})

let snoc_array (s : 'a t) (v : 'a) : 'a t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= !s; rhs= Leaf [|v|]; len= n + 1})

let split_at_array (s : 'a t) (idx : int) : 'a t * 'a t =
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

let sub_array (s : 'a t) (off : int) (cnt : int) : 'a t =
  let n = length_array s in
  if n = 0 then empty_array
  else
    let cnt = min (n - off) cnt in
    let dst = Array.make cnt (get_array s 0) in
    let rec fill s i =
      match s with
      | Leaf a ->
          let n = Array.length a in
          let src_offset = max (off - i) 0 in
          let dst_offset = max (i - off) 0 in
          let copy_len = min (n - src_offset) (cnt - dst_offset) in
          Array.blit a src_offset dst dst_offset copy_len ;
          i + n
      | Concat {lhs; rhs; _} ->
          let n = _length_array lhs in
          if i + n < off then fill rhs (i + n)
          else if off + cnt < i + n then fill lhs i
          else fill rhs (fill lhs i)
    in
    let _ = fill !s 0 in
    ref (Leaf dst)

let iter_array (f : 'a -> unit) (s : 'a t) : unit =
  let rec iter = function
    | Leaf a ->
        Array.iter f a
    | Concat {lhs; rhs; _} ->
        iter lhs ; iter rhs
  in
  iter !s

let iteri_array (f : int -> 'a -> unit) (s : 'a t) : unit =
  let rec iteri off = function
    | Leaf a ->
        Array.iteri (fun i e -> f (i + off) e) a ;
        Array.length a
    | Concat {lhs; rhs; _} ->
        let n = iteri off lhs in
        iteri (off + n) rhs
  in
  iteri 0 !s |> ignore

let map_array_array (f : 'a -> 'b) (s : 'a t) : 'b t =
  let a = _collapse_array s in
  ref (Leaf (Array.map f a))

let mapi_array_array (f : int -> 'a -> 'b) (s : 'a t) : 'b t =
  let a = _collapse_array s in
  ref (Leaf (Array.mapi f a))

let foldl_array (f : 'a -> 'b -> 'a) (acc : 'a) (s : 'b t) : 'a =
  let a = _collapse_array s in
  Array.fold_left f acc a

let reverse_array (s : 'a t) : 'a t =
  let a = _collapse_array s in
  let a' = Array.copy a in
  let n = Array.length a' in
  for i = 0 to n - 1 do
    a'.(i) <- a.(n - i - 1)
  done ;
  ref (Leaf a')

let combine_array_array (l : 'a t) (r : 'b t) : ('a * 'b) t =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    ref (Leaf (Array.map2 (fun x y -> (x, y)) a1 a2))

let equal_array (f : 'a -> 'a -> bool) (l : 'a t) (r : 'a t) : bool =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then false
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    let r = ref true in
    Array.iter2 (fun x y -> if f x y then () else r := false) a1 a2 ;
    !r

let foldr_array (f : 'a -> 'b -> 'b) (s : 'a t) (acc : 'b) : 'b =
  let a = _collapse_array s in
  Array.fold_right f a acc

let foldr2_array (f : 'a -> 'b -> 'c -> 'c) (l : 'a t) (r : 'b t) (acc : 'c) :
    'c =
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

module Convert = struct
  let to_array_array (s : 'a t) : 'a array = _collapse_array s

  let of_array_array (a : 'a array) : 'a t = ref (Leaf a)

  let to_list_array (s : 'a t) : 'a list = Array.to_list (to_array_array s)

  let of_list_array (l : 'a list) : 'a t = of_array_array (Array.of_list l)

  let to_ustring_array (s : int t) : ustring = array2ustring (to_array_array s)

  let of_ustring_array (u : ustring) : int t = of_array_array (ustring2array u)
end
