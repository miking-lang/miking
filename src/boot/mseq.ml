type 'a t = 'a BatFingerTree.t

let of_list = BatFingerTree.of_list
let to_list = BatFingerTree.to_list
let of_array a = of_list (Array.to_list a)
let to_array s = Array.of_list (to_list s)
let of_ustring u = of_list (Ustring.Op.ustring2list u)
let to_ustring s = Ustring.Op.list2ustring (to_list s)

let make n f = of_list (List.init n f)
let empty = BatFingerTree.empty
let length = BatFingerTree.size
let concat = BatFingerTree.append
let get = BatFingerTree.get
let set = BatFingerTree.set
let cons e s = BatFingerTree.cons s e
let snoc = BatFingerTree.snoc
let reverse = BatFingerTree.reverse

let split_at s n =
  if n == 0 then
    (empty, s)                                              (* O(1) *)
  else if n == 1 then
    (BatFingerTree.singleton (BatFingerTree.head_exn s),
     BatFingerTree.tail_exn s)                              (* Amortized O(1) *)
  else if n == length s - 1 then
    (BatFingerTree.init_exn s,
     BatFingerTree.singleton (BatFingerTree.last_exn s))    (* Amortized O(1) *)
  else if n == length s then
    (s, empty)                                              (* O(1) *)
  else
    BatFingerTree.split_at s n                              (* O(log n) *)

let equal = BatFingerTree.equal

let map = BatFingerTree.map
let fold_right f s a = BatFingerTree.fold_right (fun a x -> f x a) a s

let combine s1 s2 =
  let rec work a s1 s2 =
    if length s1 == 0 then a
    else work (snoc a (BatFingerTree.head_exn s1, BatFingerTree.head_exn s2))
           (BatFingerTree.tail_exn s1) (BatFingerTree.tail_exn s2)
  in
  if length s1 != length s2 then
    raise (Invalid_argument "sequences of different length")
  else work empty s1 s2

let fold_right2 f s1 s2 a =
  fold_right (fun x a -> f (fst x) (snd x) a) (combine s1 s2) a
