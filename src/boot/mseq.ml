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
let split_at = BatFingerTree.split_at
let equal = BatFingerTree.equal
let head = BatFingerTree.head_exn
let tail = BatFingerTree.tail_exn
let init = BatFingerTree.init_exn
let last = BatFingerTree.last_exn

let map = BatFingerTree.map
let fold_right f s a = BatFingerTree.fold_right (fun a x -> f x a) a s

let combine s1 s2 =
  let rec work a s1 s2 =
    if length s1 == 0 then a
    else work (snoc a (head s1, head s2)) (tail s1) (tail s2)
  in
  if length s1 != length s2 then
    raise (Invalid_argument "sequences of different length")
  else work empty s1 s2

let fold_right2 f s1 s2 a =
  fold_right (fun x a -> f (fst x) (snd x) a) (combine s1 s2) a
