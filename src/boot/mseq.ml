type 'a t = 'a BatFingerTree.t

let of_list = BatFingerTree.of_list
let to_list = BatFingerTree.to_list
let of_array a = of_list (Array.to_list a)
let to_array s = Array.of_list (to_list s)
let of_ustring u = of_list (Ustring.Op.ustring2list u)
let to_ustring s = Ustring.Op.list2ustring (to_list s)

let map = BatFingerTree.map

let make n f = of_list (List.init n f)
let empty = BatFingerTree.empty
let length = BatFingerTree.size
let concat = BatFingerTree.append
let get = BatFingerTree.get
let cons e s = BatFingerTree.cons s e
let reverse = BatFingerTree.reverse
let split_at = BatFingerTree.split_at
let equal = BatFingerTree.equal
