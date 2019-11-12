let head = lam s. nth s 0
let tail = lam s. slice s 1 (length s)

lang WrappedList
  syn List =
  | List [Dyn]

  sem my_head =
  | List l -> head l

  sem my_tail =
  | List l -> List (tail l)
end

mexpr

let s = [1,2,3] in
utest head s with 1 in
utest tail s with [2,3] in

use WrappedList in
let l = List [1,2,3] in
utest my_head l with 1 in
utest my_tail l with List [2,3] in

()
