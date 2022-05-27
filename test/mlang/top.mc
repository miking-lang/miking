lang WrappedList
  syn List =
  | List [Int]

  sem my_head =
  | List l -> head l

  sem my_tail =
  | List l -> List (tail l)
end

let topUse =
  use WrappedList in
  let l = List [1,2,3] in
  let hd = my_head l in
  hd

mexpr

utest topUse with 1 in

use WrappedList in
let l = List [1,2,3] in
utest my_head l with 1 in
utest my_tail l with List [2,3] in

()
