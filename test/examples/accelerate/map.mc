include "string.mc"

mexpr

let s1 : [Int] = [1,2,3] in
let s2 : [Int] = accelerate (
  (let m : (Int -> Int) -> [Int] -> [Int] = map in m) (lam x : Int. addi x 1) s1) in
print (strJoin ", " (map int2string s2));
()
