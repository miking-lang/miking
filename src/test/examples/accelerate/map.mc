include "string.mc"

mexpr

let s1 : [Int] = [1,2,3] in
let s2 : [Int] = accelerate (
  map (addi 1) s1) in
print (strJoin ", " (map int2string s2));
()
