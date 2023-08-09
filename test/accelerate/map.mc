include "string.mc"

mexpr

let s1 = [1,2,3] in
let s2 = accelerate (
  map (addi 1) s1) in
utest s2 with [2,3,4] in
()
