lang L 
  cosyn Foo = {x : Int, y : Int}
end 

mexpr 
use L in 
let r = {Foo of nothing} in 
let r = {extend r with x = 1, y = 2} in 
utest addi r.x r.y with 3 in 
()