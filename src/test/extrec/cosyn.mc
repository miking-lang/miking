lang L0
  cosyn Foo = {}
end

lang L1 = L0
  cosyn Foo *= {a : Int}
end

lang L2 = L0
  cosyn Foo *= {b : Int}
end 

lang L12 = L1 + L2
end

mexpr
use L12 in 

let f1 = {Foo of a = 1} in 
let f2 = {Foo of b = -1} in 
let f3 = {Foo of a = 1, b = 10} in 

utest addi f1.a f2.b with 0 using eqi in 
match f3 with {a = a, b = b} in 
utest addi a b with 11 using eqi in 
()