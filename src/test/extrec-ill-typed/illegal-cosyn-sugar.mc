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
  sem f : < L1::Foo -> Int
  sem f =
  | foo -> 
    addi foo.a foo.b
end

mexpr
use L12 in 

let foo = {Foo of a = 1, b = 10} in 
utest f foo with 11 using eqi in 

()