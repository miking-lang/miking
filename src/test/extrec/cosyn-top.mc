lang SomeLang 
  cosyn Foo = {x : Int, y : Int}

  sem f : Foo -> Int
  sem f = 
  | {x = x} -> addi x 1
end

mexpr 
use SomeLang in 
utest f {Foo of x = 22} with 23 in 
()