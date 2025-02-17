lang SomeLang
  cosyn Foo = {x : Int, y : Int}
  cosyn Bar = {f : Foo}

  sem f : Bar -> Int
  sem f =
  | {f = {x = x}} -> addi x 1
end

mexpr
use SomeLang in 
utest f {Bar of f = {Foo of x = 22}} with 23 using eqi in 
()