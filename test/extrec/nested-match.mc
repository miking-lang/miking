lang SomeLang 
  syn Expr = 
  | TmFoo {x : Int, y : Int}

  sem f = 
  | TmFoo {x = x} -> muli x 2
end

mexpr
use SomeLang in 
let foo = TmFoo {x = 21} in 
utest f foo with 42 in
()