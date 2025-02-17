lang SomeLang
  syn Expr = 
  | TmA {x : Int} 
  | TmB {y : Int}

  sem f =
  | TmA _ -> 10
end

mexpr
use SomeLang in 
utest f (TmA {x = 10}) with 10 in 
utest f (TmB {y = 10}) with 10 in 
()