lang SomeLang 
  syn Expr a = 
  | TmFoo {x : Int}

  sem f = 
  | TmFoo {x = x} -> x

  sem g =
  | TmFoo (f & {x = 1}) -> 0
  | _ -> negi 1
end

mexpr
use SomeLang in 
let foo = TmFoo {x = 21} in 
let footoo = TmFoo {x = 1} in 
utest f foo with 21 using eqi in
utest g footoo with 0 using eqi in
()