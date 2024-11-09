lang SomeLang
  type MyAlias = (Expr, Expr)

  syn Expr = 
  | TmSomething {x : MyAlias}
  | TmNil ()
end

mexpr
use SomeLang in 
let t = TmSomething {x = (TmNil (), TmNil ())} in
()