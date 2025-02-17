lang MyLang
  syn Expr = 
  | TmInt {val : Int}

  sem eval = 
  | TmInt t -> t.val

  sem negate =
  | TmInt t -> TmInt {val = negi t.val}
end

mexpr
use MyLang in 
let expr = TmInt {val = 1} in 
utest eval (negate expr) with -1 in 
()