lang ArithLang 
  syn Expr = 
  | TmZero {}
  | TmSucc {expr : Expr}

  sem val =
  | TmZero _ -> 0
  | TmSucc e -> addi (val e.expr) 1

end

mexpr
use ArithLang in 
let z = TmZero {TmZeroType of nothing} in 
let one = TmSucc {TmSuccType of expr = z} in 
utest val z with 0 in 
utest val one with 1 in 
()