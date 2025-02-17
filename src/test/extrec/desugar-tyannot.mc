lang BaseArith
  syn Expr = 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr} 
  | TmIncr {e : Expr} 

  sem eval : atmost (BaseArith::Expr - Expr::TmIncr) -> Int
  sem eval =
  | TmInt t -> t.val 
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)

  sem desugar : atmost BaseArith::Expr -> atleast (BaseArith::Expr - Expr::TmIncr) 
  sem desugar =
  | TmInt t -> TmInt {val = t.val}
  | TmAdd t -> TmAdd {lhs = desugar t.lhs,
                      rhs = desugar t.rhs}
  | TmIncr t -> TmAdd {lhs = desugar t.e, 
                       rhs = TmInt {val = 1}}
end

mexpr
use BaseArith in
let e = TmIncr {e = TmInt {val = 1}} in

let desugared = desugar e in 
utest eval desugared with 2 in ()