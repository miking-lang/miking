lang BaseArith
  syn Expr = 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr} 

  sem eval =
  | TmInt t -> t.val 
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)
end

lang SugarArith = BaseArith
  syn Expr += 
  | TmIncr {e : Expr} 

  sem desugar =
  | TmInt t -> TmInt {TmIntType of val = t.val}
  | TmAdd t -> TmAdd {TmAddType of lhs = desugar t.lhs,
                                   rhs = desugar t.rhs}
  | TmIncr t -> TmAdd {TmAddType of lhs = desugar t.e, 
                                    rhs = TmInt {TmIntType of val = 1}}
end

mexpr
use SugarArith in 
let expr = TmInt {TmIntType of val = 42} in
eval expr ;
utest eval expr with 42 using eqi in 
let expr2 = TmAdd {TmAddType of lhs = TmInt {TmIntType of val = 23},
                                rhs = TmInt {TmIntType of val = 42}} in 
eval expr2 ;
utest eval expr2 with 65 using eqi in 
let expr3 = TmIncr {TmIncrType of e = expr} in 
utest eval (desugar expr3) with 43 using eqi in 
()