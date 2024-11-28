lang BaseArith
  syn Expr = 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr} 
  | TmIncr {e : Expr} 

  -- sem eval : atmost BaseArith::Expr -> Int
  sem eval : atmost (BaseArith::Expr - Expr::TmIncr) -> Int
  sem eval =
  | TmInt t -> t.val 
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)

  sem desugar : atmost BaseArith::Expr -> atleast (BaseArith::Expr - Expr::TmIncr) 
  sem desugar =
  | TmInt t -> TmInt {TmIntType of val = t.val}
  | TmAdd t -> TmAdd {TmAddType of lhs = desugar t.lhs,
                                   rhs = desugar t.rhs}
  | TmIncr t -> TmAdd {TmAddType of lhs = desugar t.e, 
                                    rhs = TmInt {TmIntType of val = 1}}
end