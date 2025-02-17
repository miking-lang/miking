lang ArithLang
  syn Expr =
  | TmInt {val : Int}
  | TmAdd {lhs: Expr, rhs: Expr}

  sem eval : all m :: {Expr [< TmAdd TmInt], 
                       TmIntType [> val], 
                       TmAddType [> lhs rhs]}.
             Expr{m} -> Int
  sem eval = 
  | TmInt t -> t.val
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)
end

mexpr use ArithLang in 
let int_ = lam v. TmInt {TmIntType of val = v} in 
utest eval (TmAdd {TmAddType of lhs = int_ 1, rhs = int_ 2}) 
with 3 using eqi in ()