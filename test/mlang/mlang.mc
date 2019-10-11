lang Arith
  syn Expr =
  | Num(Dyn)
  | Add(Dyn, Dyn)

  sem eval =
  | Num(n) -> n
  | Add(e1, e2) -> iadd (eval e1) (eval e2)
end

lang Bool
  syn Expr =
  | True
  | False
  | If(Dyn, Dyn, Dyn)
end

lang ArithBool = Arith + Bool

lang ArithBool2 = Arith + Bool
  syn Expr =
  | IsZero(Dyn)
end

()
