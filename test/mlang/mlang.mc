lang Arith
  syn Expr =
  | Num(Dyn)
  | Add(Dyn, Dyn)

  sem eval =
  | Num n -> n
  | Add(t) ->
    let e1 = t in
    let e2 = t in
    iadd (eval e1) (eval e2)
end

lang Bool
  syn Expr =
  | True
  | False
  | If(Dyn, Dyn, Dyn)

  sem eval =
  | True -> true
  | False -> false
  | If t ->
    let cnd = t in
    let thn = t in
    let els = t in
    if eval cnd
    then eval thn
    else eval els
end

lang ArithBool = Arith + Bool

lang ArithBool2 = Arith + Bool
  syn Expr =
  | IsZero(Dyn)

  sem eval =
  | IsZero n ->
    if eqi (eval n) 0
    then True
    else False
end

nop