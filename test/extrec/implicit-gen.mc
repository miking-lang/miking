lang Base
  syn Expr = 
  sem eval =
  sem foo =
end

lang ArithLang = Base
  syn Expr +=
  | TmInt {v : Int}
  | TmAdd {e1 : Expr, e2 : Expr}

  sem eval +=
end

lang LambdaCalculus = Base
  syn Expr += 
  | TmVar {ident : String}
  | TmAbs {ident : String, body : Expr}
  | TmApp {lhs : Expr, rhs : Expr}

  sem eval +=
  sem foo +=
end

lang STLC = LambdaCalculus
  syn Expr *=
  | TmAbs {tyAnnot : String}

  sem eval +=
  sem foo +=
end

lang LCArith = STLC + ArithLang 
end

mexpr
use LCArith in
let e = TmAdd {e1 = TmInt {v = 3}, e2 = TmInt {v = 4}} in
()