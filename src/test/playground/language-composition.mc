-- title: Language composition

-- A base language fragment for an expression evaluator.
-- It does not implement anything on its own.
lang Eval
  syn Expr =

  sem eval: Expr -> Expr
end

-- A language fragment that extends the Eval fragment
-- with numbers and arithmetic addition.
lang Arith = Eval
  syn Expr +=
  | Num Int
  | Add (Expr, Expr)

  sem eval +=
  | Num n -> Num n
  | Add (e1, e2) ->
    match eval e1 with Num n1 then
      match eval e2 with Num n2 then
        Num (addi n1 n2)
      else error "Not a number"
    else error "Not a number"
end

-- Another language fragment that implements logical
-- values and branching.
lang Logic = Eval
  syn Expr +=
  | True()
  | False()
  | If (Expr, Expr, Expr)

  sem eval +=
  | True() -> True()
  | False() -> False()
  | If (cnd, thn, els) ->
    let cndVal = eval cnd in
    match cndVal with True() then eval thn
    else match cndVal with False() then eval els
    else error "Not a boolean"
end

-- Here we compose the two language fragments to
-- make a third language fragment that implements
-- both arithmetic and logical operations.
lang ArithLogic = Arith + Logic end

-- End of declarations and start of program
mexpr

use ArithLogic in

-- Construct an abstract syntax tree and evaluate it.
let ast = Add (If (False(), Num 0, Num 5), Num 2) in
let result = eval ast in
dprint result
