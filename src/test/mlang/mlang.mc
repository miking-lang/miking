lang Base
  syn Expr =
  syn Value =
  | VInt Int
  | VBool Bool

  sem eval =
end

lang Arith = Base
  syn Expr +=
  | Num Int
  | Add (Expr, Expr)

  sem eval +=
  | Num n -> VInt n
  | Add(t) ->
    let e1 = t.0 in
    let e2 = t.1 in
    match eval e1 with VInt a in
    match eval e2 with VInt b in
    VInt (addi a b)
end

lang MyBool = Base
  syn Expr +=
  | True ()
  | False ()
  | If(Expr, Expr, Expr)

  sem eval +=
  | True _ -> VBool true
  | False _ -> VBool false
  | If t ->
    let cnd = t.0 in
    let thn = t.1 in
    let els = t.2 in
    match eval cnd with VBool b in
    if b
    then eval thn
    else eval els
end

lang ArithBool = Arith + MyBool end

lang ArithBool2 = Arith + MyBool
  syn Expr +=
  | IsZero Expr

  sem eval +=
  | IsZero n ->
    match eval n with VInt v in
    VBool (eqi v 0)
end

lang User
  syn Unit =
  | Unit ()
  sem inspect =
  | Unit _ ->
    use Arith in
    match eval (Add (Num 1, Num 2)) with VInt n in n
  sem bump (x : Int) =
  | Unit _ -> addi x 1
end

lang A
  syn ATy =
  | ACon {afield : Int}
end

lang Overlap = ArithBool + ArithBool2 + Arith end

lang FooBase
  syn Val =

  sem foo =
end

lang FooA = FooBase
  syn Val +=
  | A {}

  sem foo +=
  | A _ -> "A"
end

lang FooB = FooBase
  syn Val +=
  | B {}

  sem foo +=
  | B _ -> "B"
end

lang FooTrans = FooA + FooB end

lang FooCombined = FooA + FooTrans end

mexpr

(use ArithBool2 in
  utest eval (Add (Num 1, Num 2)) with VInt 3 in
  utest eval (If (IsZero (Num 0)
                 ,Num 1
                 ,Num 2)) with VInt 1
  in
  utest eval (Add (Num 10
                  ,If (IsZero (Add (Num 0, Num 3))
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with VInt 13
  in ());

(use ArithBool in
  utest eval (Add (Num 1, Num 2)) with VInt 3 in
  utest eval (If (True ()
                 ,Num 1
                 ,Num 2)) with VInt 1
  in
  utest eval (Add (Num 10
                  ,If (False ()
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with VInt 13
  in ());


(use User in
  utest inspect (Unit ()) with 3 in
  utest bump (inspect (Unit ())) (Unit ()) with 4 in
  ());

(use Overlap in
  utest eval (Add (Num 1, Num 2)) with VInt 3 in
  utest eval (If (IsZero (Num 0)
                 ,Num 1
                 ,Num 2)) with VInt 1
  in
  utest eval (Add (Num 10
                  ,If (IsZero (Add (Num 0, Num 3))
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with VInt 13 in
  ());

let e1 = use ArithBool in If(True(), Num 1, Num 2) in
let e2 = use ArithBool2 in If(True(), Num 1, Num 2) in
utest e1 with e2 in


(use FooCombined in
  utest foo (A {}) with "A" in
  utest foo (B {}) with "B" in
  ());


()
