lang Arith
  syn Expr =
  | Num Dyn
  | Add (Dyn, Dyn)

  sem eval =
  | Num n -> n
  | Add(t) ->
    let e1 = t.0 in
    let e2 = t.1 in
    addi (eval e1) (eval e2)
end

lang Bool
  syn Expr =
  | True ()
  | False ()
  | If(Dyn, Dyn, Dyn)

  sem eval =
  | True _ -> true
  | False _ -> false
  | If t ->
    let cnd = t.0 in
    let thn = t.1 in
    let els = t.2 in
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
    then true
    else false
end

lang User
  syn Unit =
  | Unit ()
  sem inspect =
  | Unit _ ->
    use Arith in
    eval (Add (Num 1, Num 2))
  sem bump (x : Dyn) =
  | Unit -> addi x 1
end

lang A
  syn ATy =
  | ACon {afield : Dyn}
end

lang AExtend = A
  syn ATy =
  | ACon {aextfield : Dyn}
end

lang Overlap = ArithBool + ArithBool2 + Arith

mexpr

let _ =
  use ArithBool2 in
  utest eval (Add (Num 1, Num 2)) with 3 in
  utest eval (If (IsZero (Num 0)
                 ,Num 1
                 ,Num 2)) with 1
  in
  utest eval (Add (Num 10
                  ,If (IsZero (Add (Num 0, Num 3))
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with 13
  in ()
in
let _ =
  use ArithBool in
  utest eval (Add (Num 1, Num 2)) with 3 in
  utest eval (If (True ()
                 ,Num 1
                 ,Num 2)) with 1
  in
  utest eval (Add (Num 10
                  ,If (False ()
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with 13
  in ()
in
let _ =
  use User in
  utest inspect (Unit ()) with 3 in
  utest bump (inspect (Unit ())) (Unit ()) with 4 in
  ()
in
let _ =
  use Overlap in
  utest eval (Add (Num 1, Num 2)) with 3 in
  utest eval (If (IsZero (Num 0)
                 ,Num 1
                 ,Num 2)) with 1
  in
  utest eval (Add (Num 10
                  ,If (IsZero (Add (Num 0, Num 3))
                      ,Num 10
                      ,Add (Num 5, (Num (negi 2)))))) with 13 in
  ()
in
let _ =
  let e1 = use ArithBool in If(True(), Num 1, Num 2) in
  let e2 = use ArithBool2 in If(True(), Num 1, Num 2) in
  utest e1 with e2 in
  ()
in

let _ =
  let e1 = use A in ACon{afield = 1, aextfield = 2} in // TODO(vipa): this should break once we start typechecking product extensions of a constructor
  let e2 = use AExtend in ACon{afield = 1, aextfield = 2} in
  utest e1 with e2 in
  ()
in

()
