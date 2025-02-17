let and = lam b1. lam b2.
  if b1 then b2 else false
  
recursive let eqString = lam s1. lam s2.
  match (s1, s2) with ([], []) then 
    true
  else match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
    and (eqc h1 h2) (eqString t1 t2)
  else 
    false
end

lang Base
  syn Ty =

  syn Term = 

  sem isValue = 
  | _ -> false

  sem step = 

  sem subst ident term =
end

lang LambdaCalculus = Base
  syn Term += 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term}
  | TmVar {ident : String}

  sem step += 
  | TmApp t -> 
    match t.lhs with TmAbs t2 then
      subst t2.ident t2.body t.rhs  
    else if isValue t.lhs then 
      TmApp {TmAppType of lhs = t.lhs, rhs = step t.rhs} 
    else 
      TmApp {TmAppType of lhs = step t.lhs, rhs = t.rhs} 
  | TmVar _ -> error "Stuck!"
  | TmAbs _ -> error "Stuck!"

  sem subst ident term +=
  | TmVar t -> if eqString ident t.ident then term 
               else TmVar t
  | TmApp t -> TmApp {TmAppType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
  | TmAbs t -> if eqString ident t.ident then TmAbs t else
               TmAbs {TmAbsType of ident = t.ident, 
                                   body = subst ident term t.body}

  sem isValue +=
  | TmAbs _ -> true
end

lang Arith = Base
  syn Term += 
  | TmInt {val : Int}
  | TmAdd {lhs : Term, rhs : Term}

  sem step +=
  | TmAdd t ->
    match (t.lhs, t.rhs) with (TmInt t1, TmInt t2) then
      TmInt {TmIntType of val = addi t1.val t2.val}
    else match t.lhs with TmInt _ then
      TmAdd {TmAddType of lhs = t.lhs, rhs = step t.rhs}
    else 
      TmAdd {TmAddType of lhs = step t.lhs, rhs = t.rhs}
  | TmInt _ -> error "Stuck!"

  sem isValue +=
  | TmInt _ -> true
end

lang LambdaCalculusArith = LambdaCalculus + Arith
  sem subst ident term += 
  | TmInt t -> TmInt t
  | TmAdd t -> TmAdd {TmAddType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
end

lang STLC = LambdaCalculusArith

  syn Ty += 
  | TyArrow {lhs : Ty, rhs : Ty}
  | TyInt {}

  syn Term *= 
  | TmAbs {tyAnnot : Ty}

  sem eqType =
  | (TyInt _, TyInt _) -> true
  | (TyArrow t1, TyArrow t2) -> and (eqType (t1.lhs, t2.lhs)) (eqType (t1.rhs, t2.rhs))
  | _ -> false

  sem getFromEnv ident = 
  | [(h, ty)] ++ t ->
    if eqString h ident then
      ty
    else 
      getFromEnv ident t
  | [] -> error "Ident not found in env!"

  sem typeCheck env = 
  | TmVar t -> getFromEnv t.ident env
  | TmAbs t -> TyArrow {TyArrowType of lhs = t.tyAnnot, rhs = typeCheck (cons (t.ident, t.tyAnnot) env) t.body}
  | TmApp t -> 
    match typeCheck env t.lhs with TyArrow inner then
      match inner with {lhs = lhs, rhs = rhs} in 
      if eqType (lhs, (typeCheck env t.rhs)) then rhs
      else error "..."
    else error "..."
  | TmInt _ -> TyInt {TyIntType of nothing}
  | TmAdd _ -> TyInt {TyIntType of nothing}
end

mexpr
use STLC in 
let tyInt = TyInt {TyIntType of nothing} in 
let add = TmAdd {TmAddType of lhs = TmVar {TmVarType of ident = "x"}, 
                              rhs = TmInt {TmIntType of val = 1}} in 
let add1 = TmAbs {TmAbsType of ident = "x", tyAnnot = tyInt, body = add} in 

let actualTy = typeCheck [] add1 in 
let expectedType = TyArrow {TyArrowType of lhs = tyInt, rhs = tyInt} in 
utest actualTy with expectedType using (lam l. lam r. eqType (l, r)) in 

let expr = TmAdd {TmAddType of lhs = TmInt {TmIntType of val = 2}, 
                               rhs = TmInt {TmIntType of val = 1}}  in
let result = step expr in 
(match result with TmInt t then
  (utest t.val with 3 in ())
else 
  error "Test failed, result is not int!");
()  