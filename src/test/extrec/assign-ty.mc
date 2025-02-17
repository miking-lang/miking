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

lang LC 
  syn Ty = 

  syn Term = 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term, tyAnnot : Ty}
  | TmVar {ident : String}

  sem eval = 
  | (TmVar _ | TmAbs _) & tm -> tm
  | TmApp outer -> 
    match outer.lhs with TmAbs t then
      eval (subst t.ident outer.rhs t.body)
    else 
      eval (TmApp {lhs = eval outer.lhs, rhs = outer.rhs})

  sem subst ident term =
  | TmVar t -> if eqString ident t.ident then term else TmVar t
  | TmApp t -> TmApp {lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
  | TmAbs t -> if eqString ident t.ident then TmAbs t 
               else TmAbs {TmAbsType of ident = t.ident, 
                                        body = subst ident term t.body}
end

lang IntArith = LC
  syn Term += 
  | TmAdd {lhs : Term, rhs : Term}
  | TmInt {val : Int}

  sem eval +=
  | TmInt t -> TmInt t 
  | TmAdd t -> 
    match eval t.lhs with TmInt l then 
      match eval t.rhs with TmInt r then
        TmInt {val = addi l.val r.val}
      else 
        error "..."
    else 
      error "..."

  sem subst ident tm +=
  | TmInt t -> TmInt t
  | TmAdd t -> TmAdd {lhs = subst ident tm t.lhs, 
                                   rhs = subst ident tm t.rhs}
end

lang LCArith = LC + IntArith 
end

lang AssignTy = LCArith
  syn Ty += 
  | TyArrow {lhs : Ty, rhs : Ty}
  | TyInt {}

  syn Term *= 
  | TmAbs {ty : Ty}
  | TmAdd {ty : Ty}
  | TmInt {ty : Ty}
  | TmApp {ty : Ty}
  | TmVar {ty : Ty}

  sem tyTm = 
  | TmAbs t -> t.ty
  | TmAdd t -> t.ty
  | TmInt t -> t.ty
  | TmApp t -> t.ty
  | TmVar t -> t.ty


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

  sem stripTyAnnot =
  | TyInt _ -> TyInt {}
  | TyArrow t -> 
    let lhs = stripTyAnnot t.lhs in 
    let rhs = stripTyAnnot t.rhs in 
    TyArrow {lhs = lhs, rhs = rhs}

  sem assignTy env = 
  | TmVar t -> 
    let foundType = getFromEnv t.ident env in 
    TmVar {ident = t.ident, ty = foundType}
  | TmAbs t ->
    let tyAnnot = stripTyAnnot t.tyAnnot in 
    -- let tyAnnot = t.tyAnnot in 

    let body = t.body in 
    let ident = t.ident in 

    let newEnv = cons (t.ident, tyAnnot) env in 
    let newBody = assignTy newEnv body in 
    let tyBody = tyTm newBody in 

    let ty = TyArrow {lhs = tyAnnot, rhs = tyBody} in 
    TmAbs {TmAbsType of tyAnnot = tyAnnot, 
                        ty = ty,
                        body = newBody,
                        ident = ident}
  | TmApp t ->
    let lhs = t.lhs in 
    let rhs = t.rhs in

    let newLhs = assignTy env lhs in 
    let newRhs = assignTy env rhs in

    let leftTy = tyTm newLhs in 
    let rightTy = tyTm newRhs in 

    let ty = TyArrow {lhs = leftTy, rhs = rightTy} in 
    TmApp {lhs = newLhs, rhs = newRhs, ty = ty} 
  | TmInt t -> 
    let ty = TyInt {} in 
    TmInt {ty = ty, val = t.val}
  | TmAdd t -> 
    let lhs = t.lhs in 
    let rhs = t.rhs in

    let newLhs = assignTy env lhs in 
    let newRhs = assignTy env rhs in

    let leftTy = tyTm newLhs in 
    let rightTy = tyTm newRhs in 

    let tyInt = TyInt {} in 

    if and (eqType (tyInt, leftTy)) (eqType (tyInt, rightTy)) then
      TmAdd {lhs = newLhs, rhs = newRhs, ty = tyInt}
    else 
      error "LHS and RHS of TmAdd must be of integer type!"
end

mexpr
print "\n\n\nTESTS\n\n\n";
use AssignTy in 
let tyInt = TyInt {} in 
let one = TmInt {val = 1} in 
let five = TmInt {val = 5} in 

let typedOne = assignTy [] one in 
let typedFive = assignTy [] five in 
utest tyTm typedOne with tyInt using (lam l. lam r. eqType (l, r)) in 
utest tyTm typedFive with tyInt using (lam l. lam r. eqType (l, r)) in 


let addOneFive = TmAdd {lhs = five, rhs = one} in 
let typedAdd = assignTy [] addOneFive in 
utest tyTm typedAdd with tyInt using (lam l. lam r. eqType (l, r)) in 

let add = TmAdd {lhs = TmVar {ident = "x"}, rhs = TmInt {val = 1}} in 
let add1 = TmAbs {ident = "x", tyAnnot = tyInt, body = add} in 

let add1Ty = assignTy [] add1 in 
let actualTy = tyTm add1Ty in 
let expectedType = TyArrow {lhs = tyInt, rhs = tyInt} in 
utest actualTy with expectedType using (lam l. lam r. eqType (l, r)) in 

()