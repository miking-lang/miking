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
  sem eval = 
  sem subst ident term = 
end

lang LC = Base
  syn Term += 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term}
  | TmVar {ident : String}

  sem eval += 
  | TmVar t -> TmVar t
  | TmAbs t -> TmAbs t
  | TmApp outer -> 
    match outer.lhs with TmAbs t then
      eval (subst t.ident outer.rhs t.body)
    else 
      eval (TmApp {TmAppType of lhs = eval outer.lhs, rhs = outer.rhs})

  sem subst ident term +=
  | TmVar t -> if eqString ident t.ident then term else TmVar t
  | TmApp t -> TmApp {TmAppType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
  | TmAbs t -> if eqString ident t.ident then TmAbs t 
               else TmAbs {TmAbsType of ident = t.ident, 
                                        body = subst ident term t.body}
end

lang IntArith = Base
  syn Term += 
  | TmAdd {lhs : Term, rhs : Term}
  | TmInt {val : Int}

  sem eval +=
  | TmInt t -> TmInt t 
  | TmAdd t -> 
    match eval t.lhs with TmInt l then 
      match eval t.rhs with TmInt r then
        TmInt {TmIntType of val = addi l.val r.val}
      else 
        error "..."
    else 
      error "..."

  sem subst ident tm +=
  | TmInt t -> TmInt t
  | TmAdd t -> TmAdd {TmAddType of lhs = subst ident tm t.lhs, 
                                   rhs = subst ident tm t.rhs}
end

lang TypeCheck = Base
  cosyn Env = {} 

  cosem emptyEnv : () -> Env
  cosem emptyEnv arg = 

  sem typeCheck (env : Env) =

  sem eqType =
end

lang STLC = TypeCheck + LC + IntArith
  syn Ty += 
  | TyArrow {lhs : Ty, rhs : Ty}
  | TyInt {}

  syn Term *= 
  | TmAbs {tyAnnot : Ty}

  cosyn Env *= {varMap : [(String, Ty)]}

  cosem emptyEnv arg *=
  | {varMap} <- {varMap = []}

  sem eqType +=
  | (TyInt _, TyInt _) -> true
  | (TyArrow t1, TyArrow t2) -> and (eqType (t1.lhs, t2.lhs)) (eqType (t1.rhs, t2.rhs))
  | _ -> false

  sem getFromEnv ident = 
  | [(h, ty)] ++ t ->
    if eqString h ident then
      ty
    else 
      getFromEnv ident t
  | [] -> 
    error "Ident not found in env!"

  sem subst ident tm += 

  sem typeCheck (env : Env) += 
  | TmVar t -> 
    let varMap = env.varMap in 
    getFromEnv t.ident varMap
  | TmAbs t -> 
    let varMap = env.varMap in 
    let newVarMap = cons (t.ident, t.tyAnnot) varMap in 
    let newEnv = {env with varMap = newVarMap} in 
    let rhs = typeCheck newEnv t.body in 
    TyArrow {TyArrowType of lhs = t.tyAnnot, rhs = rhs}
  | TmApp t -> 
    match typeCheck env t.lhs with TyArrow inner then
      match inner with {lhs = lhs, rhs = rhs} in 
      if eqType (lhs, (typeCheck env t.rhs)) then rhs
      else error "..."
    else error "..."
  | TmInt _ -> TyInt {TyIntType of nothing}
  | TmAdd _ -> TyInt {TyIntType of nothing}
end

lang SystemF = STLC + Base + TypeCheck
  syn Ty += 
  | TyVar {ident : String}
  | TyForall {ident : String, ty : Ty}

  syn Term += 
  | TmTypeAbs {ident : String, body : Term}
  | TmTypeApp {lhs : Term, rhs : Ty}

  sem eqType +=
  | (TyVar t1, TyVar t2) -> eqString t1.ident t2.ident
  | (TyForall t1, TyForall t2) -> and (eqType (t1.ty, t2.ty)) (eqString t1.ident t2.ident)

  sem dumpType = 
  | TyVar t -> print t.ident
  | TyForall t -> 
    print "all ";
    print t.ident;
    print ". ";
    dumpType t.ty 
  | TyInt t -> print "Int"
  | TyArrow t -> 
    dumpType t.lhs ;
    print " -> ";
    dumpType t.rhs

  sem substTy ident ty =
  | TyVar t  ->
    if eqString ident t.ident then 
      ty 
    else 
      TyVar t
  | TyForall t ->
    error "nested foralls are not supported for now"
  | TyInt t -> 
    TyInt t
  | TyArrow t -> 
    TyArrow {TyArrowType of lhs = substTy ident ty t.lhs, 
                            rhs = substTy ident ty t.rhs}
  -- | 


  cosyn Env *= {tyvars : [String]}

  cosem emptyEnv arg *=
  | { tyvars} <- {tyvars = []}

  sem typeCheck (env : Env) +=
  | TmTypeAbs t -> 
    let tyvars = env.tyvars in 
    let tyvars = cons t.ident tyvars in 
    let env = {env with tyvars = tyvars} in 
    let ty = typeCheck env t.body in
    TyForall {TyForallType of ident = t.ident, ty = ty}
  | TmTypeApp t ->
    match typeCheck env t.lhs with TyForall forall then
      substTy forall.ident t.rhs forall.ty
    else 
      error "Expected universal type!"

end


mexpr 
use SystemF in 
-- Test type checking of `lam x : Int. x + 1`
let tyInt = TyInt {TyIntType of nothing} in 
let add = TmAdd {TmAddType of lhs = TmVar {TmVarType of ident = "x"}, 
                              rhs = TmInt {TmIntType of val = 1}} in 
let add1 = TmAbs {TmAbsType of ident = "x", tyAnnot = tyInt, body = add} in 

let actualTy = typeCheck (emptyEnv ()) add1 in 
let expectedType = TyArrow {TyArrowType of lhs = tyInt, rhs = tyInt} in 
utest actualTy with expectedType using (lam l. lam r. eqType (l, r)) in 

-- Test type checking of `Lam T. lam x : T. x
let id =  TmAbs {TmAbsType of ident = "x",
                              tyAnnot = TyVar {TyVarType of ident = "T"}, 
                              body = TmVar {TmVarType of ident = "x"}} in 
let idPoly = TmTypeAbs {TmTypeAbsType of ident = "T", body = id} in

let actualTy = typeCheck (emptyEnv ()) idPoly in 
let expectedTy = TyForall {TyForallType of ident = "T", 
                                           ty = TyArrow {TyArrowType of lhs = TyVar {TyVarType of ident = "T"},
                                                                        rhs = TyVar {TyVarType of ident = "T"}}} in 
utest actualTy with expectedTy using (lam l. lam r. eqType (l, r)) in 

-- Test type checking of 'twice' `Lam T. lam f : T -> T. lam x : T. f (f x)
let _var = lam s. TmVar {TmVarType of ident = s} in 
let _app = lam lhs. lam rhs. TmApp {TmAppType of lhs = lhs, rhs = rhs} in 
let _abs = lam s. lam ty. lam body. TmAbs {TmAbsType of ident = s,
                                                        tyAnnot = ty, 
                                                        body = body} in 
let _tyabs = lam s. lam body. TmTypeAbs {TmTypeAbsType of ident = s, body = body} in
let _tyall = lam s. lam ty.  TyForall {TyForallType of ident = s, ty = ty} in 
let _tyvar = lam s. TyVar {TyVarType of ident = s} in 
let _tyarrow = lam lhs. lam rhs. TyArrow {TyArrowType of lhs = lhs, rhs = rhs} in 


let _x = _var "x" in 
let _f = _var "f" in 
let _T = _tyvar "T" in 
let _T2T = _tyarrow _T _T in 

let twice = _tyabs "T" (_abs "f" _T2T (_abs "x" _T (_app _f (_app _f _x)))) in 
let actualTy = typeCheck (emptyEnv ()) twice in 
let expectedTy = _tyall "T" (_tyarrow _T2T (_tyarrow _T _T)) in 
utest actualTy with expectedTy using (lam l. lam r. eqType (l, r)) in 

()
