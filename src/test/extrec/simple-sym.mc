let and = lam b1. lam b2.
  if b1 then b2 else false

let digit2char = lam d.
  int2char (addi d (char2int '0'))
  
recursive let eqString = lam s1. lam s2.
  match (s1, s2) with ([], []) then 
    true
  else match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
    and (eqc h1 h2) (eqString t1 t2)
  else 
    false
end

let int2string = lam n.
  recursive
  let int2string_rechelper = lam n. lam acc.
    if lti n 10
    then cons (digit2char n) acc
    else int2string_rechelper (divi n 10) (cons (digit2char (modi n 10)) acc)
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n) "")
  else int2string_rechelper n ""

let mapInsert = lam k. lam v. lam m.
  cons (k, v) m

recursive let mapLookup = lam k1. lam m. 
  match m with [(k2, v)] ++ t then
    if eqString k1 k2 then 
      v
    else
      mapLookup k1 t
  else
    error "Key not found!"
end

lang Ast
  syn Expr = 

  syn Type = 
end

lang AppAst = Ast
  syn Expr +=
  | TmApp {lhs : Expr, rhs : Expr}
end

lang AbsAst = Ast
  syn Expr +=
  | TmAbs {ident : String,
           body : Expr}
end

lang IntAst = Ast 
  syn Expr += 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr}
end

lang VarAst = Ast
  syn Expr +=
  | TmVar {ident : String}
end

lang SimpleLang = Ast + AppAst + AbsAst + IntAst + VarAst
end

lang BaseSym = Ast
  cosyn SymEnv = {nextVal : Int}
  sem symbolizeExpr env = 
end

lang SimpleSym = SimpleLang + BaseSym
  cosyn SymEnv *= {varEnv : [(String, String)]}

  sem symbolizeExpr (env : SymEnv) += 
  | TmInt t -> TmInt t
  | TmAdd t -> 
    TmAdd {TmAddType of lhs = symbolizeExpr env t.lhs,
                        rhs = symbolizeExpr env t.rhs}
  | TmApp t -> TmApp {TmAppType of lhs = symbolizeExpr env t.lhs,
                                   rhs = symbolizeExpr env t.rhs}
  | TmAbs t ->
    let varEnv = env.varEnv in 
    let val = env.nextVal in 
    let newIdent = concat t.ident (int2string val) in 
    let varEnv = mapInsert t.ident newIdent varEnv in 
    let env = {env with varEnv = varEnv, nextVal = addi 1 val} in 
    TmAbs {TmAbsType of ident = newIdent,
                        body = symbolizeExpr env t.body}
  | TmVar t ->
    let varEnv = env.varEnv in 
    let ident = mapLookup t.ident varEnv in 
    TmVar {TmVarType of ident = ident} 
end

lang ConDefAst = Ast
  syn Expr += 
  | TmConDef {ident : String,
              ty : Type,
              inexpr : Expr}
end

lang ExtendedLang = ConDefAst + SimpleLang
end

lang ExtendedSym = ExtendedLang + BaseSym
  cosyn SymEnv *= {conEnv : [(String, String)]}

  sem symbolizeExpr (env : SymEnv) +=
  | TmConDef t -> 
    let val = env.nextVal in 
    let conEnv = env.conEnv in 
    let newIdent = concat t.ident (int2string val) in 
    let conEnv = mapInsert t.ident newIdent conEnv in 
    let env = {env with conEnv = conEnv, nextVal = addi 1 val} in 
    TmConDef {TmConDefType of ident = newIdent,
                              inexpr = symbolizeExpr env t.inexpr}
end

lang FullSym = ExtendedSym + SimpleSym
end

mexpr
use FullSym in 
let env = {SymEnv of varEnv = [], conEnv = [], nextVal = 0} in 
symbolizeExpr env (TmInt {TmIntType of val = 1});
()