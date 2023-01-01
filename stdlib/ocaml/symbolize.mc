include "ocaml/ast.mc"
include "mexpr/symbolize.mc"

let _symbolizeVarName = lam env : SymEnv. lam ident.
  match env with {varEnv = varEnv} then
    if nameHasSym ident then (env, ident)
    else
      let ident = nameSetNewSym ident in
      let str = nameGetStr ident in
      let varEnv = mapInsert str ident varEnv in
      let env = {env with varEnv = varEnv} in
      (env, ident)
  else never

lang OCamlSym =
  VarSym + AppAst + LamSym + LetSym + RecLetsSym + RecordAst + ConstAst
  + NamedPatSym + IntPat + CharPat + BoolPat + RecordAst
  + OCamlMatch + OCamlTuple + OCamlData
  + UnknownTypeAst + IntTypeAst + BoolTypeAst + FloatTypeAst + CharTypeAst
  + RecordTypeAst + ConAppTypeSym + OCamlExternal
  + OCamlString + OCamlRecord + OCamlLabel

  sem symbolizeExpr (env : SymEnv) =
  | OTmMatch {target = target, arms = arms} ->
    let symbArm = lam arm. match arm with (pat, expr) then
      match symbolizePat env (mapEmpty cmpString) pat with (patEnv, pat) then
        let thnEnv = {env with varEnv = mapUnion env.varEnv patEnv} in
        (pat, symbolizeExpr thnEnv expr)
      else never else never in
    OTmMatch { target = symbolizeExpr env target, arms = map symbArm arms }
  | OTmTuple { values = values } ->
    OTmTuple { values = map (symbolizeExpr env) values }
  | OTmConApp t ->
    match _symbolizeVarName env t.ident with (env, ident) then
      let args = map (symbolizeExpr env) t.args in
      OTmConApp {{t with ident = ident}
                    with args = args}
    else never
  | OTmVarExt t -> OTmVarExt t
  | OTmConAppExt ({ args = args } & t) ->
    OTmConAppExt {t with args = map (symbolizeExpr env) args}
  | OTmString t -> OTmString t
  | OTmLabel t -> OTmLabel {t with arg = symbolizeExpr env t.arg }
  | OTmRecord t ->
    let bindings =
      map (lam b : (String, Expr). (b.0, symbolizeExpr env b.1)) t.bindings
    in
    OTmRecord {t with bindings = bindings}
  | OTmProject t -> OTmProject {t with tm = symbolizeExpr env t.tm}

  sem symbolizePat (env : SymEnv) (patEnv : Map String Name) =
  | OPatTuple { pats = pats } ->
    match mapAccumL (symbolizePat env) patEnv pats with (patEnv, pats) then
      (patEnv, OPatTuple { pats = pats })
    else never
  | OPatCon t ->
    match env with {conEnv = conEnv} then
      let ident =
        if nameHasSym t.ident then t.ident
        else
          let str = nameGetStr t.ident in
          match mapLookup str conEnv with Some ident then ident
          else error (concat "Unknown constructor in symbolizeExpr: " str)
      in
      match mapAccumL (symbolizePat env) patEnv t.args with (patEnv, args) then
        (patEnv, OPatCon {{t with ident = ident}
                           with args = args})
      else never
    else never
  | OPatConExt ({ args = pats } & t) ->
    match mapAccumL (symbolizePat env) patEnv pats with (patEnv, pats) then
      (patEnv, OPatConExt { t with args = pats })
    else never
  | OPatRecord t ->
    let symf = lam patEnv. lam _i. lam p. symbolizePat env patEnv p in
    match mapMapAccum symf patEnv t.bindings with (env, bindings) then
      (env, OPatRecord {t with bindings = bindings})
    else never
end
