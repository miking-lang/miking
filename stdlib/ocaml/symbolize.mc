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
  VarSym + AppSym + LamSym + LetSym + RecLetsSym + RecordSym + ConstSym
  + NamedPatSym + IntPatSym + CharPatSym + BoolPatSym + RecordSym
  + OCamlTypeDeclAst + OCamlMatch + OCamlTuple + OCamlData
  + UnknownTypeSym + IntTypeSym + BoolTypeSym + FloatTypeSym + CharTypeSym
  + RecordTypeSym + VarTypeSym + OCamlExternal + OCamlPreambleHack
  + OCamlString + OCamlRecord

  sem symbolizeExpr (env : SymEnv) =
  | OTmVariantTypeDecl t ->
    let f = lam env. lam constr.
      match constr with (ident, ty) then
        match _symbolizeVarName env ident with (env, ident) then
          (env, (ident, symbolizeType env ty))
        else never
      else never
    in
    match _symbolizeVarName env t.ident with (env, ident) then
      let inexpr = symbolizeExpr env t.inexpr in
      match mapAccumL f env t.constrs with (env, constrs) then
        OTmVariantTypeDecl {{{t with ident = ident}
                                with constrs = constrs}
                                with inexpr = inexpr}
      else never
    else never
  | OTmMatch {target = target, arms = arms} ->
    let symbArm = lam arm. match arm with (pat, expr) then
      match symbolizePat env (mapEmpty cmpString) pat with (patEnv, pat) then
        let thnEnv = {env with varEnv = mapUnion env.varEnv patEnv} in
        (pat, symbolizeExpr thnEnv expr)
      else never else never in
    OTmMatch { target = symbolizeExpr env target, arms = map symbArm arms }
  | OTmTuple { values = values } ->
    OTmTuple { values = map (symbolizeExpr env) values }
  | OTmTupleProj t ->
    OTmTupleProj { t with tm = symbolizeExpr env t.tm }
  | OTmConApp t ->
    match _symbolizeVarName env t.ident with (env, ident) then
      let args = map (symbolizeExpr env) t.args in
      OTmConApp {{t with ident = ident}
                    with args = args}
    else never
  | OTmVarExt t -> OTmVarExt t
  | OTmConAppExt ({ args = args } & t) ->
    OTmConAppExt {t with args = map (symbolizeExpr env) args}
  | OTmPreambleText t ->
    OTmPreambleText {t with inexpr = symbolizeExpr env t.inexpr}
  | OTmString t -> OTmString t

  sem symbolizePat (env : SymEnv) (patEnv : SymEnv) =
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
