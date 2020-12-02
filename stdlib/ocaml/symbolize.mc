include "ocaml/ast.mc"
include "mexpr/symbolize.mc"

lang OCamlSym =
  VarSym + AppSym + FunSym + LetSym + RecLetsSym + ConstSym
  + NamedPatSym + IntPatSym + CharPatSym + BoolPatSym
  + OCamlMatch + OCamlTuple + OCamlData

  sem symbolizeExpr (env : Env) =
  | OTmMatch {target = target, arms = arms} ->
    let symbArm = lam arm. match arm with (pat, expr) then
      match symbolizePat env assocEmpty pat with (patEnv, pat) then
        (pat, symbolizeExpr (_symOverwrite env patEnv) expr)
      else never else never in
    OTmMatch { target = symbolizeExpr env target, arms = map symbArm arms }
  | OTmTuple { values = values } ->
    OTmTuple { values = map (symbolizeExpr env) values }
  | OTmConApp { ident = ident, args = args } -> error "We're not quite done with adt's in ocaml yet, so symbolize won't work with programs that use them (in this case OTmConApp)"

  sem symbolizePat (env : Env) (patEnv : Env) =
  | OPTuple { pats = pats } ->
    match mapAccumL (symbolizePat env) patEnv pats with (patEnv, pats) then
      (patEnv, OPTuple { pats = pats })
    else never
  | OPCon _ -> error "We're not quite done with adt's in ocaml yet, so symbolize won't work with programs that use them (in this case OPCon)"
end
