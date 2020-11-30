include "ocaml/ast.mc"
include "mexpr/symbolize.mc"

lang OCamlSym =
  VarSym + AppSym + FunSym + LetSym + RecLetsSym + ConstSym
  + NamedPatSym + IntPatSym + CharPatSym + BoolPatSym
  + OCamlMatch

  sem symbolizeExpr (env : Env) =
  | OTmMatch {target = target, arms = arms} ->
    let symbArm = lam arm. match arm with (pat, expr) then
      match symbolizePat env assocEmpty pat with (patEnv, pat) then
        (pat, symbolizeExpr (_symOverwrite env patEnv) expr)
      else never else never in
    OTmMatch { target = symbolizeExpr env target, arms = map symbArm arms }
end
