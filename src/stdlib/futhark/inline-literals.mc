-- Performs inlining of literal values bound in let-expressions. This is needed
-- to prevent an error when the accumulated value of a loop is a record
-- containing arrays on which we perform in-place updates.

include "common.mc"
include "utest.mc"
include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

lang FutharkInlineLiterals = FutharkAst
  type InlineEnv = Map Name FutExpr

  sem inlineLiterals : FutProg -> FutProg
  sem inlineLiterals =
  | FProg t ->
    let inlineEnv = mapEmpty nameCmp in
    match mapAccumL inlineLiteralsDecl inlineEnv t.decls with (_, decls) in
    FProg {t with decls = decls}

  sem inlineLiteralsDecl : InlineEnv -> FutDecl -> (InlineEnv, FutDecl)
  sem inlineLiteralsDecl env =
  | FDeclConst t -> (mapInsert t.ident t.val env, FDeclConst t)
  | FDeclFun t -> (env, FDeclFun {t with body = inlineLiteralsExpr env t.body})
  | d -> (env, d)

  sem inlineLiteralsExpr : InlineEnv -> FutExpr -> FutExpr
  sem inlineLiteralsExpr env =
  | FEVar t ->
    match mapLookup t.ident env with Some expr then expr
    else FEVar t
  | FELet t ->
    let body = inlineLiteralsExpr env t.body in
    match body with FERecord _ | FEConst _ then
      let env = mapInsert t.ident body env in inlineLiteralsExpr env t.inexpr
    else FELet {t with body = body, inexpr = inlineLiteralsExpr env t.inexpr}
  | e -> smap_FExpr_FExpr (inlineLiteralsExpr env) e
end

lang TestLang = FutharkInlineLiterals + FutharkPrettyPrint
end

mexpr

use TestLang in

let s = nameSym "s" in
let i = nameSym "i" in
let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let fun = lam body. FDeclFun {
  ident = nameNoSym "f", entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = futRecordTy_ [("x", futIntTy_), ("y", futIntTy_)],
  body = body, info = NoInfo ()
} in
let pat = futPrecord_ [("x", nFutPvar_ x), ("y", nFutPvar_ y)] in
let loopExpr =
  futForEach_
    (pat, nFutVar_ z) i (nFutVar_ s)
    (futRecord_ [
      ("x", futAdd_ (nFutVar_ x) (nFutVar_ i)),
      ("y", futAdd_ (nFutVar_ y) (nFutVar_ i))])
in
let zRec = futRecord_ [("x", futInt_ 0), ("y", futInt_ 0)] in
let body = futBindall_ [ nuFutLet_ z zRec, loopExpr ] in
let inlinedBody =
  futForEach_ (pat, zRec) i (nFutVar_ s)
    (futRecord_ [
      ("x", futAdd_ (nFutVar_ x) (nFutVar_ i)),
      ("y", futAdd_ (nFutVar_ y) (nFutVar_ i))])
in
match inlineLiteralsDecl (mapEmpty nameCmp) (fun body) with (_, inlined) in
utest printFutProg (FProg {decls = [inlined]})
with printFutProg (FProg {decls = [fun inlinedBody]})
using eqString else utestDefaultToString identity identity in

()
