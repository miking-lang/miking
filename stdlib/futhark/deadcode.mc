-- Performs deadcode elimination within top-level Futhark functions.

include "name.mc"
include "set.mc"
include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

lang FutharkDeadcodeElimination = FutharkAst
  sem deadcodeEliminationExpr (used : Set Name) =
  | FEVar t -> (setInsert t.ident used, FEVar t)
  | FELet t ->
    match deadcodeEliminationExpr used t.inexpr with (used, inexpr) then
      if setMem t.ident used then
        match deadcodeEliminationExpr used t.body with (used, body) then
          match inexpr with FEVar {ident = id} then
            if nameEq t.ident id then (used, body)
            else (used, FELet {{t with body = body} with inexpr = inexpr})
          else (used, FELet {{t with body = body} with inexpr = inexpr})
        else never
      else (used, inexpr)
    else never
  | t -> smapAccumL_FExpr_FExpr deadcodeEliminationExpr used t

  sem deadcodeEliminationDecl =
  | FDeclFun t ->
    match deadcodeEliminationExpr (setEmpty nameCmp) t.body with (_, body) then
      FDeclFun {t with body = body}
    else never
  | t -> t

  sem deadcodeElimination =
  | FProg t -> FProg {t with decls = map deadcodeEliminationDecl t.decls}
end

lang TestLang = FutharkDeadcodeElimination + FutharkPrettyPrint

mexpr

use TestLang in

let futFunction = lam body.
  let fun = FDeclFun {
    ident = nameSym "x", entry = true, typeParams = [], params = [],
    ret = futUnknownTy_, body = body, info = NoInfo ()} in
  FProg {decls = [fun]}
in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let w = nameSym "w" in
let t = futFunction (futBindall_ [
  nuFutLet_ x (futInt_ 2),
  nuFutLet_ y (futInt_ 3),
  nuFutLet_ z (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 4]),
  nuFutLet_ w (futAppSeq_ (futConst_ (FCMul ())) [futInt_ 7, nFutVar_ y]),
  nFutVar_ z]) in
let expected = futFunction (futBindall_ [
  nuFutLet_ x (futInt_ 2),
  futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 4]]) in
utest printFutProg (deadcodeElimination t) with printFutProg expected using eqString in

let f = nameSym "f" in
let t = futFunction (futBindall_ [
  nuFutLet_ f (nFutLam_ x (nFutLam_ y (futBindall_ [
    nuFutLet_ z (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, nFutVar_ y]),
    nFutVar_ z
  ]))),
  futUnit_ ()]) in
let expected = futFunction (futUnit_ ()) in
utest printFutProg (deadcodeElimination t) with printFutProg expected using eqString in

let i = nameSym "i" in
let t = futFunction (futBindall_ [
  nuFutLet_ x (futInt_ 0),
  nuFutLet_ y (futArray_ [futInt_ 2, futInt_ 7]),
  futForEach_
    (nFutPvar_ x, nFutVar_ x)
    i
    (nFutVar_ y)
    (futBindall_ [
      nuFutLet_ z (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, nFutVar_ i]),
      nuFutLet_ w (nFutVar_ z),
      nFutVar_ w])]) in
let expected = futFunction (futBindall_ [
  nuFutLet_ x (futInt_ 0),
  nuFutLet_ y (futArray_ [futInt_ 2, futInt_ 7]),
  futForEach_
    (nFutPvar_ x, nFutVar_ x)
    i
    (nFutVar_ y)
    (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, nFutVar_ i])]) in
utest printFutProg (deadcodeElimination t) with printFutProg expected using eqString in

()
