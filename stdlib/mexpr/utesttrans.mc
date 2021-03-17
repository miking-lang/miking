include "bool.mc"
include "string.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/eval.mc"
include "mexpr/type-annot.mc"
include "mexpr/utestrunner.mc"

recursive
let _consistentType =
  use MExprAst in
  use MExprEq in
  lam tyEnv. lam ty1. lam ty2.
  match (ty1, ty2) with (TyUnknown {}, _) then Some ty2
  else match (ty1, ty2) with (_, TyUnknown {}) then Some ty1
  else match (ty1, ty2) with (TyArrow t1, TyArrow t2) then
    match _consistentType tyEnv t1.from t2.from with Some a then
      match _consistentType tyEnv t1.to t2.to with Some b then
        Some (TyArrow {from = a, to = b})
      else None ()
    else None ()
  else match (ty1, ty2) with (TySeq t1, TySeq t2) then
    match _consistentType tyEnv t1.ty ty2.ty with Some t then
      Some (TySeq {ty = t})
    else None ()
  else if eqType tyEnv ty1 ty2 then Some ty1
  else None ()
end

recursive let _seqPrintFunc = lam ty.
  use MExprAst in
  match ty with TyInt {} then
    int2string
  else match ty with TyBool {} then
    lam b. if b then "true" else "false"
  else match ty with TySeq {ty = innerTy} then
    lam seq.
      join ["[", strJoin "," (map (_seqPrintFunc innerTy) seq), "]"]
  else dprintLn ty; error "Unsupported sequence element type"
end

recursive let _seqEqFunc = lam ty.
  use MExprAst in
  match ty with TyInt {} then
    eqi
  else match ty with TyBool {} then
    eqBool
  else match ty with TySeq {ty = innerTy} then
    eqSeq (_seqEqFunc innerTy)
  else dprintLn ty; error "Unsupported sequence element type"
end

-- NOTE(linnea, 2021-03-17): Assumes that typeAnnot has been called prior to the
-- transformation.
lang MExprUtestTrans = MExprAst
  sem utestStripH =
  | TmUtest t -> utestStripH t.next
  | t -> smap_Expr_Expr utestStripH t

  sem utestStrip =
  | t -> utestStripH t

  sem utestGenH =
  | TmUtest t ->
    bind_ (ulet_ "" (app_ (
    match _consistentType assocEmpty (ty t.test) (ty t.expected) with Some ty then
      match ty with TyInt {} then
        utestInt t.info t.test t.expected
      else match ty with TyBool {} then
        utestBool t.info t.test t.expected
      else match ty with TySeq _ then
        let printFunc = _seqPrintFunc ty in
        let eqFunc = _seqEqFunc ty in
        utestSeq t.info printFunc eqFunc t.test t.expected
      else dprintLn ty; error "Unsupported utest argument types"
    else error "Type error") unit_))
    t.next
  | t -> smap_Expr_Expr utestGenH t

  sem utestGen =
  | t -> utestGenH t
end

lang TestLang = MExprUtestTrans + MExprEq + MExprTypeAnnot + MExprEval

mexpr

use TestLang in

let default_info =
  Info { filename = "utesttrans.mc"
       , row1 = 0, col1 = 0, row2 = 0, col1 = 0}
in

let utest_info_ =
  lam t. lam e. lam n.
  TmUtest { test = t
          , expected = e
          , next = n
          , ty = TyUnknown {}
          , info = default_info}
in

let t = typeAnnot (utest_info_ (int_ 0) (int_ 0) unit_) in
--utest utestGen t with t using eqExpr in
eval {env = []} (utestGen t);
utest utestStrip t with unit_ using eqExpr in
()
