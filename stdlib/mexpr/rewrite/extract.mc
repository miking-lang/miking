-- Extracts all functions that accelerate calls within a given AST depend on,
-- and returns the extracted AST together with a map from identifiers of
-- accelerated functions to their types.

include "map.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

type ExtractAccelerateEnv = Map Name (Info, Type)

lang PMExprExtractAccelerate = MExprParallelKeywordMaker
  sem collectAccelerate (env : ExtractAccelerateEnv) =
  | TmAccelerate t ->
    let isArrowType = lam expr.
      match ty expr with TyArrow _ then true
      else false
    in
    if isArrowType t.e then
      let info = infoTm t.e in
      infoErrorExit info "Cannot accelerate partially applied function"
    else
      let appArgs = collectAppArguments t.e in
      match appArgs with (TmVar v, args) then
        if null args then
          infoErrorExit v.info "Cannot accelerate non-application term"
        else
          match find isArrowType args with Some arg then
            infoErrorExit
              (infoTm arg)
              "Cannot accelerate higher-order function argument"
          else mapInsert v.ident (infoTm t.e, v.ty) env
      else infoErrorExit t.info "Cannot accelerate anonymous function"
  | t -> sfold_Expr_Expr collectAccelerate env t

  sem collectIdentifiersExpr (used : Map Name (Info, Type)) =
  | TmVar t -> mapInsert t.ident (t.info, t.ty) used
  | t -> sfold_Expr_Expr collectIdentifiersExpr used t

  sem collectIdentifiersType (used : Map Name (Info, Type)) =
  | TyVar t -> mapInsert t.ident (t.info, tyunknown_) used
  | t -> sfold_Type_Type collectIdentifiersType used t

  sem extractAccelerateAst (used : Map Name (Info, Type)) =
  | TmLet t ->
    match extractAccelerateAst used t.inexpr with (used, inexpr) then
      if mapMem t.ident used then
        let used = sfold_Type_Type collectIdentifiersType used t.tyBody in
        let used = sfold_Expr_Expr collectIdentifiersExpr used t.body in
        (used, TmLet {t with inexpr = inexpr})
      else (used, inexpr)
    else never
  | TmRecLets t ->
    let extractBinding : (Set Name, [RecLetBinding]) -> RecLetBinding
                      -> (Set Name, [RecLetBinding]) =
      lam acc. lam binding.
      if mapMem binding.ident used then
        let used = sfold_Type_Type collectIdentifiersType used binding.tyBody in
        let used = sfold_Expr_Expr collectIdentifiersExpr acc.0 binding.body in
        (used, snoc acc.1 binding)
      else acc
    in
    match extractAccelerateAst used t.inexpr with (used, inexpr) then
      match foldl extractBinding (used, []) t.bindings with (used, bindings) then
        if null bindings then (used, inexpr)
        else
          (used, TmRecLets {{t with bindings = bindings}
                               with inexpr = inexpr})
      else never
    else never
  | TmType t ->
    match extractAccelerateAst used t.inexpr with (used, inexpr) then
      if mapMem t.ident used then
        let used = collectIdentifiersType used t.tyIdent in
        (used, TmType {t with inexpr = inexpr})
      else (used, inexpr)
    else never
  | TmConDef t ->
    match extractAccelerateAst used t.inexpr with (used, inexpr) then
      if mapMem t.ident used then
        let used = collectIdentifiersType used t.tyIdent in
        (used, TmConDef {t with inexpr = inexpr})
      else (used, inexpr)
    else never
  | TmExt t ->
    match extractAccelerateAst used t.inexpr with (used, inexpr) then
      match mapLookup t.ident used with Some (info, _) then
        infoErrorExit info "Cannot accelerate external function use"
      else (used, inexpr)
    else never
  | t -> (used, unit_)

  sem extractAccelerate =
  | t ->
    let accelerated = collectAccelerate (mapEmpty nameCmp) t in
    match extractAccelerateAst accelerated t with (_, t) then
      let accelerated = mapMap (lam p : (Info, Type). p.1) accelerated in
      (accelerated, t)
    else never
end

lang TestLang = PMExprExtractAccelerate + MExprEq + MExprTypeAnnot

mexpr

use TestLang in

let preprocess = lam t.
  typeAnnot (symbolize t)
in

let noAccelerateCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
let x : (Map Name Type, Expr) = extractAccelerate noAccelerateCalls in
utest mapSize x.0 with 0 in
utest x.1 with unit_ using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  accelerate_ (app_ (var_ "h") (int_ 2))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate t in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  accelerate_ (app_ (var_ "g") (int_ 4))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate t in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

let multipleCallsToSame = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (bindall_ [
    ulet_ "y" (addi_ (var_ "x") (int_ 2)),
    accelerate_ (app_ (var_ "f") (var_ "y"))
  ])),
  ulet_ "h" (ulam_ "x" (accelerate_ (app_ (var_ "f") (var_ "x")))),
  addi_
    (app_ (var_ "g") (int_ 1))
    (app_ (var_ "h") (int_ 3))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate multipleCallsToSame in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  addi_
    (accelerate_ (app_ (var_ "f") (int_ 1)))
    (accelerate_ (app_ (var_ "g") (int_ 0)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate distinctCalls in
utest mapSize x.0 with 2 in
utest x.1 with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "x" (accelerate_ (app_ (var_ "g") (var_ "x"))))],
  app_ (var_ "h") (int_ 3)
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1))))],
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate inRecursiveBinding in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

()
