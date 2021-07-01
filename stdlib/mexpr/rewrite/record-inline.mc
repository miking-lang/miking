-- Performs inlining of record literals. This is needed to prevent aliasing
-- issues in Futhark after translation of terms in ANF.

include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/rewrite/parallel-keywords.mc"

type RecordInlineEnv = Map Name Expr

lang MExprParallelRecordInline = MExprParallelKeywordMaker
  sem inlineRecordsH (env : RecordInlineEnv) =
  | TmVar t ->
    match mapLookup t.ident env with Some expr then
      expr
    else TmVar t
  | TmLet ({body = TmRecord _} & t) ->
    inlineRecordsH (mapInsert t.ident t.body env) t.inexpr
  | TmMatch (t & {target = TmVar {ident = varIdent},
                  pat = PatRecord {bindings = bindings},
                  thn = TmVar {ident = exprName}, els = TmNever _}) ->
    let binds : [(SID, Pat)] = mapBindings bindings in
    match binds with [(fieldLabel, PatNamed {ident = PName patName})] then
      if nameEq patName exprName then
        match mapLookup varIdent env with Some (TmRecord {bindings = binds}) then
          match mapLookup fieldLabel binds with Some expr then
            expr
          else TmMatch t
        else TmMatch t
      else TmMatch t
    else TmMatch t
  | t -> smap_Expr_Expr (inlineRecordsH env) t

  sem inlineRecords =
  | t -> inlineRecordsH (mapEmpty nameCmp) t
end

lang TestLang = MExprParallelRecordInline + MExprSym + MExprEq + MExprPrettyPrint

mexpr

use TestLang in

let rec = urecord_ [("a", int_ 2), ("b", float_ 3.14)] in
let t = symbolize (bind_ (ulet_ "x" rec) (var_ "x")) in
utest inlineRecords t with rec using eqExpr in

let matchExpr = lam target.
  match_ target (prec_ []) (int_ 1) (int_ 0) in
let t = symbolize (bindall_ [
  ulet_ "x" rec,
  matchExpr (var_ "x")
]) in
utest inlineRecords t with matchExpr rec using eqExpr in

let proj = symbolize (bindall_ [
  ulet_ "x" rec,
  recordproj_ "a" (var_ "x")
]) in
utest inlineRecords proj with int_ 2 using eqExpr in

()
