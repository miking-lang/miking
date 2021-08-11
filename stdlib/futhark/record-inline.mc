include "stringid.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"

lang FutharkRecordInline = FutharkAst
  sem inlineRecordsExpr (subMap : Map Name Expr) =
  | FEVar t ->
    match mapLookup t.ident subMap with Some expr then
      inlineRecordsExpr subMap expr
    else FEVar t
  | FELet ({body = FERecord _} & t) ->
    inlineRecordsExpr (mapInsert t.ident t.body subMap) t.inexpr
  | (t & FERecordProj ({rec = FEVar {ident = ident}, key = key})) ->
    match mapLookup ident subMap with Some (FERecord {fields = fields}) then
      match mapLookup key fields with Some expr then
        inlineRecordsExpr subMap expr
      else error (join ["Record projection references unknown field ",
                        sidToString key])
    else t
  | t -> smap_FExpr_FExpr (inlineRecordsExpr subMap) t

  sem inlineRecordsDecl =
  | FDeclFun t ->
    FDeclFun {t with body = inlineRecordsExpr (mapEmpty nameCmp) t.body}
  | t -> t

  sem inlineRecords =
  | FProg t -> FProg {t with decls = map inlineRecordsDecl t.decls}
end

lang TestLang = FutharkRecordInline + FutharkPrettyPrint

mexpr

use TestLang in

let futProgram = lam body.
  let fun = FDeclFun {
    ident = nameSym "x", entry = true, typeParams = [], params = [],
    ret = futUnknownTy_, body = body, info = NoInfo ()} in
  FProg {decls = [fun]}
in

let x = nameSym "x" in
let t = futProgram (futBindall_ [
  nuFutLet_ x (futRecord_ [("a", futInt_ 2), ("b", futInt_ 4)]),
  futRecordProj_ (nFutVar_ x) "b"]) in
let expected = futProgram (futInt_ 4) in
utest expr2str (inlineRecords t) with expr2str expected using eqSeq eqc in

()
