include "stringid.mc"
include "futhark/ast.mc"

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
  | FProg {decls = decls} -> FProg {decls = map inlineRecordsDecl decls}
end
