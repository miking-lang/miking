-- Replaces all TmAccelerate terms with a function call referring to an
-- external function (which is added to the generated OCaml code). The function
-- result, and all its arguments, are wrapped in calls to convertData to ensure
-- they have a valid OCaml type.

include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"
include "ocaml/external.mc"

lang PMExprReplaceAccelerate = MExprParallelKeywordMaker + OCamlGenerateExternal
  sem _mexprToOCamlType =
  | TySeq t -> OTyArray {info = t.info, ty = _mexprToOCamlType t.ty}
  | t -> t

  sem wrapInConvertData =
  | t ->
    let ty = ty t in
    let ocamlTy = _mexprToOCamlType ty in
    match convertData (infoTm t) emptyGenerateEnv t ty ocamlTy with (_, e) then
      e
    else never

  sem useExternalIdentifier (externals : Map Name Name) =
  | TmApp t ->
    match useExternalIdentifier externals t.lhs with (externals, lhs) then
      let rhs = wrapInConvertData t.rhs in
      (externals, TmApp {{t with lhs = lhs} with rhs = rhs})
    else never
  | TmVar t ->
    match mapLookup t.ident externals with Some extIdent then
      (externals, TmVar {t with ident = extIdent})
    else
      let extIdent = nameSym (concat (nameGetStr t.ident) "_ext") in
      let externals = mapInsert t.ident extIdent externals in
      (externals, TmVar {t with ident = extIdent})
  | t -> infoErrorExit (infoTm t) "Accelerated term must be an application"

  sem replaceAccelerateH (externals : Map Name Name) =
  | TmAccelerate t ->
    -- TODO(larshum, 2021-09-09): Call the external function using the
    -- (non-arrow typed) free variables as parameters.
    match useExternalIdentifier externals t.e with (externals, e) then
      let ty = ty e in
      let ocamlTy = _mexprToOCamlType ty in
      match convertData (infoTm e) emptyGenerateEnv e ocamlTy ty with (_, e) then
        (externals, e)
      else never
    else never
  | t -> smapAccumL_Expr_Expr replaceAccelerateH externals t

  sem replaceAccelerate (accelerated : Map Name Type) =
  | ast ->
    let externals = mapEmpty nameCmp in
    match replaceAccelerateH externals ast with (externals, ast) then
      let externalAccelerated =
        mapFromSeq nameCmp
          (zip (mapValues externals) (mapBindings accelerated))
      in
      (externalAccelerated, ast)
    else never
end
