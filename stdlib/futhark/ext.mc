-- Simple support to allow using the sin and cos externals as defined in
-- math.mc in the Futhark backend.

include "set.mc"
include "futhark/ast.mc"

let extMap = mapFromSeq cmpString
  [("externalSin", nameSym "f64.sin"), ("externalCos", nameSym "f64.cos")]
let extNames = setOfSeq nameCmp (mapValues extMap)

lang FutharkExternal = MExprAst
  sem replaceSinCosExternals : Expr -> Expr
  sem replaceSinCosExternals =
  | TmVar t ->
    let str = nameGetStr t.ident in
    match mapLookup str extMap with Some id then
      TmVar {t with ident = id}
    else TmVar t
  | TmExt t ->
    let str = nameGetStr t.ident in
    match mapLookup str extMap with Some id then
      replaceSinCosExternals t.inexpr
    else TmExt {t with inexpr = replaceSinCosExternals t.inexpr}
  | t -> smap_Expr_Expr replaceSinCosExternals t
end
