include "map.mc"

include "mexpr/ast.mc"

include "mlang/ast.mc"
include "mlang/pprint.mc"

include "extrec/ast.mc"

type CosemTyAnnotContext = {
  baseMap : Map Name Name,
  tyAnnotMap : Map Name (use Ast in Type)
}

lang CosemTyAnnot = MLangAst + MLangPrettyPrint + ExtRecAst
  sem handleCosemTyAnnot : Map Name Name -> MLangProgram -> MLangProgram
  sem handleCosemTyAnnot baseMap =
  | prog ->
    let ctx = { baseMap = baseMap, tyAnnotMap = mapEmpty nameCmp} in
    match mapAccumL handleCosemTyAnnot_Decl ctx prog.decls
    with (_, decls) in

    {prog with decls = decls}

  sem handleCosemTyAnnot_Decl : CosemTyAnnotContext -> Decl -> (CosemTyAnnotContext, Decl)
  sem handleCosemTyAnnot_Decl ctx =
  | DeclCosem d ->
    match mapLookup d.ident ctx.baseMap with Some baseIdent in
    if d.isBase then
      ({ctx with tyAnnotMap = mapInsert baseIdent d.tyAnnot ctx.tyAnnotMap},
       DeclCosem {d with targetTyIdent = extractCosemTarget (d.info, d.ident) d.tyAnnot})
    else
      let tyAnnot = match mapLookup baseIdent ctx.tyAnnotMap
                    with Some tyAnnot then tyAnnot
                    else errorSingle [d.info] (join [
                      "* The cosem ", (nameGetStr d.ident), " is not a base cosem and does ",
                      "not have a type annotation!\n",
                      "* Please provide a type annotation for the cosem at the",
                      " base declaration."
                    ]) in
       (ctx, DeclCosem {d with tyAnnot = tyAnnot,
                               targetTyIdent = extractCosemTarget (d.info, d.ident) tyAnnot})
  | other ->
    (ctx, other)
  | DeclLang d ->
    match mapAccumL handleCosemTyAnnot_Decl ctx d.decls with (ctx, decls) in
    (ctx, DeclLang {d with decls = decls})

  sem extractCosemTarget : (Info, Name) -> Type -> Name
  sem extractCosemTarget ctx =
  | TyAll t -> extractCosemTarget ctx t.ty
  | TyArrow t -> extractCosemTarget ctx t.to
  | TyApp t -> extractCosemTarget ctx t.rhs
  | TyCon t -> t.ident
  | other ->
    errorSingle [ctx.0] (join [
      "* The base declaration of must have a type annotation!\n",
      "* Furthermore, the return type of a cosem type annotation should be an erec, but found: '\n",
      (type2str other),
      "'\n",
      "* Please provide an appropriate type annotation for the cosem at its base",
      "declaration."
    ])
end