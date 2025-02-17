include "mlang/ast.mc"
include "mlang/ast-builder.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "ast.mc"

include "name.mc"
include "set.mc"
include "map.mc"

let implicitParamIdent = nameSym "M"

lang InsertImplictRecursionVar = MLangAst + MExprAst + ExtRecAst
  type ExtensibleNamesCtx = {
    sumTypeNames : Set Name,
    prodTypeNames : Set Name
  }

  sem collectExtensibleTypes : ExtensibleNamesCtx -> Decl -> ExtensibleNamesCtx
  sem collectExtensibleTypes ctx =
  | DeclSyn d ->
    if null d.includes then
      {ctx with sumTypeNames = setInsert d.ident ctx.sumTypeNames}
    else
      ctx
  | DeclCosyn d ->
    if d.isBase then
      {ctx with prodTypeNames = setInsert d.ident ctx.prodTypeNames}
    else
      ctx
  | other ->
    sfold_Decl_Decl collectExtensibleTypes ctx other

  sem insertImplicitParam_Type : ExtensibleNamesCtx -> Type -> Type
  sem insertImplicitParam_Type ctx =
  | TyCon t & ty ->
    if setMem t.ident ctx.prodTypeNames then
      TyCon {t with data = intyvar_ t.info implicitParamIdent}
    else if setMem t.ident ctx.sumTypeNames then
      TyCon {t with data = intyvar_ t.info implicitParamIdent}
    else
      ty
  | TyAlias t ->
    TyAlias {t with content = insertImplicitParam_Type ctx t.content}
  | ty ->
    smap_Type_Type (insertImplicitParam_Type ctx) ty

  sem insertImplicitParam_Decl : ExtensibleNamesCtx -> Decl -> Decl
  sem insertImplicitParam_Decl ctx =
  | DeclConDef d ->
    let tyIdent = TyAll {info = infoTy d.tyIdent,
                         ident = implicitParamIdent,
                         kind = Data {types = mapEmpty nameCmp},
                         ty = d.tyIdent} in
    let tyIdent = insertImplicitParam_Type ctx tyIdent in
    DeclConDef {d with tyIdent = tyIdent}
  | DeclCosyn d ->
    DeclCosyn {d with params = cons implicitParamIdent d.params,
                      ty = insertImplicitParam_Type ctx d.ty}
  | SynDeclProdExt d ->
    let params = cons implicitParamIdent d.params in
    let globalExt = optionMap (insertImplicitParam_Type ctx) d.globalExt in
    let individualExts = map
      (lam e. {e with tyIdent = insertImplicitParam_Type ctx e.tyIdent})
      d.individualExts in
    SynDeclProdExt {d with params = params,
                           globalExt = globalExt,
                           individualExts = individualExts}
  | DeclSyn d ->
    let params = cons implicitParamIdent d.params in
    let work = lam def.
      {def with tyIdent = insertImplicitParam_Type ctx def.tyIdent} in
    let defs = map work d.defs  in
    DeclSyn {d with params = params,
                    defs = defs}
  | decl ->
    smap_Decl_Decl (insertImplicitParam_Decl ctx) decl

  sem insertImplicitParams : MLangProgram -> MLangProgram
  sem insertImplicitParams =
  | prog ->
    let ctx = {sumTypeNames = setEmpty nameCmp,
               prodTypeNames = setEmpty nameCmp} in
    let ctx = foldl collectExtensibleTypes ctx prog.decls in
    {prog with decls = map (insertImplicitParam_Decl ctx) prog.decls}
end