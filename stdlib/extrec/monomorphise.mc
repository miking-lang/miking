include "mexpr/type-check.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "mlang/compile.mc"

include "ast.mc"
include "ast-builder.mc"

include "map.mc"
include "stringid.mc"
include "set.mc"

lang ExtRecMonomorphise = MLangAst + MExprAst + ExtRecAst
  sem monomorhpisePat env =
  | PatExtRecord p ->
    let bindings = mapMap (monomorhpisePat env) p.bindings in
    PatRecord {bindings = bindings,
               info = p.info,
               ty = p.ty}
  | p ->
    smap_Pat_Pat (monomorhpisePat env) p

  sem monomorphiseExpr : ExtRecEnvType -> Expr -> Expr
  sem monomorphiseExpr env =
  | TmRecType t ->
    match mapLookup t.ident env.defs with Some labelToType in

    let fields = mapFoldWithKey
      (lam acc. lam label. lam pair.
        match pair with (_, TyAbs {body = ty}) in
        recursive let work = lam ty.
          match ty with TyAbs t then work t.body else ty in
        let ty = work ty in
        let ty = removeExtRecTypes_Type env ty in
        mapInsert (stringToSid label) ty acc)
      (mapEmpty cmpSID)
      labelToType
    in

    TmType {ident = t.ident,
             -- params = cons mapParamIdent t.params,
            params = t.params,
            tyIdent = TyRecord {info = NoInfo (), fields = fields},
            inexpr = monomorphiseExpr env t.inexpr,
            ty = t.ty,
            info = t.info}
  | TmRecField t -> monomorphiseExpr env t.inexpr
  | TmExtRecord t ->
    match mapLookup t.ident env.defs with Some labelToType in

    let allLabels = mapKeys labelToType in
    let presentLabels = setOfKeys t.bindings in

    let f = lam label.
      if setMem label presentLabels then
        match mapLookup label t.bindings with Some e in
        (stringToSid label, e)
      else
        (stringToSid label, placeholder_)
    in

    let bindings = map f allLabels in
    let bindings = mapFromSeq cmpSID bindings in

    let bindings = mapMap (monomorphiseExpr env) bindings in

    TmRecord {bindings = bindings,
              ty = tyunknown_,
              info = t.info}
  | TmExtExtend t ->
    let work = lam acc. lam label. lam expr.
      TmRecordUpdate {rec = acc,
                      key = stringToSid label,
                      value = expr,
                      ty = tyunknown_,
                      info = t.info} in
    mapFoldWithKey work t.e t.bindings
  | expr ->
    let expr = smap_Expr_Pat (monomorhpisePat env) expr in
    smap_Expr_Expr (monomorphiseExpr env) expr

  sem _inspectTyWithinAlias2 : Type -> Type
  sem _inspectTyWithinAlias2 =
  | TyAlias {content = content} -> _inspectTyWithinAlias2 content
  | TyApp t -> _inspectTyWithinAlias2 t.rhs
  | ty -> ty


  sem removeExtRecTypes_Expr env =
  | TmType t ->
    -- We need to remove the first parameter from TmTypes representing
    -- open sum types or payloads. Type aliases should remain unaffected.
    if or (setMem t.ident env.sumTypeNames) (setMem t.ident env.payloadNames) then
      TmType {t with params = tail t.params,
                    tyIdent = removeExtRecTypes_Type env t.tyIdent,
                    ty = removeExtRecTypes_Type env t.ty,
                    inexpr = removeExtRecTypes_Expr env t.inexpr}
    else
      TmType {t with tyIdent = removeExtRecTypes_Type env t.tyIdent,
                     ty = removeExtRecTypes_Type env t.ty,
                     inexpr = removeExtRecTypes_Expr env t.inexpr}
  | expr ->
    let expr = smap_Expr_Type (removeExtRecTypes_Type env) expr in
    let expr = smap_Expr_TypeLabel (removeExtRecTypes_Type env) expr in
    smap_Expr_Expr (removeExtRecTypes_Expr env) expr

  sem removeExtRecTypes_Type env =
  | TyQualifiedName t ->
    TyCon {ident = t.rhs, info = t.info, data = tyunknown_}
  | TyCon t ->
    TyCon {t with data = tyunknown_}
  | TyAll t & ty ->
    match t.kind with Data _ then
      removeExtRecTypes_Type env t.ty
    else if eqString (nameGetStr t.ident) "M" then
      removeExtRecTypes_Type env t.ty
    else
      TyAll {t with ty = removeExtRecTypes_Type env t.ty,
                    kind = removeExtRecTypes_Kind env t.kind}
  | ty ->
    smap_Type_Type (removeExtRecTypes_Type env) ty

  sem removeExtRecTypes_Kind env =
  sem removeExtRecTypes_Kind =
  | Data k & kind ->
    Poly ()
  | kind ->
    smap_Kind_Type (removeExtRecTypes_Type env) kind
end