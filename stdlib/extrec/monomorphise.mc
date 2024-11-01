include "mexpr/type-check.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "mlang/compile.mc"

include "map.mc"
include "stringid.mc"
include "set.mc"

lang ExtRecMonomorphise = RecordAst + ExtRecordAst + MatchAst + 
                          MExprAst + MExprPrettyPrint +
                          TypeAbsAst + ExtRecordPat

  sem updateNames_expr names = 
  | expr ->
    let names = sfold_Expr_Expr updateNames_expr names expr in  
    sfold_Expr_Pat updateNames_pat names expr 

  sem updateNames_pat names = 
  | PatExtRecord p -> 
    let work = lam acc. lam. lam p. 
      match p with PatNamed {ident = PName n} then 
        mapInsert n 1 acc 
      else
        updateNames_pat acc p
    in 
    mapFoldWithKey work names p.bindings 
  | p ->
    sfold_Pat_Pat updateNames_pat names p

  sem monomorhpisePat env names =
  | PatExtRecord p -> 
    let bindings = mapMap (monomorhpisePat env names) p.bindings in 
    PatRecord {bindings = bindings,
               info = p.info,
               ty = p.ty}
  | p ->
    smap_Pat_Pat (monomorhpisePat env names) p

  sem monomorphiseExpr : ExtRecEnvType -> Map Name Int -> Expr -> Expr
  sem monomorphiseExpr env names = 
  | TmRecType t -> 
    match mapLookup t.ident env.defs with Some labelToType in 

    let fields = mapFoldWithKey 
      (lam acc. lam label. lam pair.
        match pair with (_, TyAbs {body = ty}) in 
        recursive let work = lam ty.
          match ty with TyAbs t then work t.body else ty in 
        let ty = work ty in 
        let ty = removeExtRecTypes_Type () ty in 
        let ty = TyArrow {info = NoInfo (),
                          from = tyunit_,
                          to = ty} in 
        mapInsert (stringToSid label) ty acc) 
      (mapEmpty cmpSID)
      labelToType
    in 

    TmType {ident = t.ident,
             -- params = cons mapParamIdent t.params,
            params = t.params,
            tyIdent = TyRecord {info = NoInfo (), fields = fields},
            inexpr = monomorphiseExpr env names t.inexpr,
            ty = t.ty,
            info = t.info}
  | TmRecField t -> monomorphiseExpr env names t.inexpr 
  | TmRecordUpdate t & tm -> 
    match tyTm t.rec with TyCon tyCon then 
      TmRecordUpdate {t with value = nulam_ (nameNoSym "") t.value,
                             rec = monomorphiseExpr env names t.rec}
    else 
      tm 
  | TmExtRecord t -> 
    match mapLookup t.ident env.defs with Some labelToType in 

    let allLabels = mapKeys labelToType in 
    let presentLabels = setOfKeys t.bindings in 

    let f = lam label.
      if setMem label presentLabels then 
        match mapLookup label t.bindings with Some e in (stringToSid label, ulam_ "" e)
      else 
        (stringToSid label, ulam_ "" never_)
    in 

    let bindings = map f allLabels in 
    let bindings = mapFromSeq cmpSID bindings in 

    let bindings = mapMap (monomorphiseExpr env names) bindings in 

    TmRecord {bindings = bindings,
              ty = tyunknown_,
              info = t.info}
  | TmExtExtend t -> 
    let work = lam acc. lam label. lam expr. 
      TmRecordUpdate {rec = acc, 
                      key = stringToSid label, 
                      value = nulam_ (nameNoSym "") expr, 
                      ty = tyunknown_,
                      info = t.info} in 
    mapFoldWithKey work t.e t.bindings
  | TmVar t & tm -> 
    match mapLookup t.ident names with Some depth then
      let units = make depth uunit_ in 
      appSeq_ tm units 
    else 
      tm
  -- | TmMatch t & tm ->
  --   printLn "Encountered match!";
  --   printLn (type2str (_inspectTyWithinAlias2 (tyTm t.target)));
  --   match _inspectTyWithinAlias2 (tyTm t.target) with TyExtRec extRec then
  --     printLn "\tEncountered correct Target!";
  --     match t.pat with PatRecord patRec & p then
  --       printLn "\t\tEncountered correct pattern!";
  --       recursive let collectBoundNames = lam acc. lam pat. 
  --         match pat with PatNamed {ident = PName ident} then setInsert ident acc 
  --         else sfold_Pat_Pat collectBoundNames acc pat
  --       in
  --       let boundNames = collectBoundNames (setEmpty nameCmp) p in 
  --       iter (lam n. printLn (nameGetStr n)) (setToSeq boundNames) ;
  --       tm
  --     else
  --       errorSingle [t.info] " * This match is too complicated for crude monomorhpization."
  --   else
  --     tm
  | expr -> 
    let expr = smap_Expr_Pat (monomorhpisePat env names) expr in 
    smap_Expr_Expr (monomorphiseExpr env names) expr
  
  sem _inspectTyWithinAlias2 : Type -> Type
  sem _inspectTyWithinAlias2 = 
  | TyAlias {content = content} -> _inspectTyWithinAlias2 content
  | TyApp t -> _inspectTyWithinAlias2 t.rhs
  | ty -> ty


  sem removeExtRecTypes_Expr env = 
  | TmType t ->
    TmType {t with params = tail t.params,
                   tyIdent = removeExtRecTypes_Type env t.tyIdent,
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
  -- | TyApp {lhs = TyCon t, rhs = TyVar _} ->
  --   TyCon{t with data = tyunknown_}
  -- | TyApp {rhs = TyVar tyVar} & TyApp t ->
  --   if eqString (nameGetStr tyVar.ident) "M" then
  --     removeExtRecTypes_Type env t.lhs 
  --   else if eqString (nameGetStr tyVar.ident) "ss" then
  --     removeExtRecTypes_Type env t.lhs 
  --   else 
  --     TyApp {t with lhs = removeExtRecTypes_Type env t.lhs,
  --                   rhs = removeExtRecTypes_Type env t.rhs}
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