include "annotate.mc"

-- NOTE(vipa, 2022-10-07): This can't use AnnotateMExprBase because it
-- has to thread a pprint environment, which AnnotateMExprBase doesn't
-- allow.
lang AstAnnot = AnnotateSources + PrettyPrint + Ast + LetAst + RecLetsAst + TypeAst + DataAst + ExtAst
  sem annotateMExpr : Expr -> Output
  sem annotateMExpr = | tm ->
    let env =
      { pprintEnv = pprintEnvEmpty
      , nextExpr = 0
      , nextPat = 0
      , nextType = 0
      , annots = []
      } in
    annotateAndReadSources (_annotateTopExpr env tm).0 .annots

  type VisAnnotEnv =
    { pprintEnv : PprintEnv
    , nextExpr : Int
    , nextType : Int
    , nextPat : Int
    , annots : [(Info, Annotation)]
    }

  syn AstNodeSource =
  | AstFromWithin Info
  | AstFromElsewhere ()
  sem _checkSource : Info -> Info -> (AstNodeSource, Info)
  sem _checkSource infoAbove = | info ->
    let source =
      switch (infoAbove, info)
      case (_, NoInfo _) then AstFromElsewhere ()
      case (NoInfo _, _) then AstFromWithin info
      case (Info above, Info here) then
        if eqString above.filename here.filename then
          let startEq = eqi above.row1 here.row1 in
          let startsAfter = if startEq
            then leqi above.col1 here.col1
            else lti above.row1 here.row1 in
          let endEq = eqi here.row2 above.row2 in
          let endsBefore = if endEq
            then leqi here.col2 above.col2
            else lti here.row2 above.row2 in
          if and startEq endEq then AstFromElsewhere ()
          else if and startsAfter endsBefore then AstFromWithin info
          else AstFromElsewhere ()
        else AstFromElsewhere ()
      end in
    (source, match source with AstFromWithin _ then info else infoAbove)

  sem _addExprAnnot : VisAnnotEnv -> Expr -> (VisAnnotEnv, Expr)
  sem _addExprAnnot env = | tm ->
    let info = infoTm tm in
    let id = join ["expr", int2string env.nextExpr] in
    match pprintCode 2 env.pprintEnv tm with (pprintEnv, tm) in
    let annot = join [id, " => ", tm] in
    let env =
      { env
      with nextExpr = addi 1 env.nextExpr
      , annots = cons (info, annot) env.annots
      , pprintEnv = pprintEnv
      } in
    (env, var_ id)

  sem _annotateTopExpr : VisAnnotEnv -> Expr -> (VisAnnotEnv, Expr)
  sem _annotateTopExpr env =
  | TmLet x ->
    match _annotateExpr x.info env x.body with (env, body) in
    match _annotateType x.info env x.tyAnnot with (env, tyAnnot) in
    match _annotateTopExpr env x.inexpr with (env, inexpr) in
    let tm = TmLet {x with body = body, tyAnnot = tyAnnot, inexpr = inexpr} in
    _addExprAnnot env tm
  | TmRecLets x ->
    let f = lam env. lam binding.
      match _annotateExpr x.info env binding.body with (env, body) in
      match _annotateType x.info env binding.tyAnnot with (env, tyAnnot) in
      (env, {binding with body = body, tyAnnot = tyAnnot}) in
    match mapAccumL f env x.bindings with (env, bindings) in
    match _annotateTopExpr env x.inexpr with (env, inexpr) in
    let tm = TmRecLets {x with bindings = bindings, inexpr = inexpr} in
    _addExprAnnot env tm
  | TmType x ->
    match _annotateType x.info env x.tyIdent with (env, tyIdent) in
    match _annotateTopExpr env x.inexpr with (env, inexpr) in
    let tm = TmType {x with tyIdent = tyIdent, inexpr = inexpr} in
    _addExprAnnot env tm
  | TmConDef x ->
    match _annotateType x.info env x.tyIdent with (env, tyIdent) in
    match _annotateTopExpr env x.inexpr with (env, inexpr) in
    let tm = TmConDef {x with tyIdent = tyIdent, inexpr = inexpr} in
    _addExprAnnot env tm
  | TmExt x ->
    match _annotateType x.info env x.tyIdent with (env, tyIdent) in
    match _annotateTopExpr env x.inexpr with (env, inexpr) in
    let tm = TmExt {x with tyIdent = tyIdent, inexpr = inexpr} in
    _addExprAnnot env tm
  | tm -> _annotateExpr (NoInfo ()) env tm

  sem _annotateExpr : Info -> VisAnnotEnv -> Expr -> (VisAnnotEnv, Expr)
  sem _annotateExpr infoAbove env = | tm ->
    match _checkSource infoAbove (infoTm tm) with (source, infoBelow) in

    match smapAccumL_Expr_Expr (_annotateExpr infoBelow) env tm with (env, tm) in
    match smapAccumL_Expr_Pat (_annotatePat infoBelow) env tm with (env, tm) in
    match smapAccumL_Expr_Type (_annotateType infoBelow) env tm with (env, tm) in

    switch source
    case AstFromElsewhere _ then (env, tm)
    case AstFromWithin _ then _addExprAnnot env tm
    end

  sem _annotatePat : Info -> VisAnnotEnv -> Pat -> (VisAnnotEnv, Pat)
  sem _annotatePat infoAbove env = | pat ->
    match _checkSource infoAbove (infoPat pat) with (source, infoBelow) in

    match smapAccumL_Pat_Expr (_annotateExpr infoBelow) env pat with (env, pat) in
    match smapAccumL_Pat_Pat (_annotatePat infoBelow) env pat with (env, pat) in
    match smapAccumL_Pat_Type (_annotateType infoBelow) env pat with (env, pat) in

    switch source
    case AstFromElsewhere _ then (env, pat)
    case AstFromWithin info then
      let id = join ["pat", int2string env.nextPat] in
      match getPatStringCode 2 env.pprintEnv pat with (pprintEnv, pat) in
      let annot = join [id, " => ", pat] in
      let env =
        { env
        with nextPat = addi 1 env.nextPat
        , annots = cons (info, annot) env.annots
        , pprintEnv = pprintEnv
        } in
      (env, pvar_ id)
    end

  sem _annotateType : Info -> VisAnnotEnv -> Type -> (VisAnnotEnv, Type)
  sem _annotateType infoAbove env = | ty ->
    match _checkSource infoAbove (infoTy ty) with (source, infoBelow) in

    match smapAccumL_Type_Type (_annotateType infoBelow) env ty with (env, ty) in

    switch source
    case AstFromElsewhere _ then (env, ty)
    case AstFromWithin info then
      let id = join ["type", int2string env.nextType] in
      match getTypeStringCode 2 env.pprintEnv ty with (pprintEnv, ty) in
      let annot = join [id, " => ", ty] in
      let env =
        { env
        with nextType = addi 1 env.nextType
        , annots = cons (info, annot) env.annots
        , pprintEnv = pprintEnv
        } in
      (env, tyvar_ id)
    end
end
