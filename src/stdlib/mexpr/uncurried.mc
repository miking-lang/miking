include "ast.mc"
include "pprint.mc"
include "type-check.mc"
include "symbolize.mc"
include "mlang/loader.mc"

lang UncurriedAst = Ast
    syn Expr =
  | TmUncurriedApp
    { f : Expr
    , positional : [Expr]
    , info : Info
    , ty : Type
    }
  | TmUncurriedLam
    { positional : [{ident : Name, tyAnnot : Type, tyParam : Type, info : Info}]
    , body : Expr
    , info : Info
    , ty : Type
    }

  sem infoTm =
  | TmUncurriedApp x -> x.info
  sem tyTm =
  | TmUncurriedApp x -> x.ty
  sem withInfo info =
  | TmUncurriedApp x -> TmUncurriedApp {x with info = info}
  sem withType ty =
  | TmUncurriedApp x -> TmUncurriedApp {x with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmUncurriedApp x ->
    match f acc x.f with (acc, newF) in
    match mapAccumL f acc x.positional with (acc, positional) in
    (acc, TmUncurriedApp {x with f = newF, positional = positional})

  sem infoTm =
  | TmUncurriedLam x -> x.info
  sem tyTm =
  | TmUncurriedLam x -> x.ty
  sem withInfo info =
  | TmUncurriedLam x -> TmUncurriedLam {x with info = info}
  sem withType ty =
  | TmUncurriedLam x -> TmUncurriedLam {x with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmUncurriedLam x ->
    match f acc x.body with (acc, body) in
    (acc, TmUncurriedLam {x with body = body})

  sem smapAccumL_Expr_Type f acc =
  | TmUncurriedLam x ->
    let f = lam acc. lam param.
      match f acc param.tyAnnot with (acc, tyAnnot) in
      (acc, {param with tyAnnot = tyAnnot}) in
    match mapAccumL f acc x.positional with (acc, positional) in
    (acc, TmUncurriedLam {x with positional = positional})

  sem smapAccumL_Expr_TypeLabel f acc =
  | TmUncurriedLam x ->
    match f acc x.ty with (acc, ty) in
    let f = lam acc. lam param.
      match f acc param.tyParam with (acc, tyParam) in
      (acc, {param with tyParam = tyParam}) in
    match mapAccumL f acc x.positional with (acc, positional) in
    (acc, TmUncurriedLam {x with positional = positional, ty = ty})

  syn Type =
  | TyUncurriedArrow
    { positional : [Type]
    , ret : Type
    , info : Info
    }

  sem infoTy =
  | TyUncurriedArrow x -> x.info
  sem tyWithInfo info =
  | TyUncurriedArrow x -> TyUncurriedArrow {x with info = info}

  sem smapAccumL_Type_Type f acc =
  | TyUncurriedArrow x ->
    match mapAccumL f acc x.positional with (acc, positional) in
    match f acc x.ret with (acc, ret) in
    (acc, TyUncurriedArrow {x with positional = positional, ret = ret})
end

lang UncurriedToJson = AstToJson + UncurriedAst
  sem exprToJson =
  | TmUncurriedApp x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmUncurriedApp")
    , ("positional", JsonArray (map exprToJson x.positional))
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )
  | TmUncurriedLam x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TmUncurriedLam")
    , ( "positional"
      , let f = lam x. JsonObject (mapFromSeq cmpString
          [ ("ident", nameToJson x.ident)
          , ("tyAnnot", typeToJson x.tyAnnot)
          , ("tyParam", typeToJson x.tyParam)
          , ("info", infoToJson x.info)
          ] ) in
        JsonArray (map f x.positional)
      )
    , ("body", exprToJson x.body)
    , ("ty", typeToJson x.ty)
    , ("info", infoToJson x.info)
    ] )

  sem typeToJson =
  | TyUncurriedArrow x -> JsonObject (mapFromSeq cmpString
    [ ("con", JsonString "TyUncurriedArrow")
    , ("positional", JsonArray (map typeToJson x.positional))
    , ("ret", typeToJson x.ret)
    , ("info", infoToJson x.info)
    ] )
end

lang LowerUncurried = UncurriedAst + LamAst + OpaqueAst
  sem lowerUncurried : Expr -> Expr
  sem lowerUncurried =
  | tm & TmOpaque _ -> tm
  | tm ->
    let tm = smap_Expr_Expr lowerUncurried tm in
    let tm = smap_Expr_Type lowerUncurriedType tm in
    let tm = smap_Expr_TypeLabel lowerUncurriedType tm in
    tm
  | TmUncurriedApp x ->
    let args = x.positional in
    let args = map lowerUncurried args in
    let args = if null args then [withType tyunit_ unit_] else args in
    match
      let f = lam fullTy. lam arg.
        (tyarrow_ (tyTm arg) fullTy, (arg, fullTy)) in
      mapAccumR f x.ty args
    with (fullTy, argsWithResTy) in
    foldl
      (lam tm. lam argPair. withType argPair.1 (app_ tm argPair.0))
      (withType fullTy (lowerUncurried x.f))
      argsWithResTy
  | TmUncurriedLam x ->
    let params = x.positional in
    let params = if null params
      then [{ident = nameSym "", tyAnnot = tyunit_, tyParam = tyunit_, info = x.info}]
      else params in
    let mkLam = lam param. lam body.
      let tyParam = lowerUncurriedType param.tyParam in
      TmLam
      { ident = param.ident
      , tyAnnot = lowerUncurriedType param.tyAnnot
      , tyParam = tyParam
      , info = param.info
      , body = lowerUncurried body
      , ty = tyarrow_ tyParam (tyTm body)
      } in
    foldr mkLam (lowerUncurried x.body) params

  sem lowerUncurriedType : Type -> Type
  sem lowerUncurriedType =
  | ty -> smap_Type_Type lowerUncurriedType ty
  | TyUncurriedArrow x ->
    let params = x.positional in
    let params = map lowerUncurriedType params in
    let params = if null params then [tyunit_] else params in
    foldr tyarrow_ x.ret params
end

lang LowerUncurryLoader = LowerUncurried + MCoreLoader
  syn Hook =
  | LowerUncurryHook ()

  sem _postTypecheck loader decl = | LowerUncurryHook _ ->
    let decl = smap_Decl_Expr lowerUncurried decl in
    let decl = smap_Decl_Type lowerUncurriedType decl in
    (loader, decl)
end

lang UncurriedPrettyPrint = PrettyPrint + UncurriedAst
  sem typePrecedence =
  | TyUncurriedArrow _ -> 0

  sem getTypeStringCode indent env =
  | TyUncurriedArrow x ->
    match mapAccumL (getTypeStringCode indent) env x.positional with (env, positional) in
    match printTypeParen indent 1 env x.ret with (env, ret) in
    (env, join ["(", strJoin ", " positional, ") => ", ret])
end

lang SymUncurried = Sym + UncurriedAst + VarSym
  sem symbolizeExpr env =
  | TmUncurriedLam x ->
    let f = lam varEnv. lam param.
      match setSymbol varEnv param.ident with (varEnv, ident) in
      (varEnv, {param with ident = ident, tyAnnot = symbolizeType env param.tyAnnot}) in
    match mapAccumL f env.currentEnv.varEnv x.positional with (varEnv, positional) in
    let env = symbolizeUpdateVarEnv env varEnv in
    TmUncurriedLam {x with positional = positional, body = symbolizeExpr env x.body}
end

lang UncurriedTypeCheck = TypeCheck + UncurriedAst + ResolveType + SubstituteUnknown + SubstituteNewReprs
  sem typeCheckExpr env =
  | TmUncurriedLam x ->
    let f = lam env. lam param.
      let tyAnnot = resolveType param.info env false param.tyAnnot in
      let tyAnnot = substituteNewReprs env tyAnnot in
      let tyParam = substituteUnknown param.info env (Mono ()) tyAnnot in
      (_insertVar param.ident tyParam env, {param with tyAnnot = tyAnnot, tyParam = tyParam}) in
    match mapAccumL f env x.positional with (env, positional) in
    let body = typeCheckExpr env x.body in
    let ty = TyUncurriedArrow
      { positional = map (lam param. param.tyParam) positional
      , ret = tyTm body
      , info = x.info
      } in
    TmUncurriedLam {x with positional = positional, body = body, ty = ty}
  | TmUncurriedApp x ->
    let f = typeCheckExpr env x.f in
    let positional = map (typeCheckExpr env) x.positional in
    let retTy = newpolyvar env.currentLvl x.info in
    let positionalTys = map (lam arg. newpolyvar env.currentLvl (infoTm arg)) positional in
    let expected = TyUncurriedArrow
      { positional = positionalTys
      , ret = retTy
      , info = x.info
      } in
    unify env [infoTm f] expected (tyTm f);
    iter2 (lam pos. lam ty. unify env [infoTm pos] ty (tyTm pos)) positional positionalTys;
    TmUncurriedApp {x with f = f, positional = positional, ty = retTy}
end

lang UnifyUncurried = Unify + UncurriedAst
  syn UnifyError =
  | NumArguments (Int, Int)

  sem unifyBase u env =
  | (TyUncurriedArrow a, TyUncurriedArrow b) ->
    let aLen = length a.positional in
    let bLen = length b.positional in
    let lengths = if neqi aLen bLen
      then u.err (NumArguments (aLen, bLen))
      else u.empty in
    let positional =
      let f = lam res. lam l. lam r. u.combine res (unifyTypes u env (l, r)) in
      foldl2 f u.empty a.positional b.positional in
    u.combine lengths (u.combine positional (unifyTypes u env (a.ret, b.ret)))
end

lang PprintUnifyErrorNumArguments = UnifyUncurried + TCUnify
  sem pprintUnifyError env =
  | NumArguments (l, r) ->
    (env, join ["different number of arguments, ", int2string l, " != ", int2string r])
end

lang UnifyUncurriedMixed = Unify + UncurriedAst + UnifyUncurried + FunTypeAst
  sem unifyBase u env =
  | (TyArrow a, b & TyUncurriedArrow _) ->
    unifyBase u env (TyUncurriedArrow {positional = [a.from], ret = a.to, info = a.info}, b)
  | (a & TyUncurriedArrow _, TyArrow b) ->
    unifyBase u env (a, TyUncurriedArrow {positional = [b.from], ret = b.to, info = b.info})
end
