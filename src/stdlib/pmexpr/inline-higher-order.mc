-- This language fragment inlines higher-order functions of foldls that are
-- only used in one place in the program.

include "pmexpr/ast.mc"
include "pmexpr/utils.mc"

lang PMExprInlineFunctions = PMExprAst + PMExprVariableSub
  type PMExprInlineMap = Map Name (Expr, Int)

  sem _incrementUseCount : PMExprInlineMap -> Name -> PMExprInlineMap
  sem _incrementUseCount useCount =
  | id ->
    -- NOTE(larshum, 2022-08-17): Only increment count of variables bound in
    -- let-expressions, where we know the expression bound to the variable.
    match mapLookup id useCount with Some (expr, count) then
      mapInsert id (expr, addi count 1) useCount
    else useCount

  sem collectBindingUseCount : PMExprInlineMap -> Expr -> PMExprInlineMap
  sem collectBindingUseCount useCount =
  | TmVar t -> _incrementUseCount useCount t.ident
  | TmLet t ->
    let useCount = mapInsert t.ident (t.body, 0) useCount in
    let useCount = collectBindingUseCount useCount t.body in
    collectBindingUseCount useCount t.inexpr
  | t -> sfold_Expr_Expr collectBindingUseCount useCount t

  sem _repeatInline : PMExprInlineMap -> Set Name -> Expr -> (Set Name, Expr)
  sem _repeatInline useCount inlined =
  | var & (TmVar {ident = id}) ->
    match mapLookup id useCount with Some (body, 1) then
      let inlined = setInsert id inlined in
      _repeatInline useCount inlined body
    else (inlined, var)
  | app & (TmApp t) ->
    recursive let inlineAppFunction = lam inlined. lam app.
      match app with TmApp t then
        match inlineAppFunction inlined t.lhs with (inlined, lhs) in
        (inlined, TmApp {t with lhs = lhs})
      else _repeatInline useCount inlined app in
    inlineAppFunction inlined app
  | t -> (inlined, t)

  sem _applyLambdas : Expr -> Expr
  sem _applyLambdas =
  | app ->
    recursive let work = lam subMap. lam app.
      match app with TmApp (t & {rhs = TmVar {ident = id}}) then
        match work subMap t.lhs with (subMap, lhs) in
        match lhs with TmLam l then
          let infoFn = lam info.
            TmVar {ident = id, ty = tyTm t.rhs, info = info,
                   frozen = false} in
          (mapInsert l.ident infoFn subMap, l.body)
        else (subMap, lhs)
      else (subMap, app)
    in
    match work (mapEmpty nameCmp) app with (subMap, body) in
    substituteVariables subMap body

  sem inlineBindingUses : PMExprInlineMap -> Set Name -> Expr
                       -> (Set Name, Expr)
  sem inlineBindingUses useCount inlined =
  | TmApp (t & {lhs = TmConst {val = CFoldl _}, rhs = rhs}) ->
    match _repeatInline useCount inlined rhs with (inlined, rhs) in
    (inlined, TmApp {t with rhs = _applyLambdas rhs})
  | t -> smapAccumL_Expr_Expr (inlineBindingUses useCount) inlined t

  sem removeInlinedFunctions : Set Name -> Expr -> Expr
  sem removeInlinedFunctions inlined =
  | TmLet t ->
    if setMem t.ident inlined then removeInlinedFunctions inlined t.inexpr
    else TmLet {t with inexpr = removeInlinedFunctions inlined t.inexpr}
  | t -> smap_Expr_Expr (removeInlinedFunctions inlined) t

  sem inlineHigherOrderFunctions : Expr -> Expr
  sem inlineHigherOrderFunctions =
  | e ->
    let inlineMap = collectBindingUseCount (mapEmpty nameCmp) e in
    match inlineBindingUses inlineMap (setEmpty nameCmp) e with (inlined, e) in
    let e = removeInlinedFunctions inlined e in
    e
end
