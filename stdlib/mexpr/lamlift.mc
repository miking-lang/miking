-- Defines lambda lifting of MExpr AST nodes in quadratic time in the size of
-- the program.

include "digraph.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/call-graph.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/utils.mc"

type LambdaLiftState = {
  -- Variables in the current scope that can occur as free variables in the
  -- current expression.
  vars : Set Name,

  -- Functions in the current scope that can occur as free variables in the
  -- current expression.
  funs : Set Name,

  -- Contains the solutions of the functions found in funs. The solution of a
  -- function is a map from the identifiers of its free variables to their
  -- corresponding types.
  sols : Map Name (Map Name Type)
}

let emptyLambdaLiftState = {
  vars = setEmpty nameCmp,
  funs = setEmpty nameCmp,
  sols = mapEmpty nameCmp
}

-- Adds a name to all anonymous functions by wrapping them in a let-expression.
-- These are all lambda expressions that are not part of the right-hand side of
-- a let-expression or a recursive binding.
lang LambdaLiftNameAnonymous = MExprAst
  sem nameAnonymousLambdasInBody =
  | TmLam t -> TmLam {t with body = nameAnonymousLambdasInBody t.body}
  | t -> nameAnonymousLambdas t

  sem nameAnonymousLambdas =
  | TmLam t ->
    recursive let recurseInLambdaBody = lam t : Expr.
      match t with TmLam tt then
        TmLam {tt with body = recurseInLambdaBody tt.body}
      else nameAnonymousLambdas t
    in
    let lambdaName = nameSym "t" in
    let letBody = TmLam {t with body = recurseInLambdaBody t.body} in
    TmLet {ident = lambdaName, tyAnnot = ityunknown_ t.info, tyBody = t.ty, body = letBody,
           inexpr = TmVar {ident = lambdaName, ty = t.ty, info = t.info, frozen = false},
           ty = t.ty, info = t.info}
  | TmLet t ->
    TmLet {{t with body = nameAnonymousLambdasInBody t.body}
              with inexpr = nameAnonymousLambdas t.inexpr}
  | TmRecLets t ->
    let bindings =
      map
        (lam bind : RecLetBinding.
          {bind with body = nameAnonymousLambdasInBody bind.body})
        t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = nameAnonymousLambdas t.inexpr}
  | t -> smap_Expr_Expr nameAnonymousLambdas t
end

lang LambdaLiftFindFreeVariablesPat = MExprAst
  sem getFreeVariablePatName (state : LambdaLiftState) =
  | PName id -> {state with vars = setInsert id state.vars}
  | PWildcard _ -> state

  sem findFreeVariablesPat (state : LambdaLiftState) =
  | PatNamed t -> getFreeVariablePatName state t.ident
  | PatSeqEdge t ->
    let state = foldl findFreeVariablesPat state t.prefix in
    let state = getFreeVariablePatName state t.middle in
    foldl findFreeVariablesPat state t.postfix
  | p -> sfold_Pat_Pat findFreeVariablesPat state p
end

-- Finds the map of free variables of all functions, mapped to their
-- corresponding types. For recursive let-expressions, this requires solving a
-- system of set equations (as the free variables within bindings may affect
-- each other).
lang LambdaLiftFindFreeVariables =
  MExprAst + MExprCallGraph + LambdaLiftFindFreeVariablesPat

  sem findFreeVariablesInBody (state : LambdaLiftState) (fv : Map Name Type) =
  | TmVar t ->
    if setMem t.ident state.vars then
      mapInsert t.ident t.ty fv
    else if setMem t.ident state.funs then
      match mapLookup t.ident state.sols with Some funFreeVars then
        mapUnion fv funFreeVars
      else fv
    else fv
  | TmLam t ->
    let state = {state with vars = setInsert t.ident state.vars} in
    let fv = findFreeVariablesInBody state fv t.body in
      mapRemove t.ident fv
  | TmLet t ->
    let fv = findFreeVariablesInBody state fv t.body in
    findFreeVariablesInBody state fv t.inexpr
  | TmRecLets t ->
    let fv = foldl (lam fv: Map Name Type. lam bind : RecLetBinding.
      findFreeVariablesInBody state fv bind.body
    ) fv t.bindings in
    findFreeVariablesInBody state fv t.inexpr
  | t -> sfold_Expr_Expr (findFreeVariablesInBody state) fv t

  sem findFreeVariablesReclet (state : LambdaLiftState) =
  | TmLet t ->
    let state =
      match t.body with TmLam _ then
        let fv = findFreeVariablesInBody state (mapEmpty nameCmp) t.body in
        {{state with funs = setInsert t.ident state.funs}
                with sols = mapInsert t.ident fv state.sols}
      else state
    in
    findFreeVariablesReclet state t.inexpr
  | TmRecLets t ->
    let findBinding = lam state : LambdaLiftState. lam bind : RecLetBinding.
      let fv = findFreeVariablesInBody state (mapEmpty nameCmp) bind.body in
      {{state with funs = setInsert bind.ident state.funs}
              with sols = mapInsert bind.ident fv state.sols}
    in
    let state = foldl findBinding state t.bindings in
    findFreeVariablesReclet state t.inexpr
  | t -> sfold_Expr_Expr findFreeVariablesReclet state t

  sem findFreeVariables (state : LambdaLiftState) =
  | TmLam t ->
    let state = {state with vars = setInsert t.ident state.vars} in
    findFreeVariables state t.body
  | TmLet t ->
    let state =
      match t.body with TmLam _ then
        let fv = findFreeVariablesInBody state (mapEmpty nameCmp) t.body in
        {{state with funs = setInsert t.ident state.funs}
                with sols = mapInsert t.ident fv state.sols}
      else
        {state with vars = setInsert t.ident state.vars}
    in
    let state = findFreeVariables state t.body in
    findFreeVariables state t.inexpr
  | TmRecLets t ->
    recursive let propagateFunNames : LambdaLiftState -> Digraph Name Int
                                   -> [[Name]] -> LambdaLiftState =
      lam state. lam g. lam s.
      match s with [h] ++ t then
        let freeVars =
          foldl
            (lam acc. lam id.
              match mapLookup id state.sols with Some fv then
                mapUnion acc fv
              else acc)
            (mapEmpty nameCmp) h in
        let state =
          foldl
            (lam state : LambdaLiftState. lam id.
              {state with sols = mapInsert id freeVars state.sols})
            state h in
        propagateFunNames state g t
      else state
    in
    let findFreeVariablesBinding : LambdaLiftState -> RecLetBinding
                                -> LambdaLiftState =
      lam state. lam bind.
      findFreeVariables state bind.body
    in
    let state = findFreeVariablesReclet state (TmRecLets t) in
    let g : Digraph Name Int = constructCallGraph (TmRecLets t) in
    let sccs = digraphTarjan g in
    let state = propagateFunNames state g (reverse sccs) in
    let state = foldl findFreeVariablesBinding state t.bindings in
    findFreeVariables state t.inexpr
  | TmMatch t ->
    let state = findFreeVariables state t.target in
    let state = findFreeVariablesPat state t.pat in
    let state = findFreeVariables state t.thn in
    findFreeVariables state t.els
  | TmExt t ->
    let state = {state with funs = setInsert t.ident state.funs} in
    findFreeVariables state t.inexpr
  | t -> sfold_Expr_Expr findFreeVariables state t
end

lang LambdaLiftInsertFreeVariables = MExprAst
  sem updateBindingType : [(Name, Type)] -> Type -> Type
  sem updateBindingType fv =
  | TyAll t -> TyAll {t with ty = updateBindingType fv t.ty}
  | ty -> updateBindingTypeH ty (reverse fv)

  sem updateBindingTypeH : Type -> [(Name, Type)] -> Type
  sem updateBindingTypeH tyAcc =
  | [(_, ty)] ++ next ->
    let tyAcc = TyArrow {from = ty, to = tyAcc, info = infoTy ty} in
    updateBindingTypeH tyAcc next
  | [] -> tyAcc

  sem insertFreeVariablesH : Map Name (Map Name Type) -> Map Name (Info -> Expr)
                          -> Expr -> Expr
  sem insertFreeVariablesH solutions subMap =
  | TmVar t ->
    match mapLookup t.ident subMap with Some subExpr then subExpr t.info
    else TmVar t
  | TmLet (t & {body = TmLam _}) ->
    match mapLookup t.ident solutions with Some freeVars then
      let fv = mapBindings freeVars in
      let info = infoTm t.body in
      let body =
        foldr
          (lam freeVar : (Name, Type). lam body.
            TmLam {ident = freeVar.0, tyAnnot = freeVar.1, tyParam = ityunknown_ info,
                   body = body, info = info,
                   ty = TyUnknown {info = info}})
          t.body
          fv in
      let annot = optionGetOr t.tyAnnot (sremoveUnknown t.tyBody) in
      let tyBody = updateBindingType fv annot in
      let tyAnnot = if null fv then t.tyAnnot else ityunknown_ t.info in
      let subExpr = lam info.
        foldr
          (lam freeVar : (Name, Type). lam acc.
            let x = TmVar {ident = freeVar.0, ty = freeVar.1, info = info, frozen = false} in
            TmApp {lhs = acc, rhs = x, ty = TyUnknown {info = info}, info = info})
          (TmVar {ident = t.ident, ty = TyUnknown {info = info}, info = info, frozen = false})
          (reverse fv) in
      let body = insertFreeVariablesH solutions subMap body in
      let subMap = mapInsert t.ident subExpr subMap in
      TmLet {t with tyBody = tyBody, tyAnnot = tyAnnot, body = body,
                    inexpr = insertFreeVariablesH solutions subMap t.inexpr}
    else errorSingle [t.info] (join ["Found no free variable solution for ",
                                     nameGetStr t.ident])
  | TmRecLets t ->
    let addBindingSubExpression =
      lam subMap : Map Name (Info -> Expr). lam bind : RecLetBinding.
      match mapLookup bind.ident solutions with Some freeVars then
        let fv = mapBindings freeVars in
        let subExpr = lam info.
          foldr
            (lam freeVar : (Name, Type). lam acc.
              let x = TmVar {ident = freeVar.0, ty = freeVar.1,
                             info = info, frozen = false} in
              TmApp {lhs = acc, rhs = x, ty = TyUnknown {info = info}, info = info})
            (TmVar {ident = bind.ident, ty = TyUnknown {info = info}, info = info, frozen = false})
            (reverse (mapBindings freeVars)) in
        mapInsert bind.ident subExpr subMap
      else errorSingle [bind.info] (join ["Lambda lifting error: No solution found for binding ",
                                          nameGetStr bind.ident])
    in
    let insertFreeVarsBinding =
      lam subMap : Map Name (Info -> Expr). lam bind : RecLetBinding.
      match mapLookup bind.ident solutions with Some freeVars then
        let fv = mapBindings freeVars in
        let body =
          foldr
            (lam freeVar : (Name, Type). lam body.
              let info = infoTm body in
              TmLam {ident = freeVar.0, tyAnnot = freeVar.1, tyParam = ityunknown_ info,
                     body = body, info = info,
                     ty = TyUnknown {info = info}})
            bind.body fv in
        let annot = optionGetOr bind.tyAnnot (sremoveUnknown bind.tyBody) in
        let tyBody = updateBindingType fv annot in
        let tyAnnot = if null fv then bind.tyAnnot else ityunknown_ bind.info in
        let body = insertFreeVariablesH solutions subMap body in
        {bind with tyBody = tyBody, tyAnnot = tyAnnot, body = body}
      else errorSingle [bind.info] (join ["Lambda lifting error: No solution found for binding ",
                                          nameGetStr bind.ident])
    in
    let subMap = foldl addBindingSubExpression subMap t.bindings in
    let bindings = map (insertFreeVarsBinding subMap) t.bindings in
    TmRecLets {t with bindings = bindings,
                      inexpr = insertFreeVariablesH solutions subMap t.inexpr}
  | t -> smap_Expr_Expr (insertFreeVariablesH solutions subMap) t

  sem insertFreeVariables (solutions : Map Name (Map Name Type)) =
  | t -> insertFreeVariablesH solutions (mapEmpty nameCmp) t
end

lang LambdaLiftLiftGlobal = MExprAst
  sem _bindLifted : [Expr] -> Expr -> Expr
  sem _bindLifted lifted =
  | t ->
    let binds = snoc lifted t in
    _bindLiftedH binds

  sem _bindLiftedH : [Expr] -> Expr
  sem _bindLiftedH =
  | [bind] ++ rest ->
    if null rest then bind else
    let rest = _bindLiftedH rest in
    switch bind
    case TmLet t then TmLet {t with inexpr = rest}
    case TmRecLets t then TmRecLets {t with inexpr = rest}
    case TmConDef t then TmConDef {t with inexpr = rest}
    case TmType t then TmType {t with inexpr = rest}
    case TmExt t then TmExt {t with inexpr = rest}
    case _ then rest
    end

  sem liftRecursiveBindingH (bindings : [RecLetBinding]) =
  | TmLet t ->
    match liftRecursiveBindingH bindings t.body with (bindings, body) in
    match t.body with TmLam _ then
      let bind : RecLetBinding =
        { ident = t.ident, tyAnnot = ityunknown_ t.info, tyBody = t.tyBody
        , body = body, info = t.info } in
      let bindings = snoc bindings bind in
      liftRecursiveBindingH bindings t.inexpr
    else match liftRecursiveBindingH bindings t.inexpr with (bindings, inexpr) in
      (bindings, TmLet {{t with body = body} with inexpr = inexpr})
  | TmRecLets t ->
    let liftBinding : [RecLetBinding] -> RecLetBinding -> [RecLetBinding] =
      lam bindings. lam bind.
      match liftRecursiveBindingH bindings bind.body with (bindings, body) in
      snoc bindings {bind with body = body}
    in
    let bindings = foldl liftBinding bindings t.bindings in
    liftRecursiveBindingH bindings t.inexpr
  | t -> smapAccumL_Expr_Expr liftRecursiveBindingH bindings t

  sem liftRecursiveBinding =
  | TmRecLets t /- : Expr -> Expr -/ ->
    let liftBinding : [RecLetBinding] -> RecLetBinding -> [RecLetBinding] =
      lam bindings. lam bind.
      match liftRecursiveBindingH bindings bind.body with (bindings, body) in
      snoc bindings {bind with body = body}
    in
    let bindings = foldl liftBinding [] t.bindings in
    TmRecLets {{t with bindings = bindings} with inexpr = unit_}

  sem liftGlobalH (lifted : [Expr]) =
  | TmLet t ->
    match liftGlobalH lifted t.body with (lifted, body) in
    match t.body with TmLam _ then
      let lifted = snoc lifted (TmLet {{t with body = body}
                                          with inexpr = unit_}) in
      liftGlobalH lifted t.inexpr
    else match liftGlobalH lifted t.inexpr with (lifted, inexpr) in
      (lifted, TmLet {{t with body = body} with inexpr = inexpr})
  | TmRecLets t ->
    let lifted = snoc lifted (liftRecursiveBinding (TmRecLets t)) in
    liftGlobalH lifted t.inexpr
  | TmType t ->
    -- TODO(larshum, 2022-10-20): Lifting type and constructor definitions to
    -- the top of the program may make an ill-typed program pass the
    -- type-checking because types are placed on the top-level of the program.
    -- In the general case, we want something more sophisticated to decide on
    -- this here.
    let lifted = snoc lifted (TmType {t with inexpr = unit_}) in
    liftGlobalH lifted t.inexpr
  | TmConDef t ->
    let lifted = snoc lifted (TmConDef {t with inexpr = unit_}) in
    liftGlobalH lifted t.inexpr
  | TmExt t ->
    let lifted = snoc lifted (TmExt {t with inexpr = unit_}) in
    liftGlobalH lifted t.inexpr
  | t -> smapAccumL_Expr_Expr liftGlobalH lifted t

  sem liftGlobal =
  | TmLet t ->
    match liftGlobalH [] t.body with (lifted, body) in
    _bindLifted
      lifted
      (TmLet {{t with body = body} with inexpr = liftGlobal t.inexpr})
  | TmRecLets t ->
    let lifted = [liftRecursiveBinding (TmRecLets t)] in
    _bindLifted lifted (liftGlobal t.inexpr)
  | TmType t -> TmType {t with inexpr = liftGlobal t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = liftGlobal t.inexpr}
  | TmUtest t ->
    let optionLiftGlobalH = lam lifted. lam t.
      match t with Some t then
        match liftGlobalH lifted t with (lifted, t) in (lifted, Some t)
      else (lifted, t)
    in
    match liftGlobalH [] t.test with (lifted, test) in
    match liftGlobalH lifted t.expected with (lifted, expected) in
    match optionLiftGlobalH lifted t.tusing with (lifted, tusing) in
    match optionLiftGlobalH lifted t.tonfail with (lifted, tonfail) in
    _bindLifted
      lifted
      (TmUtest {t with
                test = test,
                expected = expected,
                tusing = tusing,
                tonfail = tonfail,
                next = liftGlobal t.next})
  | TmExt t -> TmExt {t with inexpr = liftGlobal t.inexpr}
  | t ->
    match liftGlobalH [] t with (lifted, t) in
    _bindLifted lifted t
end

lang LambdaLiftReplaceCapturedParameters = MExprAst + MExprSubstitute
  sem replaceCapturedParameters : Map Name (Map Name Type) -> Expr
                               -> (Map Name (Map Name Type), Expr)
  sem replaceCapturedParameters solutions =
  | ast ->
    let subs : Map Name [(Name, Name, Type)] =
      mapMapWithKey
        (lam. lam sol.
          map
            (lam idTy.
              match idTy with (oldId, ty) in
              (oldId, nameSetNewSym oldId, ty))
            (mapBindings sol))
        solutions in

    -- Construct a substitution map from the old ID to the updated ID.
    let nameSub = lam sub.
      match sub with (oldId, newId, _) in
      (oldId, newId) in
    let subMap : Map Name (Map Name Name) =
      mapMapWithKey
        (lam. lam subs. mapFromSeq nameCmp (map nameSub subs))
        subs in

    -- Reconstruct the solutions map using the new ID.
    let newIdSub = lam sub.
      match sub with (_, newId, ty) in
      (newId, ty) in
    let solutions : Map Name (Map Name Type) =
      mapMapWithKey
        (lam. lam subs. mapFromSeq nameCmp (map newIdSub subs))
        subs in

    (solutions, replaceCapturedParametersH subMap ast)

  sem replaceCapturedParametersH : Map Name (Map Name Name) -> Expr -> Expr
  sem replaceCapturedParametersH subMap =
  | TmLet t ->
    let body =
      match mapLookup t.ident subMap with Some subs then
        substituteIdentifiers subs t.body
      else t.body
    in
    TmLet {t with body = body,
                  inexpr = replaceCapturedParametersH subMap t.inexpr}
  | TmRecLets t ->
    let replaceCapturedParametersBinding = lam bind.
      match mapLookup bind.ident subMap with Some subs then
        {bind with body = substituteIdentifiers subs bind.body}
      else bind
    in
    let bindings = map replaceCapturedParametersBinding t.bindings in
    TmRecLets {t with bindings = bindings,
                      inexpr = replaceCapturedParametersH subMap t.inexpr}
  | t -> smap_Expr_Expr (replaceCapturedParametersH subMap) t
end

lang LambdaLiftTyAlls = MExprAst
  type TyAllData = (VarSort, Info)

  sem liftTyAlls : Expr -> (Map Name TyAllData, Expr)
  sem liftTyAlls =
  | t -> liftTyAllsExpr (mapEmpty nameCmp) t

  sem liftTyAllsExpr : Map Name TyAllData -> Expr -> (Map Name TyAllData, Expr)
  sem liftTyAllsExpr tyAlls =
  | TmLet t ->
    match liftTyAllsExpr tyAlls t.body with (tyAlls, body) in
    match liftTyAllsType tyAlls t.tyBody with (tyAlls, tyBody) in
    match liftTyAllsExpr tyAlls t.inexpr with (tyAlls, inexpr) in
    (tyAlls, TmLet {t with body = body, tyBody = tyBody, inexpr = inexpr})
  | TmRecLets t ->
    let liftBinding = lam tyAlls. lam binding.
      match liftTyAllsExpr tyAlls binding.body with (tyAlls, body) in
      match liftTyAllsType tyAlls binding.tyBody with (tyAlls, tyBody) in
      (tyAlls, {binding with body = body, tyBody = tyBody})
    in
    match mapAccumL liftBinding tyAlls t.bindings with (tyAlls, bindings) in
    match liftTyAllsExpr tyAlls t.inexpr with (tyAlls, inexpr) in
    (tyAlls, TmRecLets {t with bindings = bindings, inexpr = inexpr})
  | t -> smapAccumL_Expr_Expr liftTyAllsExpr tyAlls t

  sem liftTyAllsType : Map Name TyAllData -> Type -> (Map Name TyAllData, Type)
  sem liftTyAllsType tyAlls =
  | TyAll t ->
    let tyAlls = mapInsert t.ident (t.sort, t.info) tyAlls in
    liftTyAllsType tyAlls t.ty
  | ty -> smapAccumL_Type_Type liftTyAllsType tyAlls ty

  sem insertTyAlls : Map Name TyAllData -> Expr -> Expr
  sem insertTyAlls tyAlls =
  | TmLet t ->
    match insertTyAllsType tyAlls t.tyAnnot with (tyAnnot, bound) in
    let body = eraseUnboundTypesExpr bound t.body in
    let inexpr = insertTyAlls tyAlls t.inexpr in
    TmLet {t with tyAnnot = tyAnnot, body = body,
                  ty = tyTm inexpr, inexpr = inexpr}
  | TmRecLets t ->
    let bindingFn = lam bind.
      match insertTyAllsType tyAlls bind.tyAnnot with (tyAnnot, bound) in
      let body = eraseUnboundTypesExpr bound bind.body in
      {bind with tyAnnot = tyAnnot, body = body}
    in
    let inexpr = insertTyAlls tyAlls t.inexpr in
    TmRecLets {t with bindings = map bindingFn t.bindings,
                      ty = tyTm inexpr, inexpr = inexpr}
  | TmType t ->
    let inexpr = insertTyAlls tyAlls t.inexpr in
    TmType {t with ty = tyTm inexpr, inexpr = inexpr}
  | TmConDef t ->
    let inexpr = insertTyAlls tyAlls t.inexpr in
    TmConDef {t with ty = tyTm inexpr, inexpr = inexpr}
  | TmUtest t ->
    let next = insertTyAlls tyAlls t.next in
    TmUtest {t with ty = tyTm next, next = next}
  | TmExt t ->
    let inexpr = insertTyAlls tyAlls t.inexpr in
    TmExt {t with ty = tyTm inexpr, inexpr = inexpr}
  | t -> smap_Expr_Expr (insertTyAlls tyAlls) t

  -- Replaces TyVar that refer to unbound variables with TyUnknown.
  -- This prevents type variables from escaping their scope, which may happen
  -- due to the lambda lifting.
  sem eraseUnboundTypesExpr : Map Name TyAllData -> Expr -> Expr
  sem eraseUnboundTypesExpr bound =
  | t ->
    let t = smap_Expr_Expr (eraseUnboundTypesExpr bound) t in
    let t = smap_Expr_Type (eraseUnboundTypesType bound) t in
    let t = smap_Expr_Pat (eraseUnboundTypesPat bound) t in
    smap_Expr_TypeLabel (eraseUnboundTypesType bound) t

  sem eraseUnboundTypesType : Map Name TyAllData -> Type -> Type
  sem eraseUnboundTypesType bound =
  | TyVar t ->
    match mapLookup t.ident bound with Some (_, info) then
      TyVar {t with info = info}
    else TyUnknown {info = t.info}
  | ty -> smap_Type_Type (eraseUnboundTypesType bound) ty

  sem eraseUnboundTypesPat : Map Name TyAllData -> Pat -> Pat
  sem eraseUnboundTypesPat bound =
  | p ->
    let p = smap_Pat_Pat (eraseUnboundTypesPat bound) p in
    withTypePat (eraseUnboundTypesType bound (tyPat p)) p

  sem insertTyAllsType : Map Name TyAllData -> Type -> (Type, Map Name TyAllData)
  sem insertTyAllsType tyAlls =
  | ty ->
    let vars = collectTyVars tyAlls (mapEmpty nameCmp) ty in
    let ty = eraseUnboundTypesType vars ty in
    ( mapFoldWithKey
        (lam accTy. lam tyId. lam tyAllData.
          match tyAllData with (varSort, info) in
          TyAll {ident = tyId, sort = varSort, ty = accTy, info = info})
        ty vars
    , vars )

  sem collectTyVars : Map Name TyAllData -> Map Name TyAllData -> Type
                   -> Map Name TyAllData
  sem collectTyVars tyAlls acc =
  | TyVar t ->
    match mapLookup t.ident tyAlls with Some entry then
      mapInsert t.ident entry acc
    else acc
  | ty -> sfold_Type_Type (collectTyVars tyAlls) acc ty
end

lang MExprLambdaLift =
  LambdaLiftNameAnonymous + LambdaLiftFindFreeVariables +
  LambdaLiftInsertFreeVariables + LambdaLiftLiftGlobal +
  LambdaLiftReplaceCapturedParameters + LambdaLiftTyAlls

  sem liftLambdas =
  | t -> match liftLambdasWithSolutions t with (_, t) in t

  sem liftLambdasWithSolutions =
  | t ->
    match liftTyAlls t with (tyAllEnv, t) in
    let t = nameAnonymousLambdas t in
    let state : LambdaLiftState = findFreeVariables emptyLambdaLiftState t in
    let t = insertFreeVariables state.sols t in
    let t = liftGlobal t in
    match replaceCapturedParameters state.sols t with (solutions, t) in
    (solutions, insertTyAlls tyAllEnv t)
end

lang TestLang =
  MExprLambdaLift + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t. typeCheck (symbolize t) in

let noLambdas = bind_ (ulet_ "x" (int_ 2)) unit_ in
utest liftLambdas noLambdas with noLambdas using eqExpr in

let innerFunction = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x"
    (bind_
      (ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))))
      (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas innerFunction with expected using eqExpr in

let factorial = preprocess (ureclets_ [
  ("fact", ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 1)
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))]) in
utest liftLambdas factorial with factorial using eqExpr in

let factorialWithHelper = preprocess (bindall_ [
  ulet_ "fact" (ulam_ "n" (bindall_ [
    ureclets_ [
      ("work", ulam_ "acc" (ulam_ "n" (
        if_ (eqi_ (var_ "n") (int_ 0))
          (var_ "acc")
          (appf2_ (var_ "work")
            (muli_ (var_ "acc") (var_ "n"))
            (subi_ (var_ "n") (int_ 1))))))],
    appf2_ (var_ "work") (int_ 1) (var_ "n")])),
  app_ (var_ "fact") (int_ 4)]) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("work", ulam_ "acc" (ulam_ "n" (
      if_ (eqi_ (var_ "n") (int_ 0))
        (var_ "acc")
        (appf2_ (var_ "work")
          (muli_ (var_ "acc") (var_ "n"))
          (subi_ (var_ "n") (int_ 1))))))],
  ulet_ "fact" (ulam_ "n" (appf2_ (var_ "work") (int_ 1) (var_ "n"))),
  app_ (var_ "fact") (int_ 4)]) in
utest liftLambdas factorialWithHelper with expected using eqExpr in

let liftFreeVars = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    app_ (var_ "g") (int_ 2)])),
  app_ (var_ "f") (int_ 3)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 2))),
  app_ (var_ "f") (int_ 3)]) in
utest liftLambdas liftFreeVars with expected using eqExpr in

let deepNesting = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (
        addi_ (var_ "y") (var_ "z"))),
      app_ (var_ "h") (int_ 2)])),
    app_ (var_ "g") (var_ "x")])),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "g" (ulam_ "y" (appf2_ (var_ "h") (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas deepNesting with expected using eqExpr in

let multipleInnerLets = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (var_ "x"))),
    addi_ (app_ (var_ "g") (int_ 1)) (app_ (var_ "h") (int_ 2))])),
  app_ (var_ "f") (int_ 1)]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "z") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (
    addi_ (appf2_ (var_ "g") (var_ "x") (int_ 1))
          (appf2_ (var_ "h") (var_ "x") (int_ 2)))),
  app_ (var_ "f") (int_ 1)]) in
utest liftLambdas multipleInnerLets with expected using eqExpr in

let letInReclet = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ureclets_ [
      ("g", ulam_ "y" (bindall_ [
        ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (int_ 1))),
        addi_ (app_ (var_ "h") (var_ "y")) (var_ "x")
      ]))],
    app_ (var_ "g") (int_ 1)
  ])),
  app_ (var_ "f") (int_ 4)]) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("h", ulam_ "z" (addi_ (var_ "z") (int_ 1))),
    ("g", ulam_ "x" (ulam_ "y" (
      addi_ (app_ (var_ "h") (var_ "y")) (var_ "x"))))],
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 4)]) in
utest liftLambdas letInReclet with expected using eqExpr in

let deepNestedRecursiveDefs = preprocess (ureclets_ [
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (bindall_ [
      ureclets_ [("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1)))],
      ureclets_ [
        ("f4", ulam_ "y" (bindall_ [
          ulet_ "k" (ulam_ "x2" (app_ (var_ "f5") (var_ "x2"))),
          addi_ (app_ (var_ "k") (var_ "x")) (var_ "y")])),
        ("f5", ulam_ "x3" (app_ (var_ "f4") (subi_ (var_ "x3") (int_ 1))))
      ],
      addi_ (app_ (var_ "f3") (var_ "x"))
            (app_ (var_ "f4") (int_ 2))]),
    var_ "f2"]))]) in
let expected = preprocess (ureclets_ [
  ("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1))),
  ("k", ulam_ "x" (ulam_ "x2" (appf2_ (var_ "f5") (var_ "x") (var_ "x2")))),
  ("f4", ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "k") (var_ "x") (var_ "x")) (var_ "y")))),
  ("f5", ulam_ "x" (ulam_ "x3" (appf2_ (var_ "f4") (var_ "x") (subi_ (var_ "x3") (int_ 1))))),
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (addi_ (app_ (var_ "f3") (var_ "x"))
                      (appf2_ (var_ "f4") (var_ "x") (int_ 2))),
    var_ "f2"]))]) in
utest liftLambdas deepNestedRecursiveDefs with expected using eqExpr in

let fdef = ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let fapp = bind_ fdef (app_ (var_ "f") (int_ 1)) in

let liftUtest = preprocess (
  utest_
    (int_ 0)
    fapp
    unit_) in
let expected = preprocess (
  bind_
    fdef
    (utest_
      (int_ 0)
      (app_ (var_ "f") (int_ 1))
      unit_)) in
utest liftLambdas liftUtest with expected using eqExpr in

let liftApp = preprocess (bindall_ [
  app_
    (bind_
      (ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
      (app_ (var_ "g") (int_ 2)))
    fapp]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  fdef,
  app_
    (app_ (var_ "g") (int_ 2))
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftApp with expected using eqExpr in

let liftSeq = preprocess (seq_ [fapp]) in
let expected = preprocess (bindall_ [fdef, seq_ [app_ (var_ "f") (int_ 1)]]) in
utest liftLambdas liftSeq with expected using eqExpr in

let liftRecord = preprocess (urecord_ [("a", fapp), ("b", int_ 2)]) in
let expected = preprocess (bindall_ [
  fdef,
  urecord_ [
    ("a", app_ (var_ "f") (int_ 1)),
    ("b", int_ 2)]]) in
utest liftLambdas liftRecord with expected using eqExpr in

let liftRecordUpdate = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  recordupdate_ (var_ "r") "b" fapp
  ]) in
let expected = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  fdef,
  recordupdate_ (var_ "r") "b" (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftRecordUpdate with expected using eqExpr in

let liftMatchTarget = preprocess (
  match_ fapp (pint_ 0)
    (int_ 1)
    (int_ 2)) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (app_ (var_ "f") (int_ 1)) (pint_ 0)
    (int_ 1)
    (int_ 2)]) in
utest liftLambdas liftMatchTarget with expected using eqExpr in

let liftMatchThn = preprocess (
  match_ (int_ 3) (pint_ 3)
    fapp
    (int_ 0)) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (app_ (var_ "f") (int_ 1))
    (int_ 0)]) in
utest liftLambdas liftMatchThn with expected using eqExpr in

let liftMatchEls = preprocess (
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    fapp) in
let expected = preprocess (bindall_ [
  fdef,
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    (app_ (var_ "f") (int_ 1))]) in
utest liftLambdas liftMatchEls with expected using eqExpr in

let conAppLift = preprocess (bindall_ [
  type_ "Tree" [] (tyvariant_ []),
  condef_ "Leaf" (tyarrow_ tyint_ (tycon_ "Tree")),
  ulet_ "x" (conapp_ "Leaf" fapp),
  unit_
]) in
let expected = preprocess (bindall_ [
  type_ "Tree" [] (tyvariant_ []),
  condef_ "Leaf" (tyarrow_ tyint_ (tycon_ "Tree")),
  fdef,
  ulet_ "x" (conapp_ "Leaf" (app_ (var_ "f") (int_ 1))),
  unit_
]) in

-- NOTE(larshum, 2022-09-15): Compare using eqString as equality of TmType has
-- not been implemented.
utest expr2str (liftLambdas conAppLift) with expr2str expected using eqString in

let anonymousFunctionLift = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    app_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "t") (var_ "x") (int_ 4))),
  app_ (var_ "f") (int_ 2)]) in
utest liftLambdas anonymousFunctionLift with expected using eqExpr in

let anonymousMapLift = preprocess (
  map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (seq_ [int_ 0, int_ 7])) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  map_ (var_ "t") (seq_ [int_ 0, int_ 7])]) in
utest liftLambdas anonymousMapLift with expected using eqExpr in

let recursiveSystem = preprocess (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulam_ "x" (addi_ (app_ (var_ "g") (var_ "x")) (var_ "a"))),
    ("g", ulam_ "y" (addi_ (app_ (var_ "h") (var_ "y")) (var_ "b"))),
    ("h", ulam_ "z" (addi_ (app_ (var_ "f") (var_ "z")) (var_ "c")))],
  unit_]) in
let expected = preprocess (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulams_ ["a", "b", "c", "x"] (
      addi_ (appSeq_ (var_ "g") [var_ "a", var_ "b", var_ "c", var_ "x"])
            (var_ "a"))),
    ("g", ulams_ ["a", "b", "c", "y"] (
      addi_ (appSeq_ (var_ "h") [var_ "a", var_ "b", var_ "c", var_ "y"])
            (var_ "b"))),
    ("h", ulams_ ["a", "b", "c", "z"] (
      addi_ (appSeq_ (var_ "f") [var_ "a", var_ "b", var_ "c", var_ "z"])
            (var_ "c")))],
  unit_]) in
utest liftLambdas recursiveSystem with expected using eqExpr in

let boundInMatchPat = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (bind_
        (ulet_ "g" (ulam_ "z" (addi_ (var_ "y") (var_ "z"))))
        (app_ (var_ "g") (var_ "x")))
      (int_ 0)))]) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (appf2_ (var_ "g") (var_ "y") (var_ "x"))
      (int_ 0)))]) in
utest liftLambdas boundInMatchPat with expected using eqExpr in

let nestedFreeVar = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (addi_ (var_ "x") (var_ "z"))),
      app_ (var_ "h") (var_ "y")])),
    app_ (var_ "g") (var_ "x")]))]) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "x") (var_ "z")))),
  ulet_ "g" (ulam_ "x" (ulam_ "y" (appf2_ (var_ "h") (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (var_ "x")))]) in
utest liftLambdas nestedFreeVar with expected using eqExpr in

let letMultiParam = preprocess (bindall_ [
  ulet_ "a" (int_ 2),
  ulet_ "b" (int_ 6),
  ulet_ "f" (ulam_ "x" (
    addi_ (addi_ (var_ "a") (var_ "b")) (var_ "x"))),
  app_ (var_ "f") (int_ 7)]) in
let expected = preprocess (bindall_ [
  ulet_ "a" (int_ 2),
  ulet_ "b" (int_ 6),
  ulet_ "f" (ulam_ "a" (ulam_ "b" (ulam_ "x" (
    addi_ (addi_ (var_ "a") (var_ "b")) (var_ "x"))))),
  appf3_ (var_ "f") (var_ "a") (var_ "b") (int_ 7)]) in
utest liftLambdas letMultiParam with expected using eqExpr in

let nestedMap = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  map_
    (ulam_ "s" (map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (var_ "s")))
    (var_ "s")]) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  ulet_ "t1" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t2" (ulam_ "s" (map_ (var_ "t1") (var_ "s"))),
  map_ (var_ "t2") (var_ "s")]) in
utest liftLambdas nestedMap with expected using eqExpr in

let nestedAnonymousLambdas = preprocess (bindall_ [
  ulet_ "s" (seq_ [int_ 1, int_ 2, int_ 3]),
  ulet_ "x" (int_ 0),
  map_
    (ulam_ "y" (bindall_ [
      ulet_ "s" (map_ (ulam_ "x" (addi_ (var_ "x") (var_ "y"))) (var_ "s")),
      ulet_ "s" (map_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (var_ "s")),
      ulet_ "s" (map_ (ulam_ "z" (addi_ (var_ "z") (int_ 1))) (var_ "s")),
      var_ "s"]))
    (var_ "s")]) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [int_ 1, int_ 2, int_ 3]),
  ulet_ "x" (int_ 0),
  ulet_ "t1" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t2" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t3" (ulam_ "z" (addi_ (var_ "z") (int_ 1))),
  ulet_ "t4" (ulam_ "s" (ulam_ "x" (ulam_ "y" (bindall_ [
    ulet_ "s" (map_ (app_ (var_ "t1") (var_ "y")) (var_ "s")),
    ulet_ "s" (map_ (app_ (var_ "t2") (var_ "x")) (var_ "s")),
    ulet_ "s" (map_ (var_ "t3") (var_ "s")),
    var_ "s"])))),
  map_ (appf2_ (var_ "t4") (var_ "s") (var_ "x")) (var_ "s")]) in
utest liftLambdas nestedAnonymousLambdas with expected using eqExpr in

let nestedMultiArgLambda = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  map_
    (ulam_ "y"
      (foldl_ (ulam_ "acc" (ulam_ "e" (addi_ (var_ "acc") (var_ "e"))))
              (int_ 0) (var_ "y")))
    (var_ "s")]) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  ulet_ "t1" (ulam_ "acc" (ulam_ "e" (addi_ (var_ "acc") (var_ "e")))),
  ulet_ "t2" (ulam_ "y" (foldl_ (var_ "t1") (int_ 0) (var_ "y"))),
  map_ (var_ "t2") (var_ "s")]) in
utest liftLambdas nestedMultiArgLambda with expected using eqExpr in

let nestedReclets = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (ulam_ "mylist" (
    if_ (eqi_ (var_ "x") (int_ 10))
        unit_
        (bindall_ [
          ureclet_ "inner_foo" (ulam_ "z" (
            if_ (eqi_ (var_ "y") (var_ "z"))
                (appf1_ (var_ "inner_foo") (addi_ (var_ "z") (int_ 1)))
                (bindall_ [
                  ureclet_ "deep_foo" (ulam_ "i" (bindall_ [
                    if_ (eqi_ (var_ "i") (var_ "z"))
                        (unit_)
                        (bindall_ [
                          ulet_ "" (get_ (var_ "mylist") (var_ "i")),
                          appf1_ (var_ "deep_foo")
                                 (addi_ (var_ "i")
                                        (int_ 1))
                        ])
                  ])),
                  appf1_ (var_ "deep_foo") (int_ 0)
                ])
          )),
          appf1_ (var_ "inner_foo") (int_ 10)
        ])
  )))),
  appf3_ (var_ "foo") (int_ 11) (int_ 12) (seq_ [int_ 1, int_ 2, int_ 3])
  ]) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("deep_foo", (ulam_ "mylist" (ulam_ "z" (ulam_ "i" (
      if_ (eqi_ (var_ "i") (var_ "z"))
          unit_
          (bindall_ [
            ulet_ "" (get_ (var_ "mylist") (var_ "i")),
            appf3_ (var_ "deep_foo")
                   (var_ "mylist")
                   (var_ "z")
                   (addi_ (var_ "i")
                          (int_ 1))
          ])
    ))))),
    ("inner_foo", (ulam_ "y" (ulam_ "mylist" (ulam_ "z" (
              if_ (eqi_ (var_ "y") (var_ "z"))
                  (appf3_ (var_ "inner_foo")
                          (var_ "y")
                          (var_ "mylist")
                          (addi_ (var_ "z") (int_ 1)))
                  (appf3_ (var_ "deep_foo")
                           (var_ "mylist")
                           (var_ "z")
                           (int_ 0))
    )))))
  ],
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (ulam_ "mylist" (
    if_ (eqi_ (var_ "x") (int_ 10))
        (unit_)
        (appf3_ (var_ "inner_foo") (var_ "y") (var_ "mylist") (int_ 10))
  )))),
  appf3_ (var_ "foo") (int_ 11) (int_ 12) (seq_ [int_ 1, int_ 2, int_ 3])
  ]) in
utest liftLambdas nestedReclets with expected using eqExpr in


let types = preprocess
  (ulet_ "f" (ulam_ "s"
    (bind_
      (ulet_ "g" (ulam_ "x" (snoc_ (var_ "s") (var_ "x"))))
      (foldl_ (uconst_ (CConcat ())) (seq_ []) (map_ (var_ "g") (var_ "s")))))) in
let expected = preprocess
  (bindall_ [
    ulet_ "g" (ulam_ "s" (ulam_ "x" (snoc_ (var_ "s") (var_ "x")))),
    ulet_ "f" (ulam_ "s"
      (foldl_ (uconst_ (CConcat ())) (seq_ []) (map_ (app_ (var_ "g") (var_ "s")) (var_ "s"))))]) in

-- NOTE(larshum, 2022-09-15): Test that the expressions are equal and that the
-- let-bodies are given equivalent types.
utest liftLambdas types with expected using eqExpr in

let nestedUtest = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    utest_ (var_ "x") (int_ 0) (
    addi_ (var_ "x") (int_ 1))))
]) in
utest liftLambdas nestedUtest with nestedUtest using eqExpr in

()
