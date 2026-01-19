-- Defines lambda lifting of MExpr AST nodes in quadratic time in the size of
-- the program.

include "digraph.mc"
include "mexpr/ast.mc"
include "mlang/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/call-graph.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/utils.mc"

-- We store a 'solution' for each let-bound lambda: the set of free
-- variables it uses, all of which will need to become new parameters
type LambdaLiftSolution = use Ast in
  { vars : Map Name Type
  , tyVars : Map Name Kind
  }
type OrderedLamLiftSolution = use Ast in
  { vars : [(Name, Type)]
  , tyVars : [(Name, Kind)]
  }
type FinalOrderedLamLiftSolution = use Ast in
  { vars : [(Name, Type)]
  , varsToParams : Map Name Name
  , tyVars : [(Name, Kind)]
  , tyVarsToParams : Map Name Name
  }

let _orderSolution : LambdaLiftSolution -> OrderedLamLiftSolution = lam x.
  { vars = mapBindings x.vars
  , tyVars = mapBindings x.tyVars
  }

let _solUnion
  : LambdaLiftSolution -> LambdaLiftSolution -> LambdaLiftSolution
  = lam a. lam b.
    { vars = mapUnion a.vars b.vars
    , tyVars = mapUnion a.tyVars b.tyVars
    }
let _solEmpty : LambdaLiftSolution = { vars = mapEmpty nameCmp, tyVars = mapEmpty nameCmp }

-- A LambdaLiftState keeps track of:
-- * all bindings (normal variables and type variables)
-- * all let-bound lambdas together with their free variables
type LambdaLiftState = use Ast in {
  -- Variables are stored with the type they have at the binding site,
  -- not use site. The two typically differ if the original type is
  -- polymorphic.
  vars : Map Name Type,
  -- Type variables bound via annotations in let-bindings.
  tyVars : Map Name Kind,

  sols : Map Name LambdaLiftSolution
}

let emptyLambdaLiftState = {
  vars = mapEmpty nameCmp,
  tyVars = mapEmpty nameCmp,
  sols = mapEmpty nameCmp
}

-- Adds a name to all anonymous functions by wrapping them in a let-expression.
-- These are all lambda expressions that are not part of the right-hand side of
-- a let-expression or a recursive binding.
lang LambdaLiftNameAnonymous = MExprAst
  sem nameAnonymousLambdas : Expr -> Expr
  sem nameAnonymousLambdas = | tm -> nameAnonymousLambdasWork false tm

  sem nameAnonymousLambdasDecl : Decl -> Decl
  sem nameAnonymousLambdasDecl =
  | d -> smap_Decl_Expr (nameAnonymousLambdasWork false) d
  | DeclLet x ->
    let body = nameAnonymousLambdasWork true x.body in
    DeclLet {x with body = body}
  | DeclRecLets x ->
    let f = lam binding. {binding with body = nameAnonymousLambdasWork true binding.body} in
    let bindings = map f x.bindings in
    DeclRecLets {x with bindings = bindings}

  sem nameAnonymousLambdasWork : Bool -> Expr -> Expr
  sem nameAnonymousLambdasWork named =
  | tm -> smap_Expr_Expr (nameAnonymousLambdasWork false) tm
  | tm & TmOpaque _ -> tm
  | tm & TmLam t ->
    let tm = smap_Expr_Expr (nameAnonymousLambdasWork true) tm in
    if named then tm else
    let lamName = nameSym "anon" in
    let ty = tyTm tm in
    bind_ (nlet_ lamName ty tm) (withType ty (nvar_ lamName))
  | TmDecl x ->
    let decl = nameAnonymousLambdasDecl x.decl in
    let inexpr = nameAnonymousLambdasWork false x.inexpr in
    TmDecl {x with decl = decl, inexpr = inexpr}
end

lang LambdaLiftFindFreeVariablesPat = MExprAst
  sem getFreeVariablePatName ty (state : LambdaLiftState) =
  | PName id -> {state with vars = mapInsert id ty state.vars}
  | PWildcard _ -> state

  sem findFreeVariablesPat (state : LambdaLiftState) =
  | PatNamed t -> getFreeVariablePatName t.ty state t.ident
  | PatSeqEdge t ->
    let state = foldl findFreeVariablesPat state t.prefix in
    let state = getFreeVariablePatName t.ty state t.middle in
    foldl findFreeVariablesPat state t.postfix
  | p -> sfold_Pat_Pat findFreeVariablesPat state p
end

let _mapFoldReverseWithKey
  : all k. all v. all a. (k -> v -> a -> a) -> a -> Map k v -> a
  = lam f. lam acc. lam m.
    mapFoldWithKey (lam next. lam k. lam v. lam a. next (f k v a)) identity m acc

lang UpdateDefinitionsAndUses = MExprAst
  sem mapUnderTyAlls : (Type -> Type) -> Type -> Type
  sem mapUnderTyAlls f =
  | TyAll t -> TyAll {t with ty = mapUnderTyAlls f t.ty}
  | ty -> f ty

  sem updateType : OrderedLamLiftSolution -> Type -> Type -> Type
  sem updateType sol inferredTy = | ty ->
    let info = infoTy ty in
    let addParam = lam pair. lam ty.
      TyArrow {from = pair.1, to = ty, info = info} in
    let addTyAll = lam ty. lam pair.
      TyAll {info = info, ident = pair.0, kind = pair.1, ty = ty} in
    switch (unwrapType ty, inferredTy, sol.tyVars)
    -- NOTE(vipa, 2023-10-12): Keep binding un-annotated unless we
    -- also need to quantify over new type variables
    case (TyUnknown _, _, []) then ty
    -- NOTE(vipa, 2023-10-12): Otherwise use the annotation primarily,
    -- but take the inferred type if there was no explicit annotation
    case (TyUnknown _, ty, ![]) | (ty & !TyUnknown _, _, _) then
      let ty = mapUnderTyAlls (lam ty. foldr addParam ty sol.vars) ty in
      foldl addTyAll ty sol.tyVars
    end

  sem updateLambdaBody : OrderedLamLiftSolution -> Expr -> Expr
  sem updateLambdaBody sol = | tm ->
    let info = infoTm tm in
    let addParam = lam pair. lam acc. TmLam
      { ident = pair.0
      , tyAnnot = match unwrapType pair.1 with TyAll _ then pair.1 else tyunknown_
      , tyParam = pair.1
      , body = acc
      , ty = TyArrow {from = pair.1, to = tyTm acc, info = info}
      , info = info
      } in
    foldr addParam tm sol.vars

  sem mkSolApplication : OrderedLamLiftSolution -> Type -> TmVarRec -> Expr
  sem mkSolApplication sol newFType = | x ->
    let removeOneArrow = lam ty. match ty with TyArrow x
      then x.to
      else error "Compiler error in lambda lifting" in
    let addApp = lam acc. lam pair. TmApp
      { lhs = acc
      , rhs = TmVar
        { ident = pair.0
        , ty = pair.1
        , info = x.info
        -- NOTE(vipa, 2023-10-09): We freeze the variable if it might
        -- be polymorphic, otherwise the type might be wrong. It would
        -- be correct (but verbose) to always freeze since `ty` always
        -- exactly matches the definition-site type of the binding.
        , frozen = match unwrapType pair.1 with TyAll _ | TyUnknown _ then true else false
        }
      , info = x.info
      -- , ty = removeOneArrow (tyTm acc)
      , ty = ityunknown_ x.info
      } in
    let tm = foldl addApp (TmVar {x with frozen = false}) sol.vars in
    if x.frozen then
      -- NOTE(vipa, 2023-10-09): Re-freeze the variable with an
      -- intermediate let-binding
      let n = nameSetNewSym x.ident in
      -- NOTE(vipa, 2023-10-09): The generated AST will technically
      -- not type-check, because of the value restriction: we can't
      -- have a polymorphic value defined as anything but a
      -- value. `tm` here is a series of applications, i.e., not a
      -- value. We know from the transformation that it will be a
      -- value, and we could eta-expand if we want to get it fully
      -- correct, but I'm leaving it like this for the moment.
      TmDecl
      { decl = DeclLet
        { ident = n
        , tyAnnot = x.ty
        , tyBody = x.ty
        , body = tm
        , info = x.info
        }
      , inexpr = TmVar {ident = n, frozen = true, info = x.info, ty = x.ty}
      , info = x.info
      , ty = x.ty
      }
    else tm
end

-- Finds the map of free variables of all functions, mapped to their
-- corresponding types. For recursive let-expressions, this requires solving a
-- system of set equations (as the free variables within bindings may affect
-- each other).
lang LambdaLiftFindFreeVariables =
  MExprAst + MExprCallGraph + LambdaLiftFindFreeVariablesPat

  sem findFreeVariablesInType : LambdaLiftState -> LambdaLiftSolution -> Type -> LambdaLiftSolution
  sem findFreeVariablesInType state sol =
  | TyVar x ->
    match mapLookup x.ident state.tyVars with Some kind
    then {sol with tyVars = mapInsert x.ident kind sol.tyVars}
    else sol
  | ty -> sfold_Type_Type (findFreeVariablesInType state) sol ty

  sem findFreeVariablesInBody : LambdaLiftState -> LambdaLiftSolution -> Expr -> LambdaLiftSolution
  sem findFreeVariablesInBody state sol =
  | TmVar t ->
    let sol = findFreeVariablesInType state sol t.ty in
    match mapLookup t.ident state.vars with Some ty then
      { sol with vars = mapInsert t.ident ty sol.vars }
    else match mapLookup t.ident state.sols with Some sol2 then
      _solUnion sol sol2
    else sol
  | t ->
    let sol = sfold_Expr_TypeLabel (findFreeVariablesInType state) sol t in
    sfold_Expr_Expr (findFreeVariablesInBody state) sol t

  sem findFreeVariables : LambdaLiftState -> Expr -> LambdaLiftState
  sem findFreeVariables state =
  | TmLam t ->
    let state = {state with vars = mapInsert t.ident t.tyParam state.vars} in
    findFreeVariables state t.body
  | TmDecl (x & {decl = DeclLet t}) ->
    let state =
      match t.body with TmLam _ then
        -- NOTE(vipa, 2023-10-09): A let-bound lambda, find a solution
        -- for it
        let sol = findFreeVariablesInBody state _solEmpty t.body in
        {state with sols = mapInsert t.ident sol state.sols}
      else
        -- NOTE(vipa, 2023-10-09): Just another variable
        {state with vars = mapInsert t.ident t.tyBody state.vars}
    in
    let state =
      let tyvars = concat (stripTyAll t.tyAnnot).0 (stripTyAll t.tyBody).0 in
      foldl (lam acc. lam pair. {acc with tyVars = mapInsert pair.0 pair.1 acc.tyVars}) state tyvars in
    let state = findFreeVariables state t.body in
    findFreeVariables state x.inexpr
  | tm & TmDecl (x & {decl = DeclRecLets t}) -> recursive
    let insertInitialSolution = lam state. lam binding.
      let sol = findFreeVariablesInBody state _solEmpty binding.body in
      {state with sols = mapInsert binding.ident sol state.sols} in
    recursive let propagateFunNames
      : LambdaLiftState -> [[Name]] -> LambdaLiftState
      = lam state. lam s.
        match s with [h] ++ t then
          let sol =
            foldl
              (lam acc. lam id.
                match mapLookup id state.sols with Some sol then
                  _solUnion acc sol
                else acc)
              _solEmpty h in
          let state =
            foldl
              (lam state : LambdaLiftState. lam id.
                {state with sols = mapInsert id sol state.sols})
              state h in
          propagateFunNames state t
        else state
    in
    let findFreeVariablesBinding
      : LambdaLiftState -> DeclLetRecord -> LambdaLiftState
      = lam state. lam bind.
        let tyvars = concat (stripTyAll bind.tyAnnot).0 (stripTyAll bind.tyBody).0 in
        let state = foldl (lam acc. lam pair. {acc with tyVars = mapInsert pair.0 pair.1 acc.tyVars}) state tyvars in
        findFreeVariables state bind.body
    in
    let state = foldl insertInitialSolution state t.bindings in
    let g : Digraph Name Int = constructCallGraph tm in
    let sccs = digraphTarjan g in
    let state = propagateFunNames state (reverse sccs) in
    let state = foldl findFreeVariablesBinding state t.bindings in
    findFreeVariables state x.inexpr
  | TmMatch t ->
    let state = findFreeVariables state t.target in
    let state = findFreeVariablesPat state t.pat in
    let state = findFreeVariables state t.thn in
    findFreeVariables state t.els
  | TmDecl (x & {decl = DeclExt t}) ->
    let state = {state with sols = mapInsert t.ident _solEmpty state.sols} in
    findFreeVariables state x.inexpr
  | t -> sfold_Expr_Expr findFreeVariables state t
end

lang LambdaLiftInsertFreeVariables = MExprAst + UpdateDefinitionsAndUses
  type TmVarRec =
    { ident : Name
    , ty: Type
    , info: Info
    , frozen: Bool
    }

  sem insertFreeVariablesH
    : Map Name LambdaLiftSolution
    -> Map Name (TmVarRec -> Expr)
    -> Expr
    -> Expr
  sem insertFreeVariablesH solutions subMap =
  | tm & TmVar t ->
    optionMapOr tm (lam f. f t) (mapLookup t.ident subMap)
  | TmOpaque x ->
    recursive let updateFree : Map Name (Name, Expr) -> Expr -> (Map Name (Name, Expr), Expr) = lam acc. lam tm.
      switch tm
      case TmOpaque x then
        match updateFree acc x.body with (acc, body) in
        (acc, TmOpaque {x with body = body})
      case TmVar x then
        match mapLookup x.ident acc with Some (n, _) then
          (acc, TmVar {x with ident = n})
        else match mapLookup x.ident subMap with Some f then
          let n = nameSetNewSym x.ident in
          let acc = mapInsert x.ident (n, f x) acc in
          (acc, TmVar {x with ident = n})
        else (acc, tm)
      case tm then
        smapAccumL_Expr_Expr updateFree acc tm
      end in
    match updateFree (mapEmpty nameCmp) x.body with (acc, body) in
    mapFoldWithKey (lam tm. lam. lam pair. bind_ (nulet_ pair.0 pair.1) tm) (TmOpaque {x with body = body}) acc
  | TmDecl (x & {decl = DeclLet (t & {body = TmLam _})}) ->
    match mapLookup t.ident solutions with Some sol then
      let sol = _orderSolution sol in
      let tyBody = updateType sol t.tyBody t.tyBody in
      let tyAnnot = updateType sol t.tyBody t.tyAnnot in
      let body = insertFreeVariablesH solutions subMap t.body in
      let body = updateLambdaBody sol body in
      let inexpr =
        let subMap = mapInsert t.ident (mkSolApplication sol tyBody) subMap in
        insertFreeVariablesH solutions subMap x.inexpr in
      TmDecl {x with decl = DeclLet {t with tyBody = tyBody, tyAnnot = tyAnnot, body = body}, inexpr = inexpr}
    else errorSingle [t.info] (join ["Found no free variable solution for ",
                                     nameGetStr t.ident])
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let updateBindingShallow = lam solutions. lam subMap. lam binding.
      match mapLookup binding.ident solutions with Some sol then
        let sol = _orderSolution sol in
        let tyBody = updateType sol binding.tyBody binding.tyBody in
        let tyAnnot = updateType sol binding.tyBody binding.tyAnnot in
        let body = updateLambdaBody sol binding.body in
        let subMap = mapInsert binding.ident (mkSolApplication sol tyBody) subMap in
        (subMap, {binding with tyBody = tyBody, tyAnnot = tyAnnot, body = body})
      else errorSingle [binding.info] (join ["Lambda lifting error: No solution found for binding ",
                                             nameGetStr binding.ident])
    in
    let updateBindingNonShallow = lam solutions. lam subMap. lam binding.
      {binding with body = insertFreeVariablesH solutions subMap binding.body} in
    match mapAccumL (updateBindingShallow solutions) subMap t.bindings with (subMap, bindings) in
    let bindings = map (updateBindingNonShallow solutions subMap) bindings in
    let inexpr = insertFreeVariablesH solutions subMap x.inexpr in
    TmDecl {x with decl = DeclRecLets {t with bindings = bindings}, inexpr = inexpr}
  | t -> smap_Expr_Expr (insertFreeVariablesH solutions subMap) t

  sem insertFreeVariables (solutions : Map Name LambdaLiftSolution) =
  | t -> insertFreeVariablesH solutions (mapEmpty nameCmp) t
end

lang LambdaLiftLiftGlobal = MExprAst
  -- Lift all bound lambdas to the top-level. Also lift Decls they may
  -- depend on (type, con, external). Note that this is run after
  -- lambda lifting, i.e., no bound lambdas can depend on bound
  -- non-lambda values.

  sem liftGlobal : Expr -> Expr
  sem liftGlobal =
  | TmDecl x ->
    match smapAccumL_Decl_Expr liftGlobalH [] x.decl with (lifted, decl) in
    let inexpr = liftGlobal x.inexpr in
    bindall_ lifted (TmDecl {x with decl = decl, inexpr = inexpr})
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let lifted = collectBindingsToRecLet t.info t.bindings in
    bindall_ lifted (liftGlobal x.inexpr)
  | t ->
    match liftGlobalH [] t with (lifted, t) in
    bindall_ lifted t

  sem getLetBindings : Decl -> Either [DeclLetRecord] Decl
  sem getLetBindings =
  | DeclLet x -> Left [x]
  | DeclRecLets x -> Left x.bindings
  | d -> Right d

  sem collectBindingsToRecLet : Info -> [DeclLetRecord] -> [Decl]
  sem collectBindingsToRecLet info = | bindings ->
    let f = lam acc. lam bind.
      match liftGlobalH acc bind.body with (acc, body) in
      (acc, {bind with body = body}) in
    match mapAccumL f [] bindings with (decls, bindings) in
    let decls = snoc decls (DeclRecLets {info = info, bindings = bindings}) in
    let decls = map getLetBindings decls in
    match eitherPartition decls with (bindings, decls) in
    snoc decls (DeclRecLets {bindings = join bindings, info = info})

  sem liftGlobalH : [Decl] -> Expr -> ([Decl], Expr)
  sem liftGlobalH lifted =
  | t -> smapAccumL_Expr_Expr liftGlobalH lifted t
  | t & TmOpaque _ -> (lifted, t)
  | TmDecl (x & {decl = DeclType _ | DeclConDef _ | DeclExt _}) ->
    liftGlobalH (snoc lifted x.decl) x.inexpr
  | TmDecl (x & {decl = DeclLet t}) ->
    match liftGlobalH lifted t.body with (lifted, body) in
    match t.body with TmLam _ then
      let lifted = snoc lifted (DeclLet {t with body = body}) in
      liftGlobalH lifted x.inexpr
    else match liftGlobalH lifted x.inexpr with (lifted, inexpr) in
    (lifted, TmDecl {x with decl = DeclLet {t with body = body}, inexpr = inexpr})
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let newLifted = collectBindingsToRecLet t.info t.bindings in
    liftGlobalH (concat lifted newLifted) x.inexpr
end

lang LambdaLiftReplaceCapturedParameters = MExprAst + MExprSubstitute
  sem replaceCapturedParameters : Map Name LambdaLiftSolution -> Expr
                               -> (Map Name FinalOrderedLamLiftSolution, Expr)
  sem replaceCapturedParameters solutions =
  | ast ->
    let newNamesForSolution
      : LambdaLiftSolution -> (Map Name Name, FinalOrderedLamLiftSolution)
      = lam sol.
        let varsToParams = mapMapWithKey (lam k. lam. nameSetNewSym k) sol.vars in
        let tyVarsToParams = mapMapWithKey (lam k. lam. nameSetNewSym k) sol.tyVars in
        let ordSol = _orderSolution sol in
        let substs = mapUnion varsToParams tyVarsToParams in
        ( substs
        , { vars = ordSol.vars
          , varsToParams = varsToParams
          , tyVars = ordSol.tyVars
          , tyVarsToParams = tyVarsToParams
          }
        ) in
    let merged = mapMap newNamesForSolution solutions in
    let subMap = mapMap (lam x. x.0) merged in
    let solutions = mapMap (lam x. x.1) merged in

    (solutions, replaceCapturedParametersH subMap ast)

  sem replaceCapturedParametersH : Map Name (Map Name Name) -> Expr -> Expr
  sem replaceCapturedParametersH subMap =
  | TmDecl (x & {decl = DeclLet t}) ->
    let t =
      match mapLookup t.ident subMap with Some subs then
        { t with body = substituteIdentifiers subs t.body
        , tyAnnot = substituteIdentifiersType subs t.tyAnnot
        , tyBody = substituteIdentifiersType subs t.tyBody
        }
      else t in
    TmDecl {x with decl = DeclLet t, inexpr = replaceCapturedParametersH subMap x.inexpr}
  | TmDecl (x & {decl = DeclRecLets t}) ->
    let replaceCapturedParametersBinding = lam bind.
      match mapLookup bind.ident subMap with Some subs then
        { bind with body = substituteIdentifiers subs bind.body
        , tyAnnot = substituteIdentifiersType subs bind.tyAnnot
        , tyBody = substituteIdentifiersType subs bind.tyBody
        }
      else bind
    in
    let bindings = map replaceCapturedParametersBinding t.bindings in
    TmDecl
    {x with decl = DeclRecLets {t with bindings = bindings}
    , inexpr = replaceCapturedParametersH subMap x.inexpr
    }
  | TmOpaque x ->
    -- NOTE(vipa, 2026-04-28): This will make sure we actually refer
    -- to the parameters standing in for captured variables, rather
    -- than the variables themselves, which notably should be a
    -- semantics preserving rename, which is allowed under TmOpaque
    TmOpaque {x with body = replaceCapturedParametersH subMap x.body}
  | t -> smap_Expr_Expr (replaceCapturedParametersH subMap) t
end

lang MExprLambdaLift =
  LambdaLiftNameAnonymous + LambdaLiftFindFreeVariables +
  LambdaLiftInsertFreeVariables + LambdaLiftLiftGlobal +
  LambdaLiftReplaceCapturedParameters

  sem liftLambdas : Expr -> Expr
  sem liftLambdas =
  | t -> match liftLambdasWithSolutions t with (_, t) in t

  sem liftLambdasWithSolutions : Expr -> (Map Name FinalOrderedLamLiftSolution, Expr)
  sem liftLambdasWithSolutions =
  | t ->
    let t = nameAnonymousLambdas t in
    let state = findFreeVariables emptyLambdaLiftState t in
    let t = insertFreeVariables state.sols t in
    let t = liftGlobal t in
    replaceCapturedParameters state.sols t
end

lang MExprLambdaLiftAllowSpineCapture =
  MExprLambdaLift

  syn AllowCapture =
  | AllowCapture
  | DisallowCapture

  sem findFreeVariablesSpine : ({ty : Type, body : Expr} -> AllowCapture) -> LambdaLiftState -> Expr -> LambdaLiftState
  sem findFreeVariablesSpine shouldAllowCapture state =
  | TmDecl (x & {decl = DeclLet t}) ->
    let state =
      match t.body with TmLam _ then
        -- NOTE(vipa, 2023-10-09): A let-bound lambda, find a solution
        -- for it
        let sol = findFreeVariablesInBody state _solEmpty t.body in
        {state with sols = mapInsert t.ident sol state.sols}
      else switch shouldAllowCapture {ty = t.tyBody, body = t.body}
        case AllowCapture _ then
          -- NOTE(vipa, 2025-01-14): Not adding a variable to the
          -- state means we don't add it as a parameter to functions
          -- that close over it, i.e., we allow their capture.
          state
        case DisallowCapture _ then
          -- NOTE(vipa, 2025-05-16): A normal variable that should not
          -- be implicitly captured, but rather passed as an explicit
          -- argument.
          {state with vars = mapInsert t.ident t.tyBody state.vars}
        end
    in
    let state =
      let tyvars = concat (stripTyAll t.tyAnnot).0 (stripTyAll t.tyBody).0 in
      foldl (lam acc. lam pair. {acc with tyVars = mapInsert pair.0 pair.1 acc.tyVars}) state tyvars in
    let state = findFreeVariables state t.body in
    findFreeVariablesSpine shouldAllowCapture state x.inexpr
  | tm & TmDecl (x & {decl = DeclRecLets t}) -> recursive
    let insertInitialSolution = lam state. lam binding.
      let sol = findFreeVariablesInBody state _solEmpty binding.body in
      {state with sols = mapInsert binding.ident sol state.sols} in
    recursive let propagateFunNames
      : LambdaLiftState -> [[Name]] -> LambdaLiftState
      = lam state. lam s.
        match s with [h] ++ t then
          let sol =
            foldl
              (lam acc. lam id.
                match mapLookup id state.sols with Some sol then
                  _solUnion acc sol
                else acc)
              _solEmpty h in
          let state =
            foldl
              (lam state : LambdaLiftState. lam id.
                {state with sols = mapInsert id sol state.sols})
              state h in
          propagateFunNames state t
        else state
    in
    let findFreeVariablesBinding
      : LambdaLiftState -> DeclLetRecord -> LambdaLiftState
      = lam state. lam bind.
        let tyvars = concat (stripTyAll bind.tyAnnot).0 (stripTyAll bind.tyBody).0 in
        let state = foldl (lam acc. lam pair. {acc with tyVars = mapInsert pair.0 pair.1 acc.tyVars}) state tyvars in
        findFreeVariables state bind.body
    in
    let state = foldl insertInitialSolution state t.bindings in
    let g : Digraph Name Int = constructCallGraph tm in
    let sccs = digraphTarjan g in
    let state = propagateFunNames state (reverse sccs) in
    let state = foldl findFreeVariablesBinding state t.bindings in
    findFreeVariablesSpine shouldAllowCapture state x.inexpr
  | TmDecl (x & {decl = DeclExt t}) ->
    let state = {state with sols = mapInsert t.ident _solEmpty state.sols} in
    findFreeVariablesSpine shouldAllowCapture state x.inexpr
  | TmDecl x ->
    let state = sfold_Decl_Expr findFreeVariables state x.decl in
    findFreeVariablesSpine shouldAllowCapture state x.inexpr
  | tm -> findFreeVariables state tm

  sem liftLambdasWithSolutionsMaybeAllowSpineCapture : ({ty : Type, body : Expr} -> AllowCapture) -> Expr -> (Map Name FinalOrderedLamLiftSolution, Expr)
  sem liftLambdasWithSolutionsMaybeAllowSpineCapture shouldAllowCapture = | t ->
    let t = nameAnonymousLambdas t in
    let state = findFreeVariablesSpine shouldAllowCapture emptyLambdaLiftState t in
    let t = insertFreeVariables state.sols t in
    let t = liftGlobal t in
    replaceCapturedParameters state.sols t

  sem liftLambdasWithSolutionsAllowSpineCapture : Expr -> (Map Name FinalOrderedLamLiftSolution, Expr)
  sem liftLambdasWithSolutionsAllowSpineCapture = | t ->
    liftLambdasWithSolutionsMaybeAllowSpineCapture (lam. AllowCapture ()) t
end

lang TestLang =
  MExprLambdaLift + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t. typeCheck (symbolize t) in

let noLambdas = bind_ (ulet_ "x" (int_ 2)) unit_ in
utest liftLambdas noLambdas with noLambdas using eqExpr in

let innerFunction = preprocess (bind_ (
  ulet_ "f" (ulam_ "x"
    (bind_
      (ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))))
      (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2)))))
  (app_ (var_ "f") (int_ 1))) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (addi_ (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (muli_ (app_ (var_ "g") (var_ "x")) (int_ 2)))]
  (app_ (var_ "f") (int_ 1))) in
utest liftLambdas innerFunction with expected using eqExpr in

let factorial = preprocess (bind_ (ureclets_ [
  ("fact", ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 1)
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))]) unit_) in
utest liftLambdas factorial with factorial using eqExpr in

let factorialWithHelper = preprocess (bindall_ [
  ulet_ "fact" (ulam_ "n" (bindall_ [
    ureclets_ [
      ("work", ulam_ "acc" (ulam_ "n" (
        if_ (eqi_ (var_ "n") (int_ 0))
          (var_ "acc")
          (appf2_ (var_ "work")
            (muli_ (var_ "acc") (var_ "n"))
            (subi_ (var_ "n") (int_ 1))))))]]
    (appf2_ (var_ "work") (int_ 1) (var_ "n"))))]
  (app_ (var_ "fact") (int_ 4))) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("work", ulam_ "acc" (ulam_ "n" (
      if_ (eqi_ (var_ "n") (int_ 0))
        (var_ "acc")
        (appf2_ (var_ "work")
          (muli_ (var_ "acc") (var_ "n"))
          (subi_ (var_ "n") (int_ 1))))))],
  ulet_ "fact" (ulam_ "n" (appf2_ (var_ "work") (int_ 1) (var_ "n")))]
  (app_ (var_ "fact") (int_ 4))) in
utest liftLambdas factorialWithHelper with expected using eqExpr in

let liftFreeVars = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))]
    (app_ (var_ "g") (int_ 2))))]
  (app_ (var_ "f") (int_ 3))) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 2)))]
  (app_ (var_ "f") (int_ 3))) in
utest liftLambdas liftFreeVars with expected using eqExpr in

let deepNesting = preprocess (bind_ (
  ulet_ "f" (ulam_ "x" (bind_ (
    ulet_ "g" (ulam_ "y" (bind_ (
      ulet_ "h" (ulam_ "z" (
        addi_ (var_ "y") (var_ "z"))))
      (app_ (var_ "h") (int_ 2)))))
    (app_ (var_ "g") (var_ "x")))))
  (app_ (var_ "f") (int_ 1))) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "g" (ulam_ "y" (appf2_ (var_ "h") (var_ "y") (int_ 2))),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x")))]
  (app_ (var_ "f") (int_ 1))) in
utest liftLambdas deepNesting with expected using eqExpr in

let multipleInnerLets = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (addi_ (var_ "x") (var_ "y"))),
    ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (var_ "x")))]
    (addi_ (app_ (var_ "g") (int_ 1)) (app_ (var_ "h") (int_ 2)))))]
  (app_ (var_ "f") (int_ 1))) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "z") (var_ "x")))),
  ulet_ "f" (ulam_ "x" (
    addi_ (appf2_ (var_ "g") (var_ "x") (int_ 1))
          (appf2_ (var_ "h") (var_ "x") (int_ 2))))]
  (app_ (var_ "f") (int_ 1))) in
utest liftLambdas multipleInnerLets with expected using eqExpr in

let letInReclet = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ureclets_ [
      ("g", ulam_ "y" (bindall_ [
        ulet_ "h" (ulam_ "z" (addi_ (var_ "z") (int_ 1)))]
        (addi_ (app_ (var_ "h") (var_ "y")) (var_ "x")
      )))]]
    (app_ (var_ "g") (int_ 1))
  ))]
  (app_ (var_ "f") (int_ 4))) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("h", ulam_ "z" (addi_ (var_ "z") (int_ 1))),
    ("g", ulam_ "x" (ulam_ "y" (
      addi_ (app_ (var_ "h") (var_ "y")) (var_ "x"))))],
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (int_ 1)))]
  (app_ (var_ "f") (int_ 4))) in
utest liftLambdas letInReclet with expected using eqExpr in

let deepNestedRecursiveDefs = preprocess (bind_ (ureclets_ [
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (bindall_ [
      ureclets_ [("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1)))],
      ureclets_ [
        ("f4", ulam_ "y" (bindall_ [
          ulet_ "k" (ulam_ "x2" (app_ (var_ "f5") (var_ "x2")))]
          (addi_ (app_ (var_ "k") (var_ "x")) (var_ "y")))),
        ("f5", ulam_ "x3" (app_ (var_ "f4") (subi_ (var_ "x3") (int_ 1))))
      ]]
      (addi_ (app_ (var_ "f3") (var_ "x"))
            (app_ (var_ "f4") (int_ 2))))]
    (var_ "f2")))]) unit_) in
let expected = preprocess (bind_ (ureclets_ [
  ("f3", ulam_ "x1" (addi_ (var_ "x1") (int_ 1))),
  ("k", ulam_ "x" (ulam_ "x2" (appf2_ (var_ "f5") (var_ "x") (var_ "x2")))),
  ("f4", ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "k") (var_ "x") (var_ "x")) (var_ "y")))),
  ("f5", ulam_ "x" (ulam_ "x3" (appf2_ (var_ "f4") (var_ "x") (subi_ (var_ "x3") (int_ 1))))),
  ("f1", ulam_ "x" (bindall_ [
    ulet_ "f2" (addi_ (app_ (var_ "f3") (var_ "x"))
                      (appf2_ (var_ "f4") (var_ "x") (int_ 2)))]
    (var_ "f2")))]) unit_) in
utest liftLambdas deepNestedRecursiveDefs with expected using eqExpr in

let fdef = ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))) in
let fapp = bind_ fdef (app_ (var_ "f") (int_ 1)) in

let liftUtest = preprocess (
  bind_ (utest_
    (int_ 0)
    fapp)
    unit_) in
let expected = preprocess (
  bind_
    fdef
    (bind_ (utest_
      (int_ 0)
      (app_ (var_ "f") (int_ 1)))
      unit_)) in
utest liftLambdas liftUtest with expected using eqExpr in

let liftApp = preprocess (
  app_
    (bind_
      (ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
      (app_ (var_ "g") (int_ 2)))
    fapp) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  fdef]
  (app_
    (app_ (var_ "g") (int_ 2))
    (app_ (var_ "f") (int_ 1)))) in
utest liftLambdas liftApp with expected using eqExpr in

let liftSeq = preprocess (seq_ [fapp]) in
let expected = preprocess (bind_ fdef (seq_ [app_ (var_ "f") (int_ 1)])) in
utest liftLambdas liftSeq with expected using eqExpr in

let liftRecord = preprocess (urecord_ [("a", fapp), ("b", int_ 2)]) in
let expected = preprocess (bindall_ [
  fdef]
  (urecord_ [
    ("a", app_ (var_ "f") (int_ 1)),
    ("b", int_ 2)])) in
utest liftLambdas liftRecord with expected using eqExpr in

let liftRecordUpdate = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)])]
  (recordupdate_ (var_ "r") "b" fapp
  )) in
let expected = preprocess (bindall_ [
  ulet_ "r" (urecord_ [("a", float_ 2.5), ("b", int_ 0)]),
  fdef]
  (recordupdate_ (var_ "r") "b" (app_ (var_ "f") (int_ 1)))) in
utest liftLambdas liftRecordUpdate with expected using eqExpr in

let liftMatchTarget = preprocess (
  match_ fapp (pint_ 0)
    (int_ 1)
    (int_ 2)) in
let expected = preprocess (bindall_ [
  fdef]
  (match_ (app_ (var_ "f") (int_ 1)) (pint_ 0)
    (int_ 1)
    (int_ 2))) in
utest liftLambdas liftMatchTarget with expected using eqExpr in

let liftMatchThn = preprocess (
  match_ (int_ 3) (pint_ 3)
    fapp
    (int_ 0)) in
let expected = preprocess (bindall_ [
  fdef]
  (match_ (int_ 3) (pint_ 3)
    (app_ (var_ "f") (int_ 1))
    (int_ 0))) in
utest liftLambdas liftMatchThn with expected using eqExpr in

let liftMatchEls = preprocess (
  match_ (int_ 3) (pint_ 3)
    (int_ 0)
    fapp) in
let expected = preprocess (bindall_ [
  fdef]
  (match_ (int_ 3) (pint_ 3)
    (int_ 0)
    (app_ (var_ "f") (int_ 1)))) in
utest liftLambdas liftMatchEls with expected using eqExpr in

let conAppLift = preprocess (bindall_ [
  type_ "Tree" [] (tyvariant_ []),
  condef_ "Leaf" (tyarrow_ tyint_ (tycon_ "Tree")),
  ulet_ "x" (conapp_ "Leaf" fapp)]
  unit_
) in
let expected = preprocess (bindall_ [
  type_ "Tree" [] (tyvariant_ []),
  condef_ "Leaf" (tyarrow_ tyint_ (tycon_ "Tree")),
  fdef,
  ulet_ "x" (conapp_ "Leaf" (app_ (var_ "f") (int_ 1)))]
  unit_
) in

-- NOTE(larshum, 2022-09-15): Compare using eqString as equality of TmType has
-- not been implemented.
utest expr2str (liftLambdas conAppLift) with expr2str expected using eqString in

let anonymousFunctionLift = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    app_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (int_ 4)))]
  (app_ (var_ "f") (int_ 2))) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "t") (var_ "x") (int_ 4)))]
  (app_ (var_ "f") (int_ 2))) in
utest liftLambdas anonymousFunctionLift with expected using eqExpr in

let anonymousMapLift = preprocess (
  map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (seq_ [int_ 0, int_ 7])) in
let expected = preprocess (bindall_ [
  ulet_ "t" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))]
  (map_ (var_ "t") (seq_ [int_ 0, int_ 7]))) in
utest liftLambdas anonymousMapLift with expected using eqExpr in

let recursiveSystem = preprocess (bindall_ [
  ulet_ "a" (int_ 1),
  ulet_ "b" (int_ 2),
  ulet_ "c" (int_ 5),
  ureclets_ [
    ("f", ulam_ "x" (addi_ (app_ (var_ "g") (var_ "x")) (var_ "a"))),
    ("g", ulam_ "y" (addi_ (app_ (var_ "h") (var_ "y")) (var_ "b"))),
    ("h", ulam_ "z" (addi_ (app_ (var_ "f") (var_ "z")) (var_ "c")))]]
  unit_) in
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
            (var_ "c")))]]
  unit_) in
utest liftLambdas recursiveSystem with expected using eqExpr in

let boundInMatchPat = preprocess (bind_ (
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (bind_
        (ulet_ "g" (ulam_ "z" (addi_ (var_ "y") (var_ "z"))))
        (app_ (var_ "g") (var_ "x")))
      (int_ 0)))) unit_) in
let expected = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "z" (addi_ (var_ "y") (var_ "z")))),
  ulet_ "f" (ulam_ "x" (
    match_ (var_ "x") (pvar_ "y")
      (appf2_ (var_ "g") (var_ "y") (var_ "x"))
      (int_ 0)))] unit_) in
utest liftLambdas boundInMatchPat with expected using eqExpr in

let nestedFreeVar = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (bindall_ [
    ulet_ "g" (ulam_ "y" (bindall_ [
      ulet_ "h" (ulam_ "z" (addi_ (var_ "x") (var_ "z")))]
      (app_ (var_ "h") (var_ "y"))))]
    (app_ (var_ "g") (var_ "x"))))]
  unit_) in
let expected = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (ulam_ "z" (addi_ (var_ "x") (var_ "z")))),
  ulet_ "g" (ulam_ "x" (ulam_ "y" (appf2_ (var_ "h") (var_ "x") (var_ "y")))),
  ulet_ "f" (ulam_ "x" (appf2_ (var_ "g") (var_ "x") (var_ "x")))]
  unit_) in
utest liftLambdas nestedFreeVar with expected using eqExpr in

let letMultiParam = preprocess (bindall_ [
  ulet_ "a" (int_ 2),
  ulet_ "b" (int_ 6),
  ulet_ "f" (ulam_ "x" (
    addi_ (addi_ (var_ "a") (var_ "b")) (var_ "x")))]
  (app_ (var_ "f") (int_ 7))) in
let expected = preprocess (bindall_ [
  ulet_ "a" (int_ 2),
  ulet_ "b" (int_ 6),
  ulet_ "f" (ulam_ "a" (ulam_ "b" (ulam_ "x" (
    addi_ (addi_ (var_ "a") (var_ "b")) (var_ "x")))))]
  (appf3_ (var_ "f") (var_ "a") (var_ "b") (int_ 7))) in
utest liftLambdas letMultiParam with expected using eqExpr in

let nestedMap = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]])]
  (map_
    (ulam_ "s" (map_ (ulam_ "x" (addi_ (var_ "x") (int_ 1))) (var_ "s")))
    (var_ "s"))) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  ulet_ "t1" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t2" (ulam_ "s" (map_ (var_ "t1") (var_ "s")))]
  (map_ (var_ "t2") (var_ "s"))) in
utest liftLambdas nestedMap with expected using eqExpr in

let nestedAnonymousLambdas = preprocess (bindall_ [
  ulet_ "s" (seq_ [int_ 1, int_ 2, int_ 3]),
  ulet_ "x" (int_ 0)]
  (map_
    (ulam_ "y" (bindall_ [
      ulet_ "s" (map_ (ulam_ "x" (addi_ (var_ "x") (var_ "y"))) (var_ "s")),
      ulet_ "s" (map_ (ulam_ "y" (addi_ (var_ "x") (var_ "y"))) (var_ "s")),
      ulet_ "s" (map_ (ulam_ "z" (addi_ (var_ "z") (int_ 1))) (var_ "s"))]
      (var_ "s")))
    (var_ "s"))) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [int_ 1, int_ 2, int_ 3]),
  ulet_ "x" (int_ 0),
  ulet_ "t1" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t2" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t3" (ulam_ "z" (addi_ (var_ "z") (int_ 1))),
  ulet_ "t4" (ulam_ "s" (ulam_ "x" (ulam_ "y" (bindall_ [
    ulet_ "s" (map_ (app_ (var_ "t1") (var_ "y")) (var_ "s")),
    ulet_ "s" (map_ (app_ (var_ "t2") (var_ "x")) (var_ "s")),
    ulet_ "s" (map_ (var_ "t3") (var_ "s"))]
    (var_ "s")))))]
  (map_ (appf2_ (var_ "t4") (var_ "s") (var_ "x")) (var_ "s"))) in
utest liftLambdas nestedAnonymousLambdas with expected using eqExpr in

let nestedMultiArgLambda = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]])]
  (map_
    (ulam_ "y"
      (foldl_ (ulam_ "acc" (ulam_ "e" (addi_ (var_ "acc") (var_ "e"))))
              (int_ 0) (var_ "y")))
    (var_ "s"))) in
let expected = preprocess (bindall_ [
  ulet_ "s" (seq_ [seq_ [int_ 1, int_ 2, int_ 3]]),
  ulet_ "t1" (ulam_ "acc" (ulam_ "e" (addi_ (var_ "acc") (var_ "e")))),
  ulet_ "t2" (ulam_ "y" (foldl_ (var_ "t1") (int_ 0) (var_ "y")))]
  (map_ (var_ "t2") (var_ "s"))) in
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
                  ureclet_ "deep_foo" (ulam_ "i" (
                    if_ (eqi_ (var_ "i") (var_ "z"))
                        (unit_)
                        (bindall_ [
                          ulet_ "" (get_ (var_ "mylist") (var_ "i"))]
                          (appf1_ (var_ "deep_foo")
                                 (addi_ (var_ "i")
                                        (int_ 1))
                        ))
                  ))]
                  (appf1_ (var_ "deep_foo") (int_ 0)
                ))
          ))]
          (appf1_ (var_ "inner_foo") (int_ 10)
        ))
  ))))]
  (appf3_ (var_ "foo") (int_ 11) (int_ 12) (seq_ [int_ 1, int_ 2, int_ 3])
  )) in
let expected = preprocess (bindall_ [
  ureclets_ [
    ("deep_foo", (ulam_ "mylist" (ulam_ "z" (ulam_ "i" (
      if_ (eqi_ (var_ "i") (var_ "z"))
          unit_
          (bindall_ [
            ulet_ "" (get_ (var_ "mylist") (var_ "i"))]
            (appf3_ (var_ "deep_foo")
                   (var_ "mylist")
                   (var_ "z")
                   (addi_ (var_ "i")
                          (int_ 1))
          ))
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
  ))))]
  (appf3_ (var_ "foo") (int_ 11) (int_ 12) (seq_ [int_ 1, int_ 2, int_ 3])
  )) in
utest liftLambdas nestedReclets with expected using eqExpr in


let types = preprocess
  (bind_ (ulet_ "f" (ulam_ "s"
    (bind_
      (ulet_ "g" (ulam_ "x" (snoc_ (var_ "s") (var_ "x"))))
      (foldl_ (uconst_ (CConcat ())) (seq_ []) (map_ (var_ "g") (var_ "s")))))) unit_) in
let expected = preprocess
  (bindall_ [
    ulet_ "g" (ulam_ "s" (ulam_ "x" (snoc_ (var_ "s") (var_ "x")))),
    ulet_ "f" (ulam_ "s"
      (foldl_ (uconst_ (CConcat ())) (seq_ []) (map_ (app_ (var_ "g") (var_ "s")) (var_ "s"))))]
   unit_) in

-- NOTE(larshum, 2022-09-15): Test that the expressions are equal and that the
-- let-bodies are given equivalent types.
utest liftLambdas types with expected using eqExpr in

let nestedUtest = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (
    bind_ (utest_ (var_ "x") (int_ 0))
    (addi_ (var_ "x") (int_ 1))))
] unit_) in
utest liftLambdas nestedUtest with nestedUtest using eqExpr in


let lhs = preprocess
  (bindall_
    [ ulet_ "x" (int_ 1)
    , ulet_ "foo" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))
    ]
    (TmOpaque {info = NoInfo (), ty = tyunknown_, body = app_ (var_ "foo") (int_ 2)})) in
let rhs = preprocess
  (bindall_
    [ ulet_ "x" (int_ 1)
    , ulet_ "foo" (ulam_ "x1" (ulam_ "y" (addi_ (var_ "x1") (var_ "y"))))
    , ulet_ "foo1" (app_ (var_ "foo") (var_ "x"))
    ]
    (TmOpaque {info = NoInfo (), ty = tyunknown_, body = app_ (var_ "foo1") (int_ 2)})) in
utest liftLambdas lhs with rhs using eqExpr in

let lhs = preprocess
  (bindall_
    [ ulet_ "x" (int_ 1)
    , ulet_ "foo" (ulam_ "y" (TmOpaque {body = addi_ (var_ "x") (var_ "y"), ty = tyunknown_, info = NoInfo ()}))
    ]
    (app_ (var_ "foo") (int_ 2))) in
let rhs = preprocess
  (bindall_
    [ ulet_ "x" (int_ 1)
    , ulet_ "foo" (ulam_ "x1" (ulam_ "y" (TmOpaque {body = addi_ (var_ "x1") (var_ "y"), ty = tyunknown_, info = NoInfo ()})))
    ]
    (appf2_ (var_ "foo") (var_ "x") (int_ 2))) in
utest liftLambdas lhs with rhs using eqExpr in


()
