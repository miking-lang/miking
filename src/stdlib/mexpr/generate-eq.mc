-- Generate code required to compare two arbitrary (monomorphic,
-- non-function) values based on their structure

include "ast.mc"
include "type-check.mc"

include "mlang/loader.mc"
include "name.mc"
include "map.mc"
include "mexpr/ast-builder.mc"
include "stringid.mc"
include "seq.mc"
include "mexpr/unify.mc"
include "basic-types.mc"
include "error.mc"
include "set.mc"

lang GenerateEq = Ast
  type GEqEnv =
    { conFunctions : Map Name Name  -- For TyCons
    , varFunctions : Map Name Name  -- For TyVars
    , newFunctions : [(Name, Type, Expr)]  -- To be defined

    , tcEnv : TCEnv -- Current typechecking environment

    , eqSeq : Name
    , eqBool : Name
    }

  sem getEqFunction : GEqEnv -> Type -> (GEqEnv, Expr)
  sem getEqFunction env = | ty -> _getEqFunction env (unwrapType ty)

  sem _getEqFunction : GEqEnv -> Type -> (GEqEnv, Expr)
end

lang GenerateEqInt = GenerateEq + IntTypeAst + CmpIntAst
  sem _getEqFunction env +=
  | TyInt _ -> (env, uconst_ (CEqi ()))
end

lang GenerateEqFloat = GenerateEq + FloatTypeAst + CmpFloatAst
  sem _getEqFunction env +=
  | TyFloat _ -> (env, uconst_ (CEqf ()))
end

lang GenerateEqBool = GenerateEq + BoolTypeAst
  sem _getEqFunction env +=
  | TyBool _ -> (env, nvar_ env.eqBool)
end

lang GenerateEqSeq = GenerateEq + SeqTypeAst
  sem _getEqFunction env +=
  | TySeq x ->
    match getEqFunction env x.ty with (env, elemF) in
    (env, app_ (nvar_ env.eqSeq) elemF)
end

lang GenerateEqChar = GenerateEq + CharTypeAst + CmpCharAst
  sem _getEqFunction env +=
  | TyChar _ ->
    (env, uconst_ (CEqc ()))
end

lang GenerateEqRecord = GenerateEq + RecordTypeAst
  sem _getEqFunction env +=
  | ty & TyRecord x ->
    if mapIsEmpty x.fields then (env, ulam_ "" (ulam_ "" true_)) else

    let lName = nameSym "l" in
    let l = withType ty (nvar_ lName) in
    let rName = nameSym "r" in
    let r = withType ty (nvar_ rName) in

    let genRecElem = lam acc. lam label. lam ty. snoc acc (lam env.
      match getEqFunction env ty with (env, eqF) in
      let label = sidToString label in
      (env, appf2_ eqF (recordproj_ label l) (recordproj_ label r))) in
    let elems = mapFoldWithKey genRecElem [] x.fields in
    match mapAccumL (lam env. lam f. f env) env elems with (env, [first] ++ elems) in

    let f = lam acc. lam elem. if_ elem acc false_ in
    (env, nlam_ lName ty (nlam_ rName ty (foldl f first elems)))
end

lang GenerateEqApp = GenerateEq + AppTypeAst
  sem _getEqFunction env +=
  | TyApp x ->
    match getEqFunction env x.lhs with (env, lhs) in
    match getEqFunction env x.rhs with (env, rhs) in
    (env, app_ lhs rhs)
end

lang GenerateEqCon = GenerateEq + ConTypeAst + Generalize + UnifyPure
  sem _getEqFunction env +=
  | ty & TyCon x ->
    -- TODO(vipa, 2025-01-27): Invalidate old eq functions if
    -- we've introduced constructors to pre-existing types
    match mapLookup x.ident env.conFunctions with Some n then (env, nvar_ n) else

    let fname = nameSym (concat "eq" (nameGetStr x.ident)) in
    let env = {env with conFunctions = mapInsert x.ident fname env.conFunctions} in

    -- TODO(vipa, 2025-01-27): We cannot see locally defined types
    -- here, which might be an issue
    let params = match mapLookup x.ident env.tcEnv.tyConEnv with Some (_, params, _)
      then params
      else errorSingle [x.info] (concat "Typecheck environment does not contain information about type " (nameGetStr x.ident)) in
    let paramFNames = map (lam n. {f = nameSetNewSym n, tyvar = nameSetNewSym n}) params in
    let fullType = tyapps_ ty (map (lam x. ntyvar_ x.tyvar) paramFNames) in
    let prevVarFunctions = env.varFunctions in
    let env = {env with varFunctions = foldl (lam m. lam p. mapInsert p.tyvar p.f m) env.varFunctions paramFNames} in

    let constructors = mapIntersectWith
      (lam. lam pair. pair.1)
      (mapLookupOr (setEmpty nameCmp) x.ident env.tcEnv.conDeps)
      env.tcEnv.conEnv in

    let lName = nameSym "l" in
    let rName = nameSym "r" in
    let addMatch = lam acc. lam c. lam t.
      match acc with (env, tm) in
      match inst (infoTy t) 0 t with TyArrow {from = from, to = to} in
      let uni = emptyUnification () in
      match unifyPure uni to fullType with Some uni then
        let from = pureApplyUniToType uni from in
        match getEqFunction env from with (env, subf) in
        let subl = nameSym "subl" in
        let subr = nameSym "subr" in
        let tm = match_ (nvar_ lName) (npcon_ c (npvar_ subl))
          (match_ (nvar_ rName) (npcon_ c (npvar_ subr))
            (appf2_ subf (nvar_ subl) (nvar_ subr))
            false_)
          tm in
        (env, tm)
      else error "Unification should always be possible here" in
    match mapFoldWithKey addMatch (env, never_) constructors with (env, matchChain) in
    let matchChain = nulam_ lName (nulam_ rName matchChain) in
    let body = foldr (lam p. lam body. nulam_ p.f body) matchChain paramFNames in
    let tyAnnot = foldr
      (lam p. lam ty. tyarrow_ (tyarrows_ [ntyvar_ p.tyvar, ntyvar_ p.tyvar, tybool_]) ty)
      (tyarrows_ [fullType, fullType, tybool_])
      paramFNames in
    let tyAnnot = foldr
      (lam p. lam ty. ntyall_ p.tyvar ty)
      tyAnnot
      paramFNames in

    let env = {env with varFunctions = prevVarFunctions, newFunctions = snoc env.newFunctions (fname, tyAnnot, body)} in
    (env, nvar_ fname)
end

lang GenerateEqVar = GenerateEq + VarTypeAst
  -- NOTE(vipa, 2025-01-27): This function will error when it
  -- encounters a polymorphic value of unknown type. We could
  -- arbitrarily say "equal" or "not equal", but that seems error
  -- prone, or we could somehow ask surrounding code to be rewritten
  -- to carry an extra eq function for the polymorphic type.
  sem _getEqFunction env +=
  | TyVar x ->
    match mapLookup x.ident env.varFunctions with Some fname
    then (env, nvar_ fname)
    else errorSingle [x.info] (join ["I don't know how to compare values of the polymorphic type ", nameGetStr x.ident])
end

lang MExprGenerateEq
  = GenerateEqRecord
  + GenerateEqBool
  + GenerateEqInt
  + GenerateEqFloat
  + GenerateEqSeq
  + GenerateEqChar
  + GenerateEqApp
  + GenerateEqCon
  + GenerateEqVar
end

lang GenerateEqLoader = LoaderInterface + GenerateEq
  syn Hook +=
  | EqHook
    { baseEnv : GEqEnv
    , functions : Ref (Map Name Name)  -- Names for TyCon related Eq functions
    }

  sem enableEqGeneration : Loader -> Loader
  sem enableEqGeneration = | loader ->
    if hasHook (lam x. match x with EqHook _ then true else false) loader then loader else

    match includeFileExn "." "stdlib::seq.mc" loader with (seqEnv, loader) in
    match includeFileExn "." "stdlib::bool.mc" loader with (boolEnv, loader) in

    let baseEnv =
      { conFunctions = mapEmpty nameCmp
      , varFunctions = mapEmpty nameCmp
      , newFunctions = []
      , tcEnv = typcheckEnvEmpty
      , eqSeq = _getVarExn "eqSeq" seqEnv
      , eqBool = _getVarExn "eqBool" boolEnv
      } in

    let hook = EqHook
      { baseEnv = baseEnv
      , functions = ref (mapEmpty nameCmp)
      } in
    addHook loader hook

  sem _eqFunctionsFor : [Type] -> Loader -> Hook -> Option (Loader, [Expr])
  sem _eqFunctionsFor tys loader =
  | _ -> None ()
  | EqHook hook ->
    let f = lam tcEnv.
      let env = {hook.baseEnv with conFunctions = deref hook.functions, tcEnv = tcEnv} in
      (tcEnv, mapAccumL getEqFunction env tys) in
    match _withTCEnv f loader with (loader, (env, printFs)) in

    modref hook.functions env.conFunctions;
    let loader = if null env.newFunctions
      then loader
      -- NOTE(vipa, 2026-08-17): We don't need to capture the
      -- definitions in a SymEnv, because they're already registered
      -- in the GEqEnv
      else (_addDeclExn _symEnvEmpty loader (nreclets_ env.newFunctions)).1 in
    Some (loader, printFs)

  sem eqFunctionsFor : [Type] -> Loader -> (Loader, [Expr])
  sem eqFunctionsFor tys = | loader ->
    withHookState (_eqFunctionsFor tys) loader
end
