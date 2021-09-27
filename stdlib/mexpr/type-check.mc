-- Type check MExpr terms, annotating AST nodes with the results.
--
-- The type system is based on FreezeML [1], and gives ML-style
-- type inference along with the expressive power of System F
-- with low syntactic overhead.
--
-- The implementation uses efficient side-effecting unification,
-- as described in [2]. The current implementation corresponds to
-- the sound but eager version described.
--
-- [1]: https://dl.acm.org/doi/abs/10.1145/3385412.3386003
-- [2]: http://okmij.org/ftp/ML/generalization.html.

include "ast.mc"
include "ast-builder.mc"
include "const-types.mc"
include "eq.mc"
include "math.mc"
include "pprint.mc"
include "seq.mc"

type TCEnv = {
  varEnv: Map Name Type,
  currentLvl: Level
}

let _tcEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  currentLvl = 1
}

let _lookupVar = lam name. lam tyenv : TCEnv.
  mapLookup name tyenv.varEnv

let _insertVar = lam name. lam ty. lam tyenv : TCEnv.
  let varEnvNew = mapInsert name ty tyenv.varEnv in
  {tyenv with varEnv = varEnvNew}


let _pprintType = use MExprPrettyPrint in
  lam ty.
  match getTypeStringCode 0 pprintEnvEmpty ty with (_,tyStr) then
    tyStr
  else never

----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = MExprEq
  sem unify =
  | (ty1, ty2) ->
    -- OPT(aathn, 2021-09-27): This equality check traverses the types unnecessarily.
    if eqType [] ty1 ty2 then
      ()
    else
      unifyBase (ty1, ty2)

  sem unifyBase =
  | (ty1, ty2) ->
    unificationError (ty1, ty2)

  sem unificationError =
  | (ty1, ty2) ->
    let msg = join [
      "Type check failed: unification failure\n",
      "LHS: ", _pprintType ty1, "\n",
      "RHS: ", _pprintType ty2, "\n"
    ] in
    infoErrorExit (infoTy ty1) msg

  sem occurs (tv : TVar) =
  -- Intentionally left empty
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase =
  | (TyVar {contents = r}, ty1)
  | (ty1, TyVar {contents = r}) ->
    match deref r with Unbound _ & tv then
      occurs tv ty1; modref r (Link ty1)
    else match deref r with Link ty2 then
      unify (ty1, ty2)
    else never
  -- No case needed for TyQVar

  sem occurs (tv : TVar) =
  | TyVar {info = info, contents = r} ->
    if eqTVar [] (deref r, tv) then
      let msg = "Type check failed: occurs check\n" in
      infoErrorExit info msg
    else
      match deref r with Link ty then
        occurs tv ty
      else match deref r with Unbound {ident = n, level = k} then
        let minLevel =
          match tv with Unbound {ident = _, level = l} then mini k l else k
        in
        modref r (Unbound {ident = n, level = minLevel})
      else never
  | TyQVar _ ->
    ()
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase =
  | (TyArrow {from = from1, to = to1}, TyArrow {from = from2, to = to2}) ->
    unify (from1, from2);
    unify (to1, to2)

  sem occurs (tv : TVar) =
  | TyArrow {from = from, to = to} ->
    occurs tv from;
    occurs tv to
end

lang AllTypeUnify = Unify + AllTypeAst
  -- sem unifyBase =
  -- | (TyAll t1, TyAll t2) -> ...

  sem occurs (tv : TVar) =
  | TyAll t ->
    occurs tv t.ty
end

lang BaseTypeUnify = Unify + BaseTypeAst
  sem unifyBase = -- Intentionally left empty
  sem occurs (tv : TVar) =
  | TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _ -> ()
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newvar = use VarTypeAst in
  lam level.
  TyVar {info = NoInfo (),
         contents = ref (Unbound {ident = nameSym "a", level = level})}

lang Generalize = AllTypeAst
  sem inst (lvl : Level) =
  | ty ->
    match instMakeSubst lvl (mapEmpty nameCmp) ty with (subst, ty) then
      instBase subst ty
    else never

  sem instMakeSubst (lvl : Level) (subst : Map Name TVar) =
  | TyAll t ->
    let tv = newvar lvl in
    instMakeSubst lvl (mapInsert t.ident tv subst) t.ty
  | ty ->
    (subst, ty)

  sem instBase (subst : Map Name TVar) =
  -- Intentionally left empty

  sem gen (lvl : Level) =
  | ty ->
    match genBase lvl ty with (vars, genTy) then
      let fi = infoTy genTy in
      let vars = distinct nameEq vars in
      foldr (lam v. lam ty. TyAll {info = fi, ident = v, ty = ty}) genTy vars
    else never

  sem genBase (lvl : Level) =
  | ty ->
    print (_pprintType ty);
    error "No matching case for function genBase" -- Intentionally left empty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem instBase (subst : Map Name Type) =
  | TyVar t & ty1 ->
    match deref t.contents with Link ty2 then
      instBase subst ty2
    else
      ty1
  | TyQVar {ident = n} & ty ->
    match mapLookup n subst with Some tyvar then tyvar
    else ty

  sem genBase (lvl : Level) =
  | TyVar t ->
    match deref t.contents with Link ty then
      genBase lvl ty
    else match deref t.contents with Unbound {ident = n, level = k} then
      if gti k lvl then
        ([n], TyQVar {ident = n})
      else
        ([], TyVar t)
    else never
  | TyQVar _ & ty ->
    ([], ty)
end

lang FunTypeGeneralize = Generalize + FunTypeAst
  sem instBase (subst : Map Name Type) =
  | TyArrow r ->
    TyArrow {{r with from = instBase subst r.from}
                with to = instBase subst r.to}

  sem genBase (lvl : Level) =
  | TyArrow r ->
    match genBase lvl r.from with (vars1, fromNew) then
      match genBase lvl r.to with (vars2, toNew) then
        (concat vars1 vars2, TyArrow {{r with from = fromNew} with to = toNew})
      else never
    else never
end

lang AllTypeGeneralize = Generalize
  sem instBase (subst : Map Name Type) =
  | TyAll t ->
    TyAll {t with ty = instBase subst t.ty}

  sem genBase (lvl : Level) =
  | TyAll t ->
    match genBase lvl t.ty with (vars, ty) then
      (vars, TyAll {t with ty = ty})
    else never
end

lang BaseTypeGeneralize = Generalize + BaseTypeAst
  sem instBase (subst : Map Name Type) =
  | (TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _) & ty -> ty
  sem genBase (lvl : Level) =
  | (TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _) & ty -> ([], ty)
end


-------------------
-- TYPE CHECKING --
-------------------

lang TypeCheck = Unify + Generalize
  sem typeOf =
  | t -> typeOfBase _tcEnvEmpty t

  sem typeOfBase (env : TCEnv) =
  | t ->
    let msg = join [
      "Type check failed: type checking not supported for term\n",
      use MExprPrettyPrint in expr2str t
    ] in
    infoErrorExit (infoTm t) msg
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeOfBase (env : TCEnv) =
  | TmVar t ->
    match _lookupVar t.ident env with Some ty then
      if t.frozen then
        ty
      else
        inst env.currentLvl ty
    else
      let msg = join [
        "Type check failed: reference to unbound variable\n",
        "Var: ", nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang LamTypeCheck = TypeCheck + LamAst
  sem typeOfBase (env : TCEnv) =
  | TmLam t ->
    let tyX = newvar env.currentLvl in
    let tyE = typeOfBase (_insertVar t.ident tyX env) t.body in
    ityarrow_ t.info tyX tyE
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeOfBase (env : TCEnv) =
  | TmApp t ->
    let tyFun = typeOfBase env t.lhs in
    let tyArg = typeOfBase env t.rhs in
    let tyRes = newvar env.currentLvl in
    unify (tyFun, tyarrow_ tyArg tyRes);
    tyRes
end

lang LetTypeCheck = TypeCheck + LetAst
  sem typeOfBase (env : TCEnv) =
  | TmLet t ->
    let lvl = env.currentLvl in
    let tyE = typeOfBase {env with currentLvl = addi 1 lvl} t.body in
    typeOfBase (_insertVar t.ident (gen lvl tyE) env) t.inexpr
end

lang ConstTypeCheck = TypeCheck + MExprConstType
  sem typeOfBase (env : TCEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    f (tyConst t.val)
end

lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FunTypeUnify + AllTypeUnify + BaseTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FunTypeGeneralize + AllTypeGeneralize + BaseTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck
  + ConstTypeCheck

end

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure

-- TODO(aathn, 2021-09-28): Test cases

-- TODO(aathn, 2021-09-28): Annotate terms instead of just returning their type
