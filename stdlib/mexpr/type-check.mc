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
include "eq.mc"
include "math.mc"
include "pprint.mc"

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

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newvar = use VarTypeAst in
  lam level.
  TyVar {info = NoInfo (),
         contents = ref (Unbound {ident = nameSym "a", level = level})}

lang Generalize
  sem inst (lvl : Level) =
  | ty ->
    match instBase lvl (mapEmpty nameCmp) ty with (_, ty) then ty
    else never

  sem instBase (lvl : Level) (subst : Map Name TVar) =
  -- Intentionally left empty

  sem gen (lvl : Level) =
  -- Intentionally left empty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem instBase (lvl : Level) (subst : Map Name TVar) =
  | TyVar t & ty1 ->
    match deref t.contents with Link ty2 then
      instBase lvl subst ty2
    else
      (subst, ty1)
  | TyQVar {ident = n} ->
    match mapLookup n subst with Some tv then
      (subst, tv)
    else
      let tv = newvar lvl in
      let substNew = mapInsert n tv subst in
      (substNew, tv)

  sem gen (lvl : Level) =
  | TyVar t ->
    match deref t.contents with Link ty then
      gen lvl ty
    else match deref t.contents with Unbound {ident = n, level = k} then
      if gti k lvl then
        TyQVar {ident = n}
      else
        TyVar t
    else never
end

lang FunTypeGeneralize = Generalize + FunTypeAst
  sem instBase (lvl : Level) (subst : Map Name TVar) =
  | TyArrow r ->
    match instBase lvl subst r.from with (subst1, fromNew) then
      match instBase lvl subst1 r.to with (subst2, toNew) then
        (subst2, TyArrow {{r with from = fromNew} with to = toNew})
      else never
    else never

  sem gen (lvl : Level) =
  | TyArrow r ->
    TyArrow {{r with from = gen lvl r.from} with to = gen lvl r.to}
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

lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FunTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FunTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck

end
