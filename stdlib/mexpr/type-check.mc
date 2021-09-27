-- Type check MExpr terms, annotating AST nodes with the results.
--
-- The type system is based on FreezeML [1], and gives ML-style
-- type inference along with the expressive power of System F
-- with low syntactic overhead.
--
-- The implementation uses efficient side-effecting unification,
-- as described in [2].
--
-- [1]: https://dl.acm.org/doi/abs/10.1145/3385412.3386003
-- [2]: http://okmij.org/ftp/ML/generalization.html.

include "ast.mc"
include "ast-builder.mc"
include "eq.mc"
include "pprint.mc"


type TypeEnv = {
  varEnv: Map Name Type
}

let _typeEnvEmpty = {
  varEnv = mapEmpty nameCmp
}

let _lookupVar = lam name. lam tyenv : TypeEnv.
  match tyenv with {varEnv=varEnv} then
    mapLookup name varEnv
  else never

let _insertVar = lam name. lam ty. lam tyenv : TypeEnv.
  match tyenv with {varEnv=varEnv} then
    let varEnvNew = mapInsert name ty varEnv in
    {varEnv = varEnvNew}
  else never


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
      else
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

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newvarNamed = use VarTypeAst in
  lam name. TyVar {info = NoInfo (),
                   contents = ref (Unbound {ident = name, level = 0})}

let newvar = lam. newvarNamed (nameSym "v")

lang Generalize
  sem inst =
  -- Intentionally left empty
  sem gen =
  -- Intentionally left empty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem inst =
  | TyVar t & ty1 ->
    match deref t.contents with Link ty2 then
      inst ty2
    else ty1
  | TyQVar {ident = n} -> newvarNamed n

  sem gen =
  | TyVar t ->
    match deref t.contents with Link ty then
      gen ty
    else match deref t.contents with Unbound {ident = n} then
      TyQVar {ident = n}
    else never
end

lang FunTypeGeneralize = Generalize + FunTypeAst
  sem inst =
  | TyArrow r ->
    TyArrow {{r with from = inst r.from} with to = inst r.to}

  sem gen =
  | TyArrow r ->
    TyArrow {{r with from = gen r.from} with to = gen r.to}
end

-------------------
-- TYPE CHECKING --
-------------------

lang TypeCheck = Unify + Generalize
  sem typeOf =
  | t -> typeOfBase _typeEnvEmpty t

  sem typeOfBase (env : TypeEnv) =
  | t ->
    let msg = join [
      "Type check failed: type checking not supported for term\n",
      use MExprPrettyPrint in expr2str t
    ] in
    infoErrorExit (infoTm t) msg
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeOfBase (env : TypeEnv) =
  | TmVar t ->
    match _lookupVar t.ident env with Some ty then
      inst ty
    else
      let msg = join [
        "Type check failed: reference to unbound variable\n",
        "Var: ", nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang LamTypeCheck = TypeCheck + LamAst
  sem typeOfBase (env : TypeEnv) =
  | TmLam t ->
    let tyX = newvar () in
    let tyE = typeOfBase (_insertVar t.ident tyX env) t.body in
    ityarrow_ t.info tyX tyE
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeOfBase (env : TypeEnv) =
  | TmApp t ->
    let tyFun = typeOfBase env t.lhs in
    let tyArg = typeOfBase env t.rhs in
    let tyRes = newvar () in
    unify (tyFun, tyarrow_ tyArg tyRes);
    tyRes
end

lang LetTypeCheck = TypeCheck + LetAst
  sem typeOfBase (env : TypeEnv) =
  | TmLet t ->
    let tyE = typeOfBase env t.body in
    typeOfBase (_insertVar t.ident (gen tyE) env) t.inexpr
end

lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FunTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FunTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck

end
