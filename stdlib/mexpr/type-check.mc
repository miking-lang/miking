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

lang ConstTypeAst =
  UnknownTypeAst + IntTypeAst + BoolTypeAst + FloatTypeAst + CharTypeAst
end

----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = MExprEq
  -- Unify the types `ty1' and `ty2'. Modifies the types in place.
  sem unify =
  | (ty1, ty2) -> unifyWithNames biEmpty (ty1, ty2)

  -- Unify the types `ty1' and `ty2', assuming that any pair of type variables in
  -- `names' are equal.
  sem unifyWithNames (names : BiNameMap) =
  | (ty1, ty2) ->
    -- OPT(aathn, 2021-09-27): This equality check traverses the types unnecessarily.
    -- TODO(aathn, 2021-09-28): This equality check uses empty type environment.
    if eqType ty1 ty2 then
      ()
    else
      unifyBase names (ty1, ty2)

  sem unifyBase (names : BiNameMap) =
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

  -- checkBeforeUnify is called before a variable `tv' is unified with another type.
  -- Performs three tasks in one traversal:
  -- - Occurs check
  -- - Update level fields of TVars
  -- - If `tv' is monomorphic, ensure it is not unified with a polymorphic type
  sem checkBeforeUnify (tv : TVar) =
  -- Intentionally left empty
end

lang VarTypeUnify = Unify + VarTypeAst + UnknownTypeAst
  sem unifyBase (names : BiNameMap) =
  -- We don't unify variables with TyUnknown
  | (TyFlex {contents = r}, !TyUnknown _ & ty1)
  | (!TyUnknown _ & ty1, TyFlex {contents = r}) ->
    match deref r with Unbound _ & tv then
      checkBeforeUnify tv ty1; modref r (Link ty1)
    else match deref r with Link ty2 then
      unifyWithNames names (ty1, ty2)
    else never
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if not (nameEq t1.ident t2.ident) then
      match biLookup (t1.ident, t2.ident) names with None () then
        unificationError (ty1, ty2)
      else ()
    else ()

  sem checkBeforeUnify (tv : TVar) =
  | TyFlex {info = info, contents = r} ->
    -- TODO(aathn, 2021-09-28): This equality check uses empty type environment.
    if eqTVar [] (deref r, tv) then
      let msg = "Type check failed: occurs check\n" in
      infoErrorExit info msg
    else
      match deref r with Link ty then
        checkBeforeUnify tv ty
      else match deref r with Unbound ({level = k} & t) then
        let minLevel =
          match tv with Unbound {level = l} then mini k l else k
        in
        modref r (Unbound {t with level = minLevel})
      else never
  | TyVar _ ->
    ()
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyArrow {from = from1, to = to1}, TyArrow {from = from2, to = to2}) ->
    unifyWithNames names (from1, from2);
    unifyWithNames names (to1, to2)

  sem checkBeforeUnify (tv : TVar) =
  | TyArrow {from = from, to = to} ->
    checkBeforeUnify tv from;
    checkBeforeUnify tv to
end

lang AllTypeUnify = Unify + AllTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyAll t1, TyAll t2) ->
    unifyWithNames (biInsert (t1.ident, t2.ident) names) (t1.ty, t2.ty)

  sem checkBeforeUnify (tv : TVar) =
  | TyAll t ->
    match tv with Unbound {weak = true} then
      let msg = join [
        "Type check failed: unification failure\n",
        "Attempted to unify monomorphic type variable with polymorphic type!\n"
      ] in
      infoErrorExit t.info msg
    else
      checkBeforeUnify tv t.ty
end

lang ConstTypeUnify = Unify + ConstTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyUnknown _, _)
  | (_, TyUnknown _) ->
    ()

  sem checkBeforeUnify (tv : TVar) =
  | TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _ ->
    ()
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TySeq t1, TySeq t2) ->
    unifyWithNames names (t1.ty, t2.ty)

  sem checkBeforeUnify (tv : TVar) =
  | TySeq t ->
    checkBeforeUnify tv t.ty
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newflexvar = use VarTypeAst in
  lam weak. lam level. lam info.
  TyFlex {info = info,
          contents = ref (Unbound {ident = nameSym "a", level = level, weak = weak})}

let newvarWeak = newflexvar true
let newvar = newflexvar false

lang Generalize = AllTypeAst
  -- Instantiate the top-level type variables of `ty' with fresh schematic variables.
  sem inst (lvl : Level) =
  | ty ->
    match stripTyAll ty with (vars, ty) then
      let fi = infoTy ty in
      let subst = foldr (lam v. mapInsert v (newvar lvl fi)) (mapEmpty nameCmp) vars in
      if gti (length vars) 0 then
        instBase subst ty
      else
        ty
    else never

  sem instBase (subst : Map Name TVar) =
  -- Intentionally left empty

  -- Generalize all flexible (schematic) type variables in `ty'.
  sem gen (lvl : Level) =
  | ty ->
    match genBase lvl ty with (vars, genTy) then
      let fi = infoTy genTy in
      let vars = distinct nameEq vars in
      foldr (lam v. lam ty. TyAll {info = fi, ident = v, ty = ty}) genTy vars
    else never

  sem genBase (lvl : Level) =
  -- Intentionally left empty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem instBase (subst : Map Name Type) =
  | TyFlex t & ty1 ->
    match deref t.contents with Link ty2 then
      instBase subst ty2
    else
      ty1
  | TyVar {ident = n} & ty ->
    match mapLookup n subst with Some tyvar then tyvar
    else ty

  sem genBase (lvl : Level) =
  | TyFlex t ->
    match deref t.contents with Link ty then
      genBase lvl ty
    else match deref t.contents with Unbound {ident = n, level = k} then
      if gti k lvl then
        -- Var is free, generalize
        ([n], TyVar {info = t.info, ident = n})
      else
        -- Var is bound in previous let, don't generalize
        ([], TyFlex t)
    else never
  | TyVar _ & ty ->
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

lang ConstTypeGeneralize = Generalize + ConstTypeAst
  sem instBase (subst : Map Name Type) =
  | (TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _) & ty -> ty
  sem genBase (lvl : Level) =
  | (TyUnknown _ | TyInt _ | TyBool _ | TyFloat _ | TyChar _) & ty -> ([], ty)
end

lang SeqTypeGeneralize = Generalize + SeqTypeAst
  sem instBase (subst : Map Name Type) =
  | TySeq t ->
    TySeq {t with ty = instBase subst t.ty}

  sem genBase (lvl : Level) =
  | TySeq t ->
    match genBase lvl t.ty with (vars, ty) then
      (vars, TySeq {t with ty = ty})
    else never
end

-------------------
-- TYPE CHECKING --
-------------------

lang TypeCheck = Unify + Generalize
  -- Type check `tm', with FreezeML-style type inference.
  sem typeCheck =
  | tm -> typeCheckBase _tcEnvEmpty tm

  sem typeCheckBase (env : TCEnv) =
  | tm ->
    let msg = join [
      "Type check failed: type checking not supported for term\n",
      use MExprPrettyPrint in expr2str tm
    ] in
    infoErrorExit (infoTm tm) msg
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeCheckBase (env : TCEnv) =
  | TmVar t ->
    match _lookupVar t.ident env with Some ty then
      let ty =
        if t.frozen then ty
        else inst env.currentLvl ty
      in
      TmVar {t with ty = ty}
    else
      let msg = join [
        "Type check failed: reference to unbound variable\n",
        "Var: ", nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang LamTypeCheck = TypeCheck + LamAst
  sem typeCheckBase (env : TCEnv) =
  | TmLam t ->
    let tyIdent =
      match t.tyIdent with TyUnknown _ then
        -- No type annotation: assign a monomorphic type variable to x.
        newvarWeak env.currentLvl t.info
      else
        -- Type annotation: assign x its annotated type.
        t.tyIdent
    in
    let body = typeCheckBase (_insertVar t.ident tyIdent env) t.body in
    let tyLam = ityarrow_ t.info tyIdent (ty body) in
    TmLam {{{t with body = body}
               with tyIdent = tyIdent}
               with ty = tyLam}
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeCheckBase (env : TCEnv) =
  | TmApp t ->
    let lhs = typeCheckBase env t.lhs in
    let rhs = typeCheckBase env t.rhs in
    let tyRes = newvar env.currentLvl t.info in
    unify (ty lhs, tyarrow_ (ty rhs) tyRes);
    TmApp {{{t with lhs = lhs}
               with rhs = rhs}
               with ty = tyRes}
end

lang LetTypeCheck = TypeCheck + LetAst
  sem typeCheckBase (env : TCEnv) =
  | TmLet t ->
    let lvl = env.currentLvl in
    let body = typeCheckBase {env with currentLvl = addi 1 lvl} t.body in
    let tyBody =
      match t.tyBody with TyUnknown _ then
        -- No type annotation: generalize the inferred type
        gen lvl (ty body)
      else
        -- Type annotation: unify the annotated type with the inferred one
        match stripTyAll t.tyBody with (_, tyAnnot) then
          unify (tyAnnot, ty body);
          t.tyBody
        else never
    in
    let inexpr = typeCheckBase (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {{{{t with body = body}
                with tyBody = tyBody}
                with inexpr = inexpr}
                with ty = ty inexpr}
end

lang ConstTypeCheck = TypeCheck + MExprConstType
  sem typeCheckBase (env : TCEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = f (tyConst t.val) in
    TmConst {t with ty = ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckBase (env : TCEnv) =
  | TmSeq t ->
    let elemTy = newvar env.currentLvl t.info in
    let tms = map (typeCheckBase env) t.tms in
    iter (lam tm. unify (elemTy, ty tm)) tms;
    TmSeq {{t with tms = tms}
              with ty = ityseq_ t.info elemTy}
end

lang UtestTypeCheck = TypeCheck + UtestAst
  sem typeCheckBase (env : TCEnv) =
  | TmUtest t ->
    let test = typeCheckBase env t.test in
    let expected = typeCheckBase env t.expected in
    let next = typeCheckBase env t.next in
    let tusing = optionMap (typeCheckBase env) t.tusing in
    (match tusing with Some tu then
       unify (ty tu) (tyarrows_ [ty test, ty expected, tybool_])
     else
       unify (ty test) (ty expected));
    TmUtest {{{{{t with test = test}
                   with expected = expected}
                   with next = next}
                   with tusing = tusing}
                   with ty = ty next}
end

lang NeverTypeCheck = TypeCheck + NeverAst
  sem typeCheckBase (env : TCEnv) =
  | TmNever t -> TmNever {t with ty = newvar env.currentLvl t.info}
end

lang ExtTypeCheck = TypeCheck + ExtAst
  sem typeCheckBase (env : TCEnv) =
  | TmExt t ->
    let env = {env with varEnv = mapInsert t.ident t.tyIdent env.varEnv} in
    let inexpr = typeCheckBase env t.inexpr in
    TmExt {{t with inexpr = inexpr}
              with ty = ty inexpr}
end


lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FunTypeUnify + AllTypeUnify + ConstTypeUnify +
  SeqTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FunTypeGeneralize + AllTypeGeneralize +
  ConstTypeGeneralize + SeqTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck
  + ConstTypeCheck + SeqTypeCheck + UtestTypeCheck + NeverTypeCheck
  + ExtTypeCheck

end

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure

-- TODO(aathn, 2021-09-28): Test cases

-- TODO(aathn, 2021-09-28): Value restriction

-- TODO(aathn, 2021-09-28): Type check remaining terms
