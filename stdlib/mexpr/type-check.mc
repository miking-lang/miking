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

lang Unify = MExprAst
  -- Unify the types `ty1' and `ty2'. Modifies the types in place.
  sem unify (ty1 : Type) =
  | ty2 ->
    unifyBase biEmpty (ty1, ty2)

  -- Unify the types `ty1' and `ty2', assuming that any pair of type variables in
  -- `names' are equal.
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
  sem checkBeforeUnify (tv : TVarRec) =
  | ty ->
    sfold_Type_Type (lam. lam ty. checkBeforeUnify tv ty) () ty
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if not (nameEq t1.ident t2.ident) then
      match biLookup (t1.ident, t2.ident) names with None () then
        unificationError (ty1, ty2)
      else ()
    else ()
end

lang FlexTypeUnify = Unify + FlexTypeAst + UnknownTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyFlex {contents = r1} & ty1, TyFlex {contents = r2} & ty2) ->
    match (deref r1, deref r2) with (Unbound {ident = n}, Unbound {ident = m}) then
      if not (nameEq n m) then
        modref r1 (Link ty2)
      else ()
    else
      unifyBase names (resolveLink ty1, resolveLink ty2)
  | (TyFlex {contents = r} & ty1, !(TyUnknown _ | TyFlex _) & ty2)
  | (!(TyUnknown _ | TyFlex _) & ty2, TyFlex {contents = r} & ty1) ->
    match deref r with Unbound tv then
      checkBeforeUnify tv ty2; modref r (Link ty2)
    else
      unifyBase names (resolveLink ty1, ty2)

  sem checkBeforeUnify (tv : TVarRec) =
  | TyFlex {info = info, contents = r} ->
    match deref r with Unbound t then
      if nameEq t.ident tv.ident then
        let msg = "Type check failed: occurs check\n" in
        infoErrorExit info msg
      else
        let updated = Unbound {{t with level = mini t.level tv.level}
                                  with weak  = or t.weak tv.weak} in
        modref r updated
    else match deref r with Link ty then
      checkBeforeUnify tv ty
    else never
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyArrow {from = from1, to = to1}, TyArrow {from = from2, to = to2}) ->
    unifyBase names (from1, from2);
    unifyBase names (to1, to2)
end

lang AllTypeUnify = Unify + AllTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyAll t1, TyAll t2) ->
    unifyBase (biInsert (t1.ident, t2.ident) names) (t1.ty, t2.ty)

  sem checkBeforeUnify (tv : TVarRec) =
  | TyAll t ->
    match tv with {weak = true} then
      let msg = join [
        "Type check failed: unification failure\n",
        "Attempted to unify monomorphic type variable with polymorphic type!\n"
      ] in
      infoErrorExit t.info msg
    else
      checkBeforeUnify tv t.ty
end

lang BoolTypeUnify = Unify + BoolTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyBool _, TyBool _) -> ()
end

lang IntTypeUnify = Unify + IntTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyInt _, TyInt _) -> ()
end

lang FloatTypeUnify = Unify + FloatTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyFloat _, TyFloat _) -> ()
end

lang CharTypeUnify = Unify + CharTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyChar _, TyChar _) -> ()
end

lang UnknownTypeUnify = Unify + UnknownTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyUnknown _, _)
  | (_, TyUnknown _) ->
    ()
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TySeq t1, TySeq t2) ->
    unifyBase names (t1.ty, t2.ty)
end

lang TensorTypeUnify = Unify + TensorTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyTensor t1, TyTensor t2) ->
    unifyBase names (t1.ty, t2.ty)
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newflexvar =
  lam weak. lam level. lam info.
  tyFlexUnbound info (nameSym "a") level weak

let newvarWeak = newflexvar true
let newvar = newflexvar false

lang Generalize = AllTypeAst
  -- Instantiate the top-level type variables of `ty' with fresh schematic variables.
  sem inst (lvl : Level) =
  | ty ->
    match stripTyAll ty with (vars, ty) then
      if gti (length vars) 0 then
        let fi = infoTy ty in
        let inserter = lam v. mapInsert v (newvar lvl fi) in
        let subst = foldr inserter (mapEmpty nameCmp) vars in
        instBase subst ty
      else
        ty
    else never

  sem instBase (subst : Map Name Type) =
  | ty ->
    smap_Type_Type (instBase subst) ty

  -- Generalize all flexible (schematic) type variables in `ty'.
  sem gen (lvl : Level) =
  | ty ->
    match genBase lvl ty with (vars, genTy) then
      let fi = infoTy genTy in
      let vars = distinct nameEq vars in
      foldr (lam v. lam ty. TyAll {info = fi, ident = v, ty = ty}) genTy vars
    else never

  sem genBase (lvl : Level) =
  | ty ->
    smapAccumL_Type_Type (lam vars1. lam ty.
      match genBase lvl ty with (vars2, ty) then
        (concat vars1 vars2, ty)
      else never
    ) [] ty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem instBase (subst : Map Name Type) =
  | TyVar {ident = n} & ty ->
    match mapLookup n subst with Some tyvar then tyvar
    else ty
end

lang FlexTypeGeneralize = Generalize + FlexTypeAst + VarTypeAst
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
end

-- The default cases handle all other constructors!

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

lang PatTypeCheck = Unify
  sem typeCheckPat (env : TCEnv) =
  | pat ->
    let msg = join [
      "Type check failed: type checking not supported for pattern\n",
      use MExprPrettyPrint in
      match getPatStringCode 0 pprintEnvEmpty pat with (_, str)
      then str else never
    ] in
    infoErrorExit (infoPat pat) msg
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
    let tyX = optionGetOrElse
      -- No type annotation: assign a monomorphic type variable to x
      (lam. newvarWeak env.currentLvl t.info)
      -- Type annotation: assign x its annotated type
      (sremoveUnknown t.tyIdent)
    in
    let body = typeCheckBase (_insertVar t.ident tyX env) t.body in
    let tyLam = ityarrow_ t.info tyX (tyTm body) in
    TmLam {{t with body = body}
              with ty = tyLam}
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeCheckBase (env : TCEnv) =
  | TmApp t ->
    let lhs = typeCheckBase env t.lhs in
    let rhs = typeCheckBase env t.rhs in
    let tyRes = newvar env.currentLvl t.info in
    unify (tyTm lhs) (ityarrow_ (infoTm lhs) (tyTm rhs) tyRes);
    TmApp {{{t with lhs = lhs}
               with rhs = rhs}
               with ty = tyRes}
end

lang LetTypeCheck = TypeCheck + LetAst
  sem typeCheckBase (env : TCEnv) =
  | TmLet t ->
    let lvl = env.currentLvl in
    let body = typeCheckBase {env with currentLvl = addi 1 lvl} t.body in
    let tyBody = optionMapOrElse
      -- No type annotation: generalize the inferred type
      (lam. gen lvl (tyTm body))
      -- Type annotation: unify the annotated type with the inferred one
      (lam ty.
        match stripTyAll ty with (_, tyAnnot) then
          unify tyAnnot (tyTm body);
          ty
        else never)
      (sremoveUnknown t.tyBody)
    in
    let inexpr = typeCheckBase (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {{{t with body = body}
               with inexpr = inexpr}
               with ty = tyTm inexpr}
end

lang RecLetsTypeCheck = TypeCheck + RecLetsAst
  sem typeCheckBase (env : TCEnv) =
  | TmRecLets t ->
    let lvl = env.currentLvl in

    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b : RecLetBinding.
      let tyBinding = optionGetOrElse
        (lam. newvar (addi 1 lvl) b.info)
        (sremoveUnknown b.tyBody)
      in
      _insertVar b.ident tyBinding acc
    in
    let recLetEnv : TCEnv = foldl recLetEnvIteratee env t.bindings in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b : RecLetBinding.
      let body = typeCheckBase {recLetEnv with currentLvl = addi 1 lvl} b.body in
      optionMapOrElse
        -- No type annotation: unify the inferred type of the body with the
        -- inferred type of the binding
        (lam.
          match _lookupVar b.ident recLetEnv with Some ty then
            unify ty (tyTm body)
          else never)
        -- Type annotation: unify the inferred type of the body with the annotated one
        (lam ty.
          match stripTyAll ty with (_, tyAnnot) then
            unify tyAnnot (tyTm body)
          else never)
        (sremoveUnknown b.tyBody);
      {b with body = body}
    in
    let bindings = map typeCheckBinding t.bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      let tyBody = optionGetOrElse
        (lam. gen lvl (tyTm b.body))
        (sremoveUnknown b.tyBody)
      in
      _insertVar b.ident tyBody acc
    in
    let env = foldl envIteratee env bindings in
    let inexpr = typeCheckBase env t.inexpr in
    TmRecLets {{{t with bindings = bindings}
                   with inexpr = inexpr}
                   with ty = tyTm inexpr}
end

lang MatchTypeCheck = TypeCheck + PatTypeCheck + MatchAst
  sem typeCheckBase (env : TCEnv) =
  | TmMatch t ->
    let target = typeCheckBase env t.target in
    match typeCheckPat env t.pat with (thnEnv, pat) then
      unify (tyTm target) (tyPat pat);
      let thn = typeCheckBase thnEnv t.thn in
      let els = typeCheckBase env t.els in
      unify (tyTm thn) (tyTm els);
      TmMatch {{{{{t with target = target}
                     with thn = thn}
                     with els = els}
                     with ty = tyTm thn}
                     with pat = pat}
    else never
end

lang ConstTypeCheck = TypeCheck + MExprConstType
  sem typeCheckBase (env : TCEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = inst env.currentLvl (f (tyConst t.val)) in
    TmConst {t with ty = ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckBase (env : TCEnv) =
  | TmSeq t ->
    let elemTy = newvar env.currentLvl t.info in
    let tms = map (typeCheckBase env) t.tms in
    iter (compose (unify elemTy) tyTm) tms;
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
       unify (tyTm tu, tyarrows_ [tyTm test, tyTm expected, tybool_])
     else
       unify (tyTm test, tyTm expected));
    TmUtest {{{{{t with test = test}
                   with expected = expected}
                   with next = next}
                   with tusing = tusing}
                   with ty = tyTm next}
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
              with ty = tyTm inexpr}
end


lang NamedPatTypeCheck = PatTypeCheck + NamedPat
  sem typeCheckPat (env : TCEnv) =
  | PatNamed t ->
    let patTy = newvar env.currentLvl t.info in
    let env =
      match t.ident with PName n then
        _insertVar n patTy env
      else env
    in
    (env, PatNamed {t with ty = patTy})
end

lang SeqTotPatTypeCheck = PatTypeCheck + SeqTotPat
  sem typeCheckPat (env : TCEnv) =
  | PatSeqTot t ->
    let elemTy = newvar env.currentLvl t.info in
    match mapAccumL typeCheckPat env t.pats with (env, pats) then
      iter (compose (unify elemTy) tyPat) pats;
      (env, PatSeqTot {{t with pats = pats}
                          with ty = ityseq_ t.info elemTy})
    else never
end

lang SeqEdgePatTypeCheck = PatTypeCheck + SeqEdgePat
  sem typeCheckPat (env : TCEnv) =
  | PatSeqEdge t ->
    let elemTy = newvar env.currentLvl t.info in
    let seqTy = ityseq_ t.info elemTy in
    let unifyPat = compose (unify elemTy) tyPat in
    match mapAccumL typeCheckPat env t.prefix with (env, prefix) then
      iter unifyPat prefix;
      match mapAccumL typeCheckPat env t.postfix with (env, postfix) then
        iter unifyPat postfix;
        let env =
          match t.middle with PName n then _insertVar n seqTy env
          else env
        in
        (env, PatSeqEdge {{{t with prefix = prefix}
                              with postfix = postfix}
                              with ty = seqTy})
      else never
    else never
end

lang IntPatTypeCheck = PatTypeCheck + IntPat
  sem typeCheckPat (env : TCEnv) =
  | PatInt t -> (env, PatInt {t with ty = TyInt {info = t.info}})
end

lang CharPatTypeCheck = PatTypeCheck + CharPat
  sem typeCheckPat (env : TCEnv) =
  | PatChar t -> (env, PatChar {t with ty = TyChar {info = t.info}})
end

lang BoolPatTypeCheck = PatTypeCheck + BoolPat
  sem typeCheckPat (env : TCEnv) =
  | PatBool t -> (env, PatBool {t with ty = TyBool {info = t.info}})
end

lang AndPatTypeCheck = PatTypeCheck + AndPat
  sem typeCheckPat (env : TCEnv) =
  | PatAnd t ->
    match typeCheckPat env t.lpat with (env, lpat) then
      match typeCheckPat env t.rpat with (env, rpat) then
        unify (tyPat lpat) (tyPat rpat);
        (env, PatAnd {{{t with lpat = lpat} with rpat = rpat} with ty = tyPat lpat})
      else never
    else never
end

lang OrPatTypeCheck = PatTypeCheck + OrPat
  sem typeCheckPat (env : TCEnv) =
  | PatOr t ->
    match typeCheckPat env t.lpat with (env, lpat) then
      match typeCheckPat env t.rpat with (env, rpat) then
        unify (tyPat lpat) (tyPat rpat);
        (env, PatOr {{{t with lpat = lpat} with rpat = rpat} with ty = tyPat lpat})
      else never
    else never
end

lang NotPatTypeCheck = PatTypeCheck + NotPat
  sem typeCheckPat (env : TCEnv) =
  | PatNot t ->
    match typeCheckPat env t.subpat with (env, subpat) then
      (env, PatNot {{t with subpat = subpat} with ty = tyPat subpat})
    else never
end

lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FlexTypeUnify + FunTypeUnify + AllTypeUnify + SeqTypeUnify +
  BoolTypeUnify + IntTypeUnify + FloatTypeUnify + CharTypeUnify +
  UnknownTypeUnify + TensorTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FlexTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck + RecLetsTypeCheck +
  MatchTypeCheck + ConstTypeCheck + SeqTypeCheck + UtestTypeCheck +
  NeverTypeCheck + ExtTypeCheck +

  -- Patterns
  NamedPatTypeCheck + SeqTotPatTypeCheck + SeqEdgePatTypeCheck +
  IntPatTypeCheck + CharPatTypeCheck + BoolPatTypeCheck +
  AndPatTypeCheck + OrPatTypeCheck + NotPatTypeCheck

end

lang TestLang = MExprTypeCheck + MExprEq end

mexpr

use TestLang in

let gen_  = lam tm. bind_ (ulet_ "x" tm) (freeze_ (var_ "x")) in
let inst_ = lam tm. bind_ (ulet_ "x" tm) (var_ "x") in

let a = tyvar_ "a" in
let b = tyvar_ "b" in
let fa = tyflexunbound_ "a" in
let fb = tyflexunbound_ "b" in

let tychoose_ = tyall_ "a" (tyarrows_ [a, a, a]) in
let choose_ = ("choose", tychoose_) in

let idbody_ = ulam_ "y" (var_ "y") in
let tyid_ = tyall_ "a" (tyarrow_ a a) in
let id_ = ("id", tyid_) in

let idsbody_ = bind_ id_ (seq_ [freeze_ (var_ "id")]) in
let tyids_ = tyseq_ tyid_ in
let ids_ = ("ids", tyids_) in

let autobody_ = lam_ "x" tyid_ (app_ (var_ "x") (freeze_ (var_ "x"))) in
let tyauto_ = tyarrow_ tyid_ tyid_ in
let auto_ = ("auto", tyauto_) in

let auto1body_ = lam_ "x" tyid_ (app_ (var_ "x") (var_ "x")) in
let tyauto1_ = tyall_ "b" (tyarrows_ [tyid_, b, b]) in
let auto1_ = ("auto1", tyauto1_) in

let polybody_ = lam_ "f" tyid_ (utuple_ [app_ (var_ "f") (int_ 1), app_ (var_ "f") true_]) in
let typoly_ = tyarrow_ tyid_ (tytuple_ [tyint_, tybool_]) in
let poly_ = ("poly", typoly_) in

type TypeTest = {
  -- Name of the test case, for documentation purposes
  name : String,
  -- The term to typecheck
  tm : Expr,
  -- Its expected type
  ty : Type,
  -- Environment assigning types to functions like id, choose, et.c.
  env : [(String, Type)]
}
in

let typeOf = lam test : TypeTest.
  let env = foldr (lam n : (String, Type).
    mapInsert (nameNoSym n.0) n.1) (mapEmpty nameCmp) test.env in
  tyTm (typeCheckBase {_tcEnvEmpty with varEnv = env} test.tm)
in

let runTest =
  lam test : TypeTest.
  -- Make sure to print the test name if the test fails.
  let eqTypeTest = lam a : Type. lam b : Type.
    if eqType a b then true
    else print (join ["\n ** Type test FAILED: ", test.name, " **"]); false
  in
  utest typeOf test with test.ty using eqTypeTest in ()
in

let tests = [

  -- Examples from the paper
  -- A : Polymorphic Instantiation
  {name = "A1",
   tm = ulam_ "x" idbody_,
   ty = tyarrows_ [fa, fb, fb],
   env = []},

  {name = "A1o",
   tm = gen_ (ulam_ "x" idbody_),
   ty = tyalls_ ["a", "b"] (tyarrows_ [a, b, b]),
   env = []},

  {name = "A2",
   tm = app_ (var_ "choose") (var_ "id"),
   ty = tyarrows_ [tyarrow_ fa fa, fa, fa],
   env = [choose_, id_]},

  {name = "A2o",
   tm = app_ (var_ "choose") (freeze_ (var_ "id")),
   ty = tyauto_,
   env = [choose_, id_]},

  {name = "A3",
   tm = appf2_ (var_ "choose") empty_ (var_ "ids"),
   ty = tyids_,
   env = [choose_, ids_]},

  {name = "A4",
   tm = auto1body_,
   ty = tyarrows_ [tyid_, fb, fb],
   env = []},

  {name = "A4o",
   tm = autobody_,
   ty = tyauto_,
   env = []},

  {name = "A5",
   tm = app_ (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [id_, auto_]},

  {name = "A6",
   tm = app_ (var_ "id") (var_ "auto1"),
   ty = tyarrows_ [tyid_, fb, fb],
   env = [id_, auto1_]},

  {name = "A6o",
   tm = app_ (var_ "id") (freeze_ (var_ "auto1")),
   ty = tyauto1_,
   env = [id_, auto1_]},

  {name = "A7",
   tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [choose_, id_, auto_]},

  -- We can't handle negative tests yet, since the type checker errors on failure
  -- {name = "A8",
  --  tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto1"),
  --  ty = fails,
  --  env = [choose_, id_, auto1_]}

  {name = "A9*",
   tm = appf2_ (var_ "f") (app_ (var_ "choose") (freeze_ (var_ "id"))) (var_ "ids"),
   ty = tyid_,
   env = [
     choose_,
     id_,
     ids_,
     ("f", tyall_ "a" (tyarrows_ [tyarrow_ a a, tyseq_ a, a]))
   ]},

  {name = "A10*",
   tm = app_ (var_ "poly") (freeze_ (var_ "id")),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  {name = "A11*",
   tm = app_ (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_]},

  {name = "A12*",
   tm = appf2_ (var_ "id") (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  -- TODO(aathn, 2021-10-02): Add remaining tests from the paper
  -- B : Inference with Polymorphic Arguments
  -- C : Functions on Polymorphic Lists
  -- D : Application Functions
  -- E : Eta-Expansion
  -- F : FreezeML Programs

  -- Other tests
  {name = "RecLets1",
   tm = bindall_ [
     ureclets_ [
       ("x", ulam_ "n" (app_ (var_ "y") false_)),
       ("y", ulam_ "n" (app_ (var_ "x") false_))
     ],
     var_ "x"
   ],
   ty = tyarrow_ tybool_ fa,
   env = []},

  {name = "RecLets2",
   tm = bindall_ [
     ureclets_ [
       ("even", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           true_
           (app_ (var_ "odd") (subi_ (var_ "n") (int_ 1))))),
       ("odd", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           false_
           (app_ (var_ "even") (subi_ (var_ "n") (int_ 1)))))
     ],
     var_ "even"
   ],
   ty = tyarrow_ tyint_ tybool_,
   env = []},

  {name = "Match1",
   tm = if_ true_ (int_ 1) (int_ 0),
   ty = tyint_,
   env = []},

  {name = "Match2",
   tm = ulam_ "x"
     (match_ (var_ "x") (pvar_ "y") (addi_ (var_ "y") (int_ 1)) (int_ 0)),
   ty = tyarrow_ tyint_ tyint_,
   env = []},

  {name = "Match3",
   tm = match_
     (seq_ [str_ "a", str_ "b", str_ "c", str_ "d"])
     (pseqedge_ [pseqtot_ [pchar_ 'a']] "mid" [pseqtot_ [pchar_ 'd']])
     (var_ "mid")
     never_,
   ty = tyseq_ tystr_,
   env = []},

  {name = "Const1",
   tm = addi_ (int_ 5) (int_ 2),
   ty = tyint_,
   env = []},

  {name = "Const2",
   tm = cons_ (int_ 0) empty_,
   ty = tyseq_ tyint_,
   env = []},

  {name = "Const3",
   tm = ulam_ "x" (int_ 0),
   ty = tyarrow_ fa tyint_,
   env = []},

  {name = "Seq1",
   tm = seq_ [],
   ty = tyseq_ fa,
   env = []},

  {name = "Seq2",
   tm = seq_ [int_ 1, int_ 2],
   ty = tyseq_ tyint_,
   env = []},

  {name = "Seq3",
   tm = seq_ [seq_ [int_ 1, int_ 2],
              seq_ [int_ 3, int_ 4]],
   ty = tyseq_ (tyseq_ tyint_),
   env = []},

  {name = "Utest1",
   tm = utest_ (int_ 1) (addi_ (int_ 0) (int_ 1)) false_,
   ty = tybool_,
   env = []},

  {name = "Utest2",
   tm = utestu_ (int_ 1) true_ false_ (ulam_ "x" idbody_),
   ty = tybool_,
   env = []},

  {name = "Never1",
   tm = never_,
   ty = fa,
   env = []}

]
in

iter runTest tests;

()

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure

-- TODO(aathn, 2021-09-28): Value restriction

-- TODO(aathn, 2021-09-28): Type check remaining terms
