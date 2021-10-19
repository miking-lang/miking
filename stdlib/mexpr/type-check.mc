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
  sem checkBeforeUnify (tv : TVarRec) =
  | ty ->
    sfold_Type_Type (lam. lam ty. checkBeforeUnify tv ty) () ty
end

lang VarTypeUnify = Unify + VarTypeAst + UnknownTypeAst
  sem unifyBase (names : BiNameMap) =
  -- We don't unify variables with TyUnknown
  | (TyFlex {contents = r}, !TyUnknown _ & ty1)
  | (!TyUnknown _ & ty1, TyFlex {contents = r}) ->
    match deref r with Unbound tv then
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
    unifyWithNames names (from1, from2);
    unifyWithNames names (to1, to2)
end

lang AllTypeUnify = Unify + AllTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyAll t1, TyAll t2) ->
    unifyWithNames (biInsert (t1.ident, t2.ident) names) (t1.ty, t2.ty)

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

lang UnknownTypeUnify = Unify + UnknownTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TyUnknown _, _)
  | (_, TyUnknown _) ->
    ()
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase (names : BiNameMap) =
  | (TySeq t1, TySeq t2) ->
    unifyWithNames names (t1.ty, t2.ty)
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
    let tyX =
      match t.tyIdent with TyUnknown _ then
        -- No type annotation: assign a monomorphic type variable to x.
        newvarWeak env.currentLvl t.info
      else
        -- Type annotation: assign x its annotated type.
        t.tyIdent
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
    unify (tyTm lhs, tyarrow_ (tyTm rhs) tyRes);
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
        gen lvl (tyTm body)
      else
        -- Type annotation: unify the annotated type with the inferred one
        match stripTyAll t.tyBody with (_, tyAnnot) then
          unify (tyAnnot, tyTm body);
          t.tyBody
        else never
    in
    let inexpr = typeCheckBase (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {{{t with body = body}
               with inexpr = inexpr}
               with ty = tyTm inexpr}
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
    iter (lam tm. unify (elemTy, tyTm tm)) tms;
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
       unify (tyTm tu) (tyarrows_ [tyTm test, tyTm expected, tybool_])
     else
       unify (tyTm test) (tyTm expected));
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


lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FunTypeUnify + AllTypeUnify + SeqTypeUnify +
  UnknownTypeUnify +

  -- Type generalization
  VarTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck +
  ConstTypeCheck + SeqTypeCheck + UtestTypeCheck + NeverTypeCheck +
  ExtTypeCheck

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
   env = [poly_, id_]}

  -- TODO(aathn, 2021-10-02): Add remaining tests from the paper
  -- B : Inference with Polymorphic Arguments
  -- C : Functions on Polymorphic Lists
  -- D : Application Functions
  -- E : Eta-Expansion
  -- F : FreezeML Programs

]
in

iter runTest tests;

()

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure

-- TODO(aathn, 2021-09-28): Value restriction

-- TODO(aathn, 2021-09-28): Type check remaining terms
