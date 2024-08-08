-- Defines a language fragment for determining whether a given MExpr expression
-- may contain side-effects or if it does not. The recommended use is:
--  1. Pass the full expression to 'constructSideEffectEnv' to construct a
--     global side-effect environment.
--  2. Use this environment in 'exprHasSideEffect' to check whether a given
--     expression, which is a subexpression of the expression used in step 1, has
--     a side-effect.
--
-- If an expression only uses variables that are known to have no side-effect
-- and that have arity 0, the 'hasSideEffect' function can be used directly.

include "set.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/call-graph.mc"
include "mexpr/const-arity.mc"

type SideEffectEnv = {
  -- A set containing the identifiers that are considered to have
  -- side-effects.
  sideEffectId : Set Name,

  -- Maps identifiers to their arity. An identifier not in this map is
  -- assumed to have arity 0.
  arityId : Map Name Int
}

lang SideEffect = Ast
  sem sideEffectEnvEmpty =
  | () -> {sideEffectId = setEmpty nameCmp, arityId = mapEmpty nameCmp}

  sem updateSideEffectEnv (env : SideEffectEnv) (id : Name) (arity : Int) =
  | se ->
    let env =
      if neqi arity 0 then {env with arityId = mapInsert id arity env.arityId}
      else env in
    if se then {env with sideEffectId = setInsert id env.sideEffectId} else env

  sem identHasSideEffects (env : SideEffectEnv) =
  | id -> setMem id env.sideEffectId

  sem identArity (env : SideEffectEnv) =
  | id ->
    optionGetOrElse
      (lam. 0)
      (mapLookup id env.arityId)

  sem exprHasSideEffectH : SideEffectEnv -> Bool -> Bool -> Expr -> Bool

  sem exprHasSideEffect : SideEffectEnv -> Expr -> Bool
  sem exprHasSideEffect env =
  | t -> exprHasSideEffectH env true false t

  sem hasSideEffect : Expr -> Bool
  sem hasSideEffect =
  | t -> exprHasSideEffect (sideEffectEnvEmpty ()) t
end

lang ConstSideEffectBase = ConstAst
  sem constHasSideEffect : Const -> Bool
end

lang ConstSideEffect = ConstSideEffectBase + MExprAst
  sem constHasSideEffect =
  | CInt _ | CFloat _ | CBool _ | CChar _ -> false
  | CAddi _ | CSubi _ | CMuli _ | CDivi _ | CNegi _ | CModi _ -> false
  | CSlli _ | CSrli _ | CSrai _ -> false
  | CAddf _ | CSubf _ | CMulf _ | CDivf _ | CNegf _ -> false
  | CFloorfi _ | CCeilfi _ | CRoundfi _ | CInt2float _ -> false
  | CEqi _ | CNeqi _ | CLti _ | CGti _ | CLeqi _ | CGeqi _ -> false
  | CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _ -> false
  | CEqc _ -> false
  | CInt2Char _ | CChar2Int _ -> false
  | CStringIsFloat _ | CString2float _ | CFloat2string _ -> false
  | CSymb _ | CGensym _ | CSym2hash _ -> true
  | CEqsym _ -> true
  | CSet _ | CGet _ | CCons _ | CSnoc _ | CConcat _ | CLength _ | CReverse _
  | CHead _ | CTail _ | CNull _ | CMap _ | CMapi _ | CIter _ | CIteri _
  | CFoldl _ | CFoldr _ | CCreate _ | CCreateList _ | CCreateRope _
  | CSplitAt _ | CSubsequence _ -> false
  | CFileRead _ | CFileWrite _ | CFileExists _ | CFileDelete _ -> true
  | CPrint _ | CPrintError _ | CDPrint _ | CFlushStdout _ | CFlushStderr _
  | CReadLine _ | CReadBytesAsString _ -> true
  | CRandIntU _ | CRandSetSeed _ -> true
  | CExit _ | CError _ | CArgv _ | CCommand _ -> true
  | CWallTimeMs _ | CSleepMs _ -> true
  | CConstructorTag _ -> true
  | CRef _ | CModRef _ | CDeRef _ -> true
  | CTensorCreateInt _ | CTensorCreateFloat _ | CTensorCreate _
  | CTensorGetExn _ | CTensorSetExn _
  | CTensorLinearGetExn _ | CTensorLinearSetExn _
  | CTensorRank _ | CTensorShape _
  | CTensorReshapeExn _ | CTensorCopy _ | CTensorTransposeExn _
  | CTensorSliceExn _ | CTensorSubExn _ | CTensorIterSlice _ |  CTensorEq _
  | CTensorToString _ -> true
  | CBootParserParseMExprString _ | CBootParserParseMCoreFile _ | CBootParserParseMLangFile _
  | CBootParserParseMLangString _ | CBootParserGetTop _ | CBootParserGetDecl _
  | CBootParserGetId _ | CBootParserGetTerm _ | CBootParserGetType _
  | CBootParserGetString _ | CBootParserGetInt _ | CBootParserGetFloat _
  | CBootParserGetListLength _ | CBootParserGetConst _ | CBootParserGetPat _
  | CBootParserGetInfo _ -> true
end

lang MExprSideEffect =
  SideEffect + ConstSideEffect + MExprAst + MExprArity + MExprCallGraph

  sem exprHasSideEffectH env lambdaCounting acc =
  | TmVar t ->
    if acc then true
    else if and lambdaCounting (geqi (identArity env t.ident) 1) then false
    else identHasSideEffects env t.ident
  | TmApp t ->
    if acc then true
    else if exprHasSideEffectH env lambdaCounting false t.rhs then true
    else if lambdaCounting then
      let larity = exprArity env t.lhs in
      if leqi larity 1 then
        -- NOTE(larshum, 2022-02-01): If we find that the left-hand side has
        -- arity at most 1, we check whether the left-hand side argument
        -- contains side-effects while ignoring the lambda count.
        exprHasSideEffectH env false false t.lhs
      else false
    else exprHasSideEffectH env lambdaCounting false t.lhs
  | TmLam t ->
    if acc then true
    else if lambdaCounting then false
    else exprHasSideEffectH env lambdaCounting false t.body
  | TmConst t -> if acc then true else constHasSideEffect t.val
  | t -> if acc then true else sfold_Expr_Expr (exprHasSideEffectH env lambdaCounting) false t

  sem exprArity (env : SideEffectEnv) =
  | TmVar t -> identArity env t.ident
  | TmApp t -> subi (exprArity env t.lhs) 1
  | TmLam t -> addi (exprArity env t.body) 1
  | TmConst t -> constArity t.val

  -- Constructs a SideEffectEnv from a given expression 't', which can be used
  -- to determine whether any subexpression of 't' contains a side-effect.
  sem constructSideEffectEnv =
  | t -> constructSideEffectEnvH (sideEffectEnvEmpty ()) t

  sem constructSideEffectEnvH (env : SideEffectEnv) =
  | TmLet t ->
    let bodySideEffect = exprHasSideEffectH env false false t.body in
    let lambdaCount = countArityExpr 0 t.body in
    let env = updateSideEffectEnv env t.ident lambdaCount bodySideEffect in
    let env = constructSideEffectEnvH env t.body in
    constructSideEffectEnvH env t.inexpr
  | TmRecLets t ->
    -- NOTE(larshum, 2022-02-01): The call graph implementation stores bindings
    -- by name, not index, so we need to use a map for binding lookup.
    let bindMap : Map Name RecLetBinding =
      mapFromSeq nameCmp
        (map (lam bind : RecLetBinding. (bind.ident, bind)) t.bindings) in
    let sideEffectsScc = lam env : SideEffectEnv. lam scc : [Name].
      let sccBindings : [RecLetBinding] =
        foldl
          (lam acc. lam id. optionMapOr acc (snoc acc) (mapLookup id bindMap))
          []
          scc
      in
      -- Determine whether the body of any binding within this strongly
      -- connected component contains side-effects. If we find any side-effect,
      -- we know they must all contain a side-effect as they can be called from
      -- each other.
      let sccHasSideEffect =
        foldl
          (lam acc : Bool. lam bind : RecLetBinding.
            exprHasSideEffectH env false acc bind.body)
          false sccBindings in
      -- Update the entries for all the bindings in this SCC.
      foldl
        (lam env : SideEffectEnv. lam bind : RecLetBinding.
          let lambdaCount = countArityExpr 0 bind.body in
          updateSideEffectEnv env bind.ident lambdaCount sccHasSideEffect)
      env sccBindings in
    let g : Digraph Name Int = constructCallGraph (TmRecLets t) in
    let sccs = digraphTarjan g in
    let env = foldl sideEffectsScc env (reverse sccs) in
    let env =
      foldl
        (lam env : SideEffectEnv. lam bind : RecLetBinding.
          constructSideEffectEnvH env bind.body)
        env t.bindings in
    constructSideEffectEnvH env t.inexpr
  | TmExt t ->
    let lambdaCount = countArityType 0 t.tyIdent in
    let env = updateSideEffectEnv env t.ident lambdaCount t.effect in
    constructSideEffectEnvH env t.inexpr
  | t -> sfold_Expr_Expr constructSideEffectEnvH env t

  sem countArityExpr (count : Int) =
  | TmLam t -> countArityExpr (addi count 1) t.body
  | _ -> count

  sem countArityType (count : Int) =
  | TyArrow t -> countArityType (addi count 1) t.to
  | _ -> count
end

mexpr

use MExprSideEffect in

let x = nameSym "x" in
utest hasSideEffect (int_ 2) with false in
utest hasSideEffect (addf_ (float_ 2.0) (float_ 3.0)) with false in
utest hasSideEffect (nulam_ x (addi_ (nvar_ x) (int_ 1))) with false in
utest hasSideEffect (nulam_ x (wallTimeMs_ (nvar_ x))) with false in
utest hasSideEffect (app_ (nulam_ x (wallTimeMs_ (nvar_ x))) (float_ 1.0)) with true in

let env1 = sideEffectEnvEmpty () in
let env2 = updateSideEffectEnv env1 x 0 true in
utest exprHasSideEffect env1 (nvar_ x) with false in
utest exprHasSideEffect env2 (nvar_ x) with true in

let eqArityEntry = lam a : (Name, Int). lam b : (Name, Int).
  if nameEq a.0 b.0 then
    eqi a.1 b.1
  else false
in

let a = nameSym "a" in
let b = nameSym "b" in
let c = nameSym "c" in
let x = nameSym "x" in
let y = nameSym "y" in
let bindings = bindall_ [
  nulet_ a (ref_ (int_ 2)),
  nulet_ b (nulam_ x (addi_ (nvar_ x) (deref_ (nvar_ x)))),
  nulet_ c (nulam_ x (nulam_ y (addi_ (nvar_ x) (nvar_ y)))),
  appf2_ (nvar_ c) (int_ 2) (app_ (nvar_ b) (int_ 3))] in
let env : SideEffectEnv = constructSideEffectEnv bindings in
match env with {sideEffectId = sideEffectId, arityId = arityId} in
utest setToSeq sideEffectId with [a, b] using eqSeq nameEq in
utest mapToSeq arityId with [(b, 1), (c, 2)] using eqSeq eqArityEntry in
utest exprHasSideEffect env (nvar_ a) with true in
utest exprHasSideEffect env (nvar_ b) with false in
utest exprHasSideEffect env (nvar_ c) with false in
utest exprHasSideEffect env (addi_ (nvar_ b) (int_ 1)) with true in
utest exprHasSideEffect env (nulam_ x (addi_ (nvar_ b) (nvar_ x))) with false in

let d = nameSym "d" in
let z = nameSym "z" in
let reclets = bindall_ [
  nureclets_ [
    (a, nulam_ x (muli_ (nvar_ x) (int_ 2))),
    (b, nulam_ x (addi_ (app_ (nvar_ a) (int_ 3)) (app_ (nvar_ c) (nvar_ x)))),
    (c, nulam_ x (bind_ (nulet_ d (wallTimeMs_ (nvar_ x))) (app_ (nvar_ b) (int_ 2))))],
  nulet_ y (app_ (nvar_ b) (int_ 3)),
  nulet_ z (app_ (nvar_ a) (int_ 2)),
  int_ 0] in
let env : SideEffectEnv = constructSideEffectEnv reclets in
match env with {sideEffectId = sideEffectId, arityId = arityId} in
utest setToSeq sideEffectId with [b, c, y, d] using eqSeq nameEq in
utest mapToSeq arityId with [(a, 1), (b, 1), (c, 1)] using eqSeq eqArityEntry in
utest exprHasSideEffect env (addi_ (int_ 3) (nvar_ y)) with true in
utest exprHasSideEffect env (addi_ (int_ 3) (nvar_ z)) with false in

let exts = bindall_ [
  next_ a false (tyarrow_ tyint_ tyint_),
  next_ b true (tyarrow_ tyint_ tyint_),
  nulet_ x (app_ (nvar_ a) (int_ 4)),
  nulet_ y (app_ (nvar_ b) (int_ 3)),
  addi_ (nvar_ x) (nvar_ y)] in
let env : SideEffectEnv = constructSideEffectEnv exts in
match env with {sideEffectId = sideEffectId, arityId = arityId} in
utest setToSeq sideEffectId with [b, y] using eqSeq nameEq in
utest mapToSeq arityId with [(a, 1), (b, 1)] using eqSeq eqArityEntry in
utest exprHasSideEffect env (addi_ (nvar_ x) (nvar_ y)) with true in

let t = bind_
  (nulet_ a (nulam_ x
    (bind_
      (nulet_ b (nulam_ y (deref_ (nvar_ y))))
      (nvar_ x))))
  (app_ (nvar_ a) (ref_ (int_ 2))) in
let env : SideEffectEnv = constructSideEffectEnv t in
match env with {sideEffectId = sideEffectId, arityId = arityId} in
utest setToSeq sideEffectId with [a, b] using eqSeq nameEq in
utest mapToSeq arityId with [(a, 1), (b, 1)] using eqSeq eqArityEntry in
utest exprHasSideEffect env (nvar_ b) with false in
utest exprHasSideEffect env (app_ (nvar_ b) (nvar_ x)) with true in
utest exprHasSideEffect env (app_ (nvar_ a) (int_ 2)) with true in
utest exprHasSideEffect env (app_ (nvar_ a) (ref_ (int_ 2))) with true in

()
