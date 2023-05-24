-- Defines the transformation of specialize terms.

include "peval/ast.mc"
include "peval/lift.mc"
include "peval/extract.mc"
include "peval/include.mc"

include "map.mc"
include "name.mc"
include "seq.mc"
include "error.mc"
include "set.mc"

include "mexpr/ast.mc"
include "mexpr/lamlift.mc"
include "mexpr/shallow-patterns.mc"


lang SpecializeCompile = SpecializeAst + MExprPEval + MExprAst + SpecializeInclude +
                    SpecializeLiftMExpr + MExprLambdaLift + SpecializeExtract +
                    MExprLowerNestedPatterns 

  sem createSpecExpr : Expr -> Expr -> Expr
  sem createSpecExpr deps =
  | TmLam {body = b} -> createSpecExpr deps b
  | t -> bind_ deps t

  sem updateBody : Expr -> Expr -> Expr
  sem updateBody e =
  | TmLam t -> smap_Expr_Expr (updateBody e) (TmLam t)
  | t -> e

  sem rmCopy : Name -> Expr -> Expr
  sem rmCopy rm =
  | TmLet t ->
    if nameEq t.ident rm then
      t.inexpr
    else smap_Expr_Expr (rmCopy rm) (TmLet t)
  | t -> smap_Expr_Expr (rmCopy rm) t

  sem specializePass : SpecializeNames -> SpecializeArgs -> Map Name Name ->
                  Expr -> (Map Name Name, Expr)
  sem specializePass pnames args idMap =
  | TmLet t ->
    match mapLookup t.ident args.extractMap with Some e then
      -- Remove the copy of this let binding in the extracted bindings
      let e = rmCopy t.ident e in
      -- Bind the dependencies to the thing we want to specialize, disregarding
      -- any outer lambdas, i.e. with specialize (lam x. addi x y)
      -- we will only look at addi x y
      let toSpec = createSpecExpr e t.body in

      let toSpec = lowerAll toSpec in

      -- Update the map of names that have been bound already
      let args = updateIds args idMap in

      -- TODO: extractMap in args is useless for lift, maybe exclude

      -- The environment holds the free variables of the expression to spec.
      match getLiftedEnv pnames args toSpec with (args, pevalEnv) in
      match liftExpr pnames args toSpec with (args, pevalArg) in
      match liftName pnames args (nameSym "residualID") with (args, id) in

      let jitCompile = nvar_ (jitName pnames) in
      let placeHolderPprint = nvar_ (nameMapName pnames) in
      let jitCompile = appf2_ jitCompile id placeHolderPprint in
      let pevalFunc = nvar_ (pevalName pnames) in
      let residual = appf2_ pevalFunc pevalEnv pevalArg in
      let compiledResidual = app_ jitCompile residual in
      let newBody = updateBody compiledResidual t.body in
      (args.idMapping, TmLet {t with body = newBody})
    else smapAccumL_Expr_Expr (specializePass pnames args) idMap (TmLet t)
  | t -> smapAccumL_Expr_Expr (specializePass pnames args) idMap t

  sem hasSpecializeTerm : Bool -> Expr -> Bool
  sem hasSpecializeTerm acc =
  | TmSpecialize _ -> true
  | t -> or acc (sfold_Expr_Expr hasSpecializeTerm acc t)

  sem updatePprintPH : SpecializeNames -> Map Name Name -> Map Name String ->
                       Expr -> (Map Name String, Expr)
  sem updatePprintPH names idMap nameMap =
  | TmLet t ->
    if nameEq t.ident (nameMapName names) then
      -- IdMap : ActualName -> GeneratedName
      --       : NameInProgram.ml -> NameInPlugin.ml
      -- ActualName and GeneratedName should be pprinted to same string
      -- Here, we create the strings for those names explicitly
      let stringName = lam acName.
       join ["specialize_", nameGetStr acName
       , "\'"
       , (int2string (sym2hash (optionGetOrElse
                                 (lam. error "Expected symbol")
                                 (nameGetSym acName))))] in

      -- Create Expr of nameMap (used in plugins)
      let kvSeq = mapFoldWithKey (lam l. lam acName. lam genName.
         let name = utuple_ [str_ acName.0, nvar_ genName] in
         snoc l (utuple_ [name, str_ (stringName acName)])) [] idMap in
      let mfs = nvar_ (mapFromSeqName names) in
      let ncmp = nvar_ (nameCmpName names) in
      let nameMapExpr = appf2_ mfs ncmp (seq_ kvSeq) in

      -- Create actual nameMap (used in actual program)
      let nameMap = mapFoldWithKey (lam m. lam acName. lam genName.
        mapInsert acName (stringName acName) m) (mapEmpty nameCmp) idMap in

      (nameMap, TmLet {t with body=nameMapExpr})
    else
      smapAccumL_Expr_Expr (updatePprintPH names idMap) nameMap (TmLet t)
  | t ->
      smapAccumL_Expr_Expr (updatePprintPH names idMap) nameMap t

  sem compileSpecialize =
  | ast ->
    if not (hasSpecializeTerm false ast) then (false, (mapEmpty nameCmp), ast)
    else
    match addIdentifierToSpecializeTerms ast with (specializeData, ast) in
    match liftLambdasWithSolutions ast with (solutions, ast) in

    let specializeIds : [Name] = mapKeys specializeData in

    let extractMap : Map Name Expr = extractSeparate specializeIds ast in

    -- Bulk of the time taken
    match includeSpecializeDeps ast with (ast, nameMapName) in
    -- Find the names of the functions and constructors needed later
    let names = createNames ast nameMapName in

    let args = initArgs extractMap in
    match specializePass names args (mapEmpty nameCmp) ast
    with (idMapping, ast) in

    let ast = if gti (mapLength idMapping) 0 then
      let symDefs = bindall_ (map (lam n:Name. nulet_ n (gensym_ uunit_))
                  (mapValues idMapping)) in
      bindall_ [
          symDefs,
          ast]
    else ast in
    match updatePprintPH names idMapping (mapEmpty nameCmp) ast
      with (nameMap, ast) in
    (true, nameMap, ast)
end


lang TestLang = SpecializeCompile + MExprEq + MExprSym + MExprTypeCheck
                + MExprPrettyPrint
end

mexpr
use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in


--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  specialize_ (app_ (var_ "f") (int_ 1))
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  ulam_ "x" (bindall_ [
--    ulet_ "k" (addi_ (var_ "x") (var_ "x")),
--    ulet_ "q" (specialize_ (var_ "k")),
--    var_ "k"
--    ])
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--    ulet_ "f" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
--    ulet_ "p" (ulam_ "x" (specialize_ (app_ (var_ "f") (var_ "x")))),
--    app_ (var_ "p") (int_ 4)
--]) in


-- TyInt
let unknownTyInt = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyint_ (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (int_ 4)),
    app_ (var_ "p") (int_ 12)
]) in

-- TyFloat
let unknownTyFloat = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyfloat_ (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (float_ 4.0)),
    unit_
]) in

-- TyBool
let unknownTyBool = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tybool_ (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (bool_ false)),
    unit_
]) in

-- TyChar
let unknownTyChar = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tychar_ (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (char_ 'x')),
    unit_
]) in

-- TySeq
let intseq = tyseq_ tyint_ in
let unknownTySeq = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" intseq (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (seq_ [int_ 1, int_ 2])),
    unit_
]) in

-- TyRec
let t = tyrecord_ [("a", tyint_), ("b", tyint_)] in
let unknownTyRec = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (urecord_ [("a",int_ 1), ("b", int_ 3)]))
]) in

-- TyRec with one unliftable field

let t = tyrecord_ [("a", tyint_), ("b", tyunknown_)] in
let unknownTyRecUnknown = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (urecord_ [("a",int_ 1), ("b", int_ 3)]))
]) in

-- TyArrow

let t = tyarrow_ (tyint_) (tyint_) in
let unknownTyArrow = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (specialize_ (var_ "x"))),
    ulet_ "id" (lam_ "x" (tyint_) (var_ "x")),
    ulet_ "k" (app_ (var_ "p") (var_ "id"))
]) in

let recursiveThing = preprocess (bindall_ [
    (ureclets_
       [("odd",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 1))
              true_
              (if_ (lti_ (var_ "x") (int_ 1))
                 false_
                 (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))),

        ("even",
         ulam_ "x"
           (if_ (eqi_ (var_ "x") (int_ 0))
              true_
              (if_ (lti_ (var_ "x") (int_ 0))
                 false_
                 (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1))))))]),
    ulet_ "ra" (specialize_ (app_ (var_ "odd") (int_ 4)))]) in

let e = match_ (int_ 3) (pvar_ "wo") (int_ 5) (int_ 6) in
let e = bind_ (ulet_ "x" (int_ 3)) (addi_ (int_ 4) (var_ "x")) in
let distinctCalls = preprocess (bindall_ [
    ulet_ "k" (specialize_ (e))
]) in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  specialize_ (app_ (var_ "f") (int_ 1))
]) in

let distinctCalls = preprocess (bindall_ [
    ulet_ "f" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
    ulet_ "p" (ulam_ "x" (
        specialize_ (app_ (var_ "f") (var_ "x")))),
    app_ (var_ "p") (int_ 4)
]) in

match compileSpecialize unknownTyRecUnknown with (_, _, ast) in

()
