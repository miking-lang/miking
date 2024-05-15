include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"
include "./composition-check.mc"

include "mexpr/eval.mc"
include "mexpr/eq.mc"

include "common.mc"
include "option.mc"
include "map.mc"
include "bool.mc"
include "name.mc"
include "set.mc"
include "result.mc"

type CompilationContext = use MLangAst in {
  -- Accumulator of compilation result
  exprs: [Expr],

  compositionCheckEnv : CompositionCheckEnv,

  -- A mapping from syn identifiers to their constructors
  synNameDefMap : Map Name [{ident : Name, tyIdent : Type}],

  -- A map from identifier strings of semantic functions to the 
  -- symbolized names that the function has in different fragments.
  semSymbols : Map String [Name]
}

-- Substitute the identifier stored in a TmVar based on the provided substitution
recursive let subTmVarSymbol = lam subst : (Name -> Name). lam expr. 
  use MExprAst in 
  switch expr
    case TmVar tm then TmVar {tm with ident = subst tm.ident}
    case other then smap_Expr_Expr (subTmVarSymbol subst) other
  end
end

let collectIncludedDefs = lam ctx. lam includes. 
  let getDefs = lam incl : Name. 
    match mapLookup incl ctx.synNameDefMap with Some defs then defs 
    else error "No definitions for included Syntax definition! This is illegal!"
  in 
  join (map getDefs includes)

let _emptyCompilationContext : CompositionCheckEnv -> CompilationContext = lam env : CompositionCheckEnv. {
  exprs = [],
  compositionCheckEnv = env,
  synNameDefMap = mapEmpty nameCmp,
  semSymbols = mapEmpty cmpString
}

let withExpr = lam ctx. lam expr. {ctx with exprs = snoc ctx.exprs expr}

let withSemSymbol = lam ctx : CompilationContext. lam n : Name.
  let s = nameGetStr n in 
  let newValue = match mapLookup s ctx.semSymbols with Some names 
                 then cons n names 
                 else [n]
  in
  {ctx with semSymbols = mapInsert s newValue ctx.semSymbols}

-- Create a substitution function by partially applying the first two elements
-- This substitution function maps symbols belonging to semantic function in 
-- included language fragments to the symbol of the semantic function in the 
-- current fragment
let createSubst = lam semSymbols. lam semNames. lam n. 
  let s = nameGetStr n in 
  match mapLookup s semSymbols with Some xs then
    if optionIsSome (find (lam x. nameEqSym x n) xs) then
      match mapLookup s semNames with Some res then res
      else n
    else
      n
  else 
    n

type CompilationError
con FoundIncludeError : {info : Info, path: String} -> CompilationError

type CompilationWarning

type CompilationResult = Result CompilationWarning CompilationError CompilationContext 

let isTypeDecl = use MLangAst in 
  lam d. match d with DeclType _ then true else false
let isSynDecl = use MLangAst in 
  lam d. match d with DeclSyn _ then true else false
let isSemDecl = use MLangAst in 
  lam d. match d with DeclSem _ then true else false

lang MLangCompiler = MLangAst + MExprAst
  sem compileDecl : CompilationContext -> Decl -> CompilationResult
  sem compileDecl ctx = 
  | DeclLet d -> _ok (
    withExpr ctx (TmLet {ident = d.ident,
                         tyAnnot = d.tyAnnot,
                         tyBody = d.tyBody,
                         body = d.body,
                         info = d.info,
                         ty = tyunknown_,
                         inexpr = uunit_}))
  | DeclRecLets d -> _ok (
    withExpr ctx (TmRecLets {bindings = d.bindings,
                             inexpr = uunit_,
                             ty = tyunknown_,
                             info = d.info}))
  | DeclUtest d -> _ok (
    withExpr ctx (TmUtest {test = d.test,
                           expected = d.expected,
                           next = uunit_,
                           tusing = d.tusing,
                           tonfail = None (),
                           ty = tyunknown_,
                           info = d.info}))
  | DeclType d -> _ok (
    withExpr ctx (TmType {ident = d.ident,
                          params = d.params,
                          tyIdent = d.tyIdent,
                          info = d.info,
                          ty = tyunknown_,
                          inexpr = uunit_}))
  | DeclConDef d -> _ok (
    withExpr ctx (TmConDef {ident = d.ident,
                            tyIdent = d.tyIdent,
                            info = d.info,
                            ty = tyunknown_,
                            inexpr = uunit_}))
  -- TODO(voorberg, 2024-04-23): Add test case for the compilation of externals.
  | DeclExt d -> _ok (
    withExpr ctx (TmExt {ident = d.ident,
                         tyIdent = d.tyIdent,
                         effect = d.effect,
                         info = d.info,
                         ty = tyunknown_,
                         inexpr = uunit_}))
  -- TODO(voorberg, 2024-04-23): Add test case for error on DeclInclude
  | DeclInclude d -> _err (FoundIncludeError {info = d.info, path = d.path})
  | DeclLang l -> 
    let typeDecls = filter isTypeDecl l.decls in 
    let synDecls = filter isSynDecl l.decls in 
    let semDecls = filter isSemDecl l.decls in 

    let nameSeq =  (map (lam s. match s with DeclSem s in (nameGetStr s.ident, s.ident)) semDecls) in 
    let semNames = mapFromSeq cmpString nameSeq in 
    let ctx = foldl withSemSymbol ctx (map (lam s. match s with DeclSem s in s.ident) semDecls) in 

    let res = _foldl compileDecl ctx typeDecls in 
    let res = _bind res (lam ctx. _foldl compileDecl ctx synDecls) in 

    let compileSemToResult : CompilationContext -> [Decl] -> CompilationResult
      = lam ctx. lam sems.
        let bindings = map (compileSem ctx semNames) sems in 
        _ok (withExpr ctx (TmRecLets {bindings = bindings,
                                      inexpr = uunit_, 
                                      ty = tyunknown_,
                                      info = l.info}))
    in
    _bind res (lam ctx. compileSemToResult ctx semDecls)
  | DeclSyn s -> 
    let allDefs = concat s.defs (collectIncludedDefs ctx s.includes) in 

    -- TODO(voorberg, 2024-04-23): Handle includes
    -- NOTE(voorberg, 2024-04-23): We use the info field of the DeclSyn
    --                             for the generated TmConDef.
    let ctx = withExpr ctx (TmType {ident = s.ident,
                                    params = s.params,
                                    tyIdent = tyvariant_ [],
                                    inexpr = uunit_,
                                    ty = tyunknown_,
                                    info = s.info}) in 
    let compileDef = lam ctx. lam def : {ident : Name, tyIdent : Type}.
      _ok (withExpr ctx (TmConDef {ident = def.ident,
                                   tyIdent = def.tyIdent,
                                   inexpr = uunit_,
                                   ty = tyunknown_,
                                   info = s.info}))
    in
    let res = _foldl compileDef ctx allDefs in 
    _map (lam ctx. {ctx with synNameDefMap = mapInsert s.ident allDefs ctx.synNameDefMap}) res
  | DeclSem s -> 
    error "Unexpected DeclSem!"

  sem compileSem : CompilationContext -> Map String Name -> Decl -> RecLetBinding 
  sem compileSem ctx semNames = 
  | DeclSem d -> 
    let subst = createSubst ctx.semSymbols semNames in 
    let targetName = nameSym "target" in 
    let target = nvar_ targetName in 

    -- OPT(voorberg, 23-04-2024): The implementation of compileBody and
    --                            compileArgs can be made tail-recursive.
    recursive 
      let compileBody = lam cases : [{pat : Pat, thn : Expr}]. 
        match cases with [h] ++ t then
          TmMatch {target = target,
                   pat = h.pat,
                   thn = h.thn,
                   els = compileBody t,
                   ty = tyunknown_,
                   info = d.info}
        else (error_ (str_ "Inexhaustive match!"))
    in 
    let cases = match mapLookup d.ident ctx.compositionCheckEnv.semPatMap 
                with Some x then x
                else error "CompositionCheckEnv must contain the ordered cases for all semantic functions!"
    in
    let cases = map (lam c. {c with thn = subTmVarSymbol subst c.thn}) cases in 
    let cases = map (lam c. {thn = c.thn, pat = c.pat}) cases in
    let body = compileBody cases in 
    recursive let compileArgs = lam args. 
          match args with [h] ++ t then
            TmLam {ident = h.ident,
                   tyAnnot = h.tyAnnot,
                   tyParam = tyunknown_,
                   body = compileArgs t,
                   ty = tyunknown_,
                   info = d.info}
          else
            TmLam {ident = targetName,
                   tyAnnot = tyunknown_,
                   tyParam = tyunknown_,
                   body = body,
                   ty = tyunknown_,
                   info = d.info}
    in 
    let result = compileArgs (optionGetOrElse (lam. []) d.args) in 
    {ident = d.ident,
     tyAnnot = d.tyAnnot,
     tyBody = tyunknown_,
     body = result,
     info = d.info}


  sem compileProg : CompilationContext -> MLangProgram -> CompilationResult
  sem compileProg ctx = 
  | prog -> 
    let res = _foldl compileDecl ctx prog.decls in
    _map (lam ctx. withExpr ctx prog.expr) res

  sem compile : CompilationContext -> MLangProgram -> Result CompilationWarning CompilationError Expr
  sem compile ctx =| prog -> 
    match _consume (compileProg ctx prog) with (_, res) in
    switch res
      case Left err then _err (head err)
      case Right ctx then _ok (bindall_ ctx.exprs)
    end
end

lang TestLang = MLangCompiler + MLangSym + MLangCompositionCheck + 
                MExprPrettyPrint + MExprEval + MExprEq end

mexpr
use TestLang in 

let simpleEval = lam e. eval (evalCtxEmpty ()) e in 

let testCompile = lam p. 
  match symbolizeMLang symEnvDefault p with (_, p) in 
  match _consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = _consume (compile ctx p) in 
  match res with (_, rhs) in 
  match rhs with Right expr in expr
in

let testError = lam p. 
  match symbolizeMLang symEnvDefault p with (_, p) in 
  match _consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = _consume (compile ctx p) in 
  match res with (_, rhs) in 
  match rhs with Left errs in errs
in

let testEval = lam p.
  simpleEval (testCompile p)
in 

-- Test simple let binding
let p : MLangProgram = {
    decls = [
        decl_ulet_ "x" (int_ 1)
    ],
    expr = var_ "x"
} in 
utest testEval p with int_ 1 using eqExpr in 

-- Test recursive let bindings through mutually recursive odd/even
let odd = (ulam_ "x" 
  (if_ 
    (eqi_ (var_ "x") (int_ 0))
    (false_)
    (appf1_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
in 
let even = (ulam_ "x" 
  (if_ 
    (eqi_ (var_ "x") (int_ 0))
    (true_)
    (appf1_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
in 
let p : MLangProgram = {
    decls = [
        decl_ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 9)
} in 
utest testEval p with true_ using eqExpr in 
let p : MLangProgram = {
    decls = [
        decl_ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 10)
} in 
utest testEval p with false_ using eqExpr in 

-- Test Utest
let p : MLangProgram = {
    decls = [
        decl_utest_ (int_ 3) (addi_ (int_ 1) (int_ 2))
    ],
    expr = uunit_
} in 
let expected : Expr = utest_ (int_ 3) (addi_ (int_ 1) (int_ 2)) uunit_ in 
utest testCompile p with expected using eqExpr in 

-- Test Declype and DeclConDef
let p : MLangProgram = {
    decls = [
      decl_type_ "Foo" [] (tyvariant_ []),
      decl_condef_ "Bar"
        (tyarrow_ tyint_ (tycon_ "Foo"))
      ],
    expr = matchex_ 
      (conapp_ "Bar" (int_ 1))
      (pcon_ "Bar" (pvar_ "x"))
      (addi_ (var_ "x") (int_ 1))
} in 
let res = testCompile p in 
utest testEval p with int_ 2 using eqExpr in 

-- Test basic semantic function
let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_sem_ 
                "f"
                [("x", tyint_)]
                [(pvar_ "y", addi_ (var_ "x") (var_ "y"))]
        ]
    ],
    expr = bind_ (use_ "L1") (appf2_ (var_ "f") (int_ 10) (int_ 20))
} in 
utest testEval p with int_ 30 using eqExpr in 

-- Test semantic function with pattern that must be ordered
-- Since the 2nd pattern is a strict subset of the first,
-- the first pattern is checked first and only if this is not a match
-- do we fall through to the first pattern. 
let fsem = decl_sem_ "f" [] [(por_ (pint_ 1) (pint_ 2), int_ -1),
                             (pint_ 2, int_ 1)]
in
let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [fsem]
    ],
    expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 2))
} in 
utest testEval p with int_ 1 using eqExpr in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [fsem]
    ],
    expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 1))
} in 
utest testEval p with int_ -1 using eqExpr in

-- Test DeclSyn and DeclSem using a small arithmetic language
let exprSyn = decl_syn_ "Expr" [("IntExpr", tyint_), 
                                ("AddExpr", tytuple_ [tycon_ "Expr", tycon_ "Expr"])] in 
let evalSem = decl_sem_ "eval" [] [(pcon_ "IntExpr" (pvar_ "i"), var_ "i"),
                                   (pcon_ "AddExpr" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]), 
                                    addi_ (appf1_ (var_ "eval") (var_ "lhs")) (appf1_ (var_ "eval") (var_ "rhs")))] in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [exprSyn, evalSem]
    ],
    expr = bind_ (use_ "MyIntArith") 
                 (appf1_ (var_ "eval") 
                         (conapp_ "AddExpr" (utuple_ [(conapp_ "IntExpr" (int_ 40)),
                                                      (conapp_ "IntExpr" (int_ 2))])))
} in 
utest testEval p with int_ 42 using eqExpr in

-- Test Sum Extension
let baseSyn = decl_syn_ "Expr" [("IntExpr", tyint_), 
                                ("AddExpr", tytuple_ [tycon_ "Expr", tycon_ "Expr"])] in 
let baseSem = decl_sem_ "eval" [] [(pcon_ "IntExpr" (pvar_ "i"), var_ "i"),
                                   (pcon_ "AddExpr" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]), 
                                    addi_ (appf1_ (var_ "eval") (var_ "lhs")) (appf1_ (var_ "eval") (var_ "rhs")))] in 
let sugarSyn = decl_syn_ "Expr" [("IncrExpr", tycon_ "Expr")] in 
let sugarEval = decl_sem_ "eval" [] [(pcon_ "IncrExpr" (pvar_ "e"), addi_ (int_ 1) (appf1_ (var_ "eval") (var_ "e")))] in 
let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [baseSyn, baseSem],
        decl_langi_ "SugaredIntArith" ["MyIntArith"] [sugarSyn, sugarEval]
    ],
    expr = bind_ (use_ "SugaredIntArith") 
                 (appf1_ (var_ "eval") 
                         (conapp_ "IncrExpr" (conapp_ "AddExpr" (utuple_ [(conapp_ "IntExpr" (int_ 20)),
                                                      (conapp_ "IntExpr" (int_ 2))]))))
} in 
utest testEval p with int_ 23 using eqExpr in

let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [baseSyn, baseSem],
        decl_langi_ "SugaredIntArith" ["MyIntArith"] [sugarSyn, sugarEval]
    ],
    expr = bind_ (use_ "SugaredIntArith")
                 (appf1_ (var_ "eval") 
                         (conapp_ "AddExpr" (utuple_ [(conapp_ "IncrExpr" (conapp_ "IntExpr" (int_ 21))),
                                                      (conapp_ "IntExpr" (int_ 1))])))
} in 
utest testEval p with int_ 23 using eqExpr in

()