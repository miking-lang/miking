include "./ast.mc"
include "./ast-builder.mc"
include "./pprint.mc"
include "./symbolize.mc"
include "./composition-check.mc"

include "mexpr/eval.mc"
include "mexpr/eq.mc"

include "common.mc"
include "bool.mc"
include "name.mc"
include "set.mc"
include "result.mc"

type CompilationContext = use MLangAst in {
  exprs: [Expr],
  compositionCheckEnv : CompositionCheckEnv
}

let _emptyCompilationContext : CompositionCheckEnv -> CompilationContext = lam env : CompositionCheckEnv. {
  exprs = [],
  compositionCheckEnv = env
}

let withExpr = lam ctx. lam expr. {ctx with exprs = snoc ctx.exprs expr}

type CompilationError
con FoundIncludeError : {info : Info, path: String} -> CompilationError

type CompilationWarning

type CompilationResult = Result CompilationWarning CompilationError CompilationContext 

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
      case Right ctx then _ok (bindallutest_ ctx.exprs)
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

()