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

  sem compileProg : CompilationContext -> MLangProgram -> CompilationResult
  sem compileProg ctx = 
  | prog -> 
    let res = _foldl compileDecl ctx prog.decls in
    _map (lam ctx. withExpr ctx prog.expr) res

  sem compile : CompilationContext -> MLangProgram -> Expr
  sem compile ctx =| prog -> 
    match _consume (compileProg ctx prog) with (_, res) in
    switch res
      case Left err then error "Compilation error(s) occured!"
      case Right ctx then bindallutest_ ctx.exprs
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
  compile ctx p
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

()