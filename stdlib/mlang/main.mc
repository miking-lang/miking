include "composition-check.mc"
include "result.mc"

include "compile.mc"
include "boot-parser.mc"
include "ast-builder.mc"
include "symbolize.mc"
include "composition-check.mc"
include "const-transformer.mc"

include "mexpr/eval.mc"
include "mexpr/builtin.mc"


lang MainLang = MLangCompiler + BootParserMLang + 
                MLangSym + MLangCompositionCheck +
                MExprPrettyPrint + MExprEval + MExprEq
                + MLangConstTransformer
end

mexpr
use MainLang in 
let simpleEval = lam e. eval (evalCtxEmpty ()) e in 


let eval = lam str. 
  let parseResult = _consume (parseMLangString str) in
  match parseResult with (_, errOrResult) in 
  match errOrResult with Left _ then 
    error "Something went wrong during parsing!"
  else match errOrResult with Right p in
    let p = constTransformProgram builtin p in
    match symbolizeMLang symEnvDefault p with (_, p) in 
    match _consume (checkComposition p) with (_, res) in 
    match res with Right env in
    let ctx = _emptyCompilationContext env in 
    let res = _consume (compile ctx p) in 
    match res with (_, rhs) in 
    match rhs with Right expr in
    simpleEval expr
in 

utest eval "let x = 10\nmexpr\n10" with int_ 10 using eqExpr in 

let str = strJoin "\n" [
  "type Tree",
  "con Leaf: Int -> Tree",
  "con Node: (Tree, Tree) -> Tree",
  "recursive",
  "  let sum = lam tree.",
  "    match tree with Node (l, r) then",
  "    addi (sum l) (sum r)",
  "    else (match tree with Leaf val in val)",
  "end",
  "mexpr",
  "sum (Node (Leaf 10, Leaf 20))"
] in
utest eval str with int_ 30 using eqExpr in 

()
