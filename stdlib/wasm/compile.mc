include "mexpr/pprint.mc"
include "mexpr/lamlift.mc"
include "mexpr/lamlift.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

include "string.mc"
include "seq.mc"

let compileMCoreToWasm = lam ast.
    use MExprLowerNestedPatterns in 
    let ast = lowerAll ast in 
    -- use MExprLambdaLift in
    -- let ast = liftLambdas ast in
    -- (printLn "Lifted Lambdas: ");
    -- (printLn (use MExprPrettyPrint in expr2str ast));
    -- use MExprClosAst in
    -- let ast =  closureConvert ast in
    (printLn (use MExprPrettyPrint in expr2str ast)) ;
    ""

mexpr
let sseq = seq_ [int_ 1] in
let m = match_ (sseq) (pseqedgew_ [pint_ 1]) (int_ 1) (int_ 2) in 
let e1 = bind_ (ulet_ "x" (int_ 10)) m in
-- let f1 = (app_ (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))) (int_ 3)) in
use MExprPrettyPrint in
(printLn (expr2str e1))
-- compileMCoreToWasm f1
-- (printLn (compileMCoreToWasm f1))