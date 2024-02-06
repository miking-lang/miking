include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/lamlift.mc"


include "mclos-ast.mc"
include "mclos-pprint.mc"

include "common.mc"
include "string.mc"
include "name.mc"

lang Transpiler = MClosAst
    -- sem collectDefs : [Expr] -> [String], 
    -- sem subEnvVar envVars = 
    -- | TmVar r -> 

    sem collectNestedDefs acc envVars name counter = 
    | TmLam r -> match r.body with TmLam inner
        then 
            let lowerIdent = nameSym (concat name (int2string counter)) in
            let newBody = TmApp {
                lhs = TmVar {
                    ident = lowerIdent, 
                    ty = inner.ty,
                    info = inner.info,
                    frozen = false
                }, 
                rhs = TmEnvAdd (nameGetStr r.ident),
                ty = r.ty,
                info = r.info
            } in 
            -- let newBody = TmEnvAdd (nameGetStr r.ident) in 
            let funcDef = TmFuncDef {
                funcIdent = nameSym (concat name (int2string counter)),
                argIdent = r.ident,
                body = newBody,
                env = envVars,
                tyAnnot = r.tyAnnot,
                tyParam = r.tyParam,
                ty = r.ty,
                info = r.info} in 
            let acc = cons funcDef acc in 
            let envVars = cons (nameGetStr r.ident) envVars in 
            let counter = addi 1 counter in 
            collectNestedDefs acc envVars name counter r.body
        else 
            let funcDef = TmFuncDef {
                funcIdent = nameSym (concat name (int2string counter)),
                argIdent = r.ident,
                body = r.body,
                env = envVars,
                tyAnnot = r.tyAnnot,
                tyParam = r.tyParam,
                ty = r.ty,
                info = r.info} in 
            cons funcDef acc
    | _ -> acc

    sem collectDefs acc envVars = 
    | TmLet letRec -> 
        let identStr = nameGetStr letRec.ident in 
        collectNestedDefs [] [] identStr 0 letRec.body
    | other -> acc
    -- sem transpile = 
    -- | TmLet letRec -> match letRec.body with TmLam lamRec 
    --     then TmFuncDef {ident = letRec.ident,
    --                     body = lamRec.body,
    --                     env = "???",
    --                     tyAnnot = lamRec.tyAnnot,
    --                     tyParam = lamRec.tyParam,
    --                     ty = lamRec.ty,
    --                     info = lamRec.info}
    --     else error "Unsupported TmLet body!"
    -- | other -> other
end

mexpr 
use MExprLambdaLift in 
let addxy = ulet_ "f" 
    (ulam_ "x"
        (ulam_ "y" (addi_ (var_ "x") (var_ "y")))) in 
let liftedAddxy = liftLambdas addxy in 
use MClosPrettyPrint in 
-- (printLn (expr2str addxy)) ; 
-- (printLn (expr2str liftedAddxy)) ;
use Transpiler in
let defs = collectDefs [] [] liftedAddxy in 
use MClosPrettyPrint in 
() ;
printLn (strJoin "\n" (map expr2str defs))
-- let f1 = (app_ (lam_ "x" tyint_ (addi_ (var_ "x") (int_ 1))) (int_ 3)) in
-- let f1 = liftLambdas f1 in 
-- use Transpiler in 
-- let transpiled = transpile f1 in
-- use MClosPrettyPrint in 
-- printLn (expr2str transpiled)