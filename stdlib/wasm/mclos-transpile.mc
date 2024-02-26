include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/lamlift.mc"
include "mexpr/pprint.mc"
include "mexpr/eq.mc"

include "mclos-ast.mc"
include "mclos-pprint.mc"

include "common.mc"
include "string.mc"
include "name.mc"
include "option.mc"

type SigType = {
    ident: Name,
    tyAnnot: (use MClosAst in Type),
    ty: (use MClosAst in Type),
    info: Info
}

type TranspileContext = {
    mainExpr: Option (use MClosAst in Expr),
    functionDefs: [(use MClosAst in Expr)],
    globals: [
        {ident: Name, value: (use MClosAst in Expr)}
    ]
}

lang MClosTranspiler = MClosAst
    sem extractFuncDef: [{ident: Name, ty: Type}] -> SigType -> Expr -> Expr
    sem extractFuncDef argsAcc sig = 
    | TmLam lamRec -> 
        let newArg = match (nameGetStr lamRec.ident) with "" then (nameNoSym "_unnamed") else lamRec.ident in 
        let newArgsAcc = (snoc argsAcc {ident = newArg, ty = lamRec.tyParam}) in 
        extractFuncDef newArgsAcc sig lamRec.body
    | other ->  
        TmFuncDef {
            funcIdent = sig.ident,
            tyAnnot = sig.tyAnnot,
            ty = sig.ty,
            info = sig.info,
            body = other,
            args = argsAcc
        }

    sem transpileAcc : TranspileContext -> Expr -> TranspileContext
    sem transpileAcc ctx = 
    | TmLet r -> 
        match r.body with TmLam _ 
            then 
                let sig: SigType = {
                    ident = r.ident,
                    tyAnnot = r.tyAnnot,
                    ty = r.ty,
                    info = r.info
                } in 
                let newDef = (extractFuncDef [] sig r.body) in 
                let ctx = {ctx with functionDefs = snoc ctx.functionDefs newDef} in 
                transpileAcc ctx r.inexpr
            else 
                let newGlobal = {
                    ident = r.ident,
                    value = r.body
                } in 
                let ctx = {ctx with globals = snoc ctx.globals newGlobal} in 
                transpileAcc ctx r.inexpr
    | TmRecLets {bindings = bindings, inexpr = inexpr} ->
        let work = lam acc. lam r. 
            let sig = {
                ident = r.ident,
                tyAnnot = r.tyAnnot,
                info = r.info, 
                ty = r.tyBody
            } in 
            let newDef = (extractFuncDef [] sig r.body) in 
            {ctx with functionDefs = snoc ctx.functionDefs newDef}
        in
        let ctx = foldl work ctx bindings in 
        transpileAcc ctx inexpr
    | other -> 
        {ctx with mainExpr = Some other}

    sem transpile =
    | expr -> 
        let ctx = {
            functionDefs = [],
            globals = [],
            mainExpr = None ()
        } in 
        transpileAcc ctx expr
end

mexpr
use MClosTranspiler in 
let body = (addi_ (var_ "x") (int_ 10)) in 
let f = ulet_ "f" (ulam_ "x" body) in 
let expr = app_ (var_ "f") (int_ 10) in 
let prog = bind_ f expr in 
let transpiled = transpile prog in 
match head transpiled with TmFuncDef f in 
    utest nameGetStr f.funcIdent with "f" in 
    utest length f.args with 1 in 
    utest nameGetStr (head f.args).ident with "x" in 
    utest f.body with body using (use MExprEq in eqExpr) in 

let body = (addi_ (var_ "x") (var_ "y")) in 
let g = ulet_ "g" (ulam_ "x" (ulam_ "y" body)) in 
let expr = app_ (app_ (var_ "g") (int_ 10)) (int_ 20) in 
let prog = bind_ g expr in 
let transpiled = transpile prog in 
match head transpiled with TmFuncDef f in 
    utest nameGetStr f.funcIdent with "g" in 
    utest length f.args with 2 in 
    utest f.body with body using (use MExprEq in eqExpr) in 
-- use MClosPrettyPrint in 
-- (printLn (expr2str prog)) ;
-- (printLn (strJoin "\n\n" (map expr2str transpiled))) ;
() 