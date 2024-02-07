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

type SigType = {
    ident: Name,
    tyAnnot: (use MClosAst in Type),
    ty: (use MClosAst in Type),
    info: Info
}

lang MClosTranspiler = MClosAst
    sem extractFuncDef: [{ident: Name, ty: Type}] -> SigType -> Expr -> Expr
    sem extractFuncDef argsAcc sig = 
    | TmLam lamRec -> 
        let newArgsAcc = (snoc argsAcc {ident = lamRec.ident, ty = lamRec.tyParam}) in 
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

    sem transpileAcc : [Expr] -> Expr -> [Expr]
    sem transpileAcc acc = 
    | TmLet r -> 
        let sig: SigType = {
            ident = r.ident,
            tyAnnot = r.tyAnnot,
            ty = r.ty,
            info = r.info
        } in 
        let funDef = (extractFuncDef [] sig r.body) in 
        let acc = cons funDef acc in 
        transpileAcc acc r.inexpr
    | other -> cons other acc

    sem transpile =
    | expr -> reverse (transpileAcc [] expr)
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