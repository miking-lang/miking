include "mexpr/pprint.mc"
include "mclos-ast.mc"
include "name.mc"
include "mexpr/ast-builder.mc"

lang MClosPrettyPrint = MExprPrettyPrint + MClosAst
    sem pprintCode indent env =
    | TmFuncDef f -> 
        let formattedBody = match pprintCode (addi 4 indent) env f.body with (_, str) in str in
        let args = strJoin ", " (map (lam r. nameGetStr r.ident) f.args) in
        (env, join [
            "funcdef ",
            nameGetStr f.funcIdent,
            " = lam ",
            args,
            ".\n",
            pprintSpacing (addi 4 indent),
            formattedBody
        ])
end

mexpr 
use MClosPrettyPrint in 
utest expr2str (TmFuncDef {
    funcIdent = nameSym "f",
    args = [{ident = nameSym "x", ty = tyint_}],
    body = int_ 10,
    tyAnnot = tyint_, 
    ty = tyint_,
    info = NoInfo ()
}) with "funcdef f = lam x.\n    10" in ()