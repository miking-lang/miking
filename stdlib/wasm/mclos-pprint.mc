include "mexpr/pprint.mc"
include "mclos-ast.mc"
include "name.mc"

lang MClosPrettyPrint = MExprPrettyPrint + MClosAst
    sem expr2str = 
    | TmFuncDef f -> 
        let formattedBody = expr2str f.body in 
        join [
            "FuncDef(",
            nameGetStr f.funcIdent,
            " ",
            nameGetStr f.argIdent,
            "",
            strJoin " " f.env, 
            "\n",
            formattedBody,
            ")"
        ]
    | TmEnvAdd envIdent -> join ["EnvAdd(", envIdent, ")"]

    sem isAtomic = 
    | _ -> false

    sem pprintCode indent env =
    | TmFuncDef f -> 
        let formattedBody = expr2str f.body in 
        join [
            "FuncDef(",
            nameGetStr f.funcIdent,
            " ",
            nameGetStr f.argIdent,
            "",
            strJoin " " f.env, 
            "\n",
            formattedBody,
            ")"
        ]
    | TmEnvAdd envIdent -> (env, join ["EnvAdd(", envIdent, ")"])
    -- | TmEnvVar r -> (env, join ["TmEnvVar(", nameGetStr r.ident, ")"])
end