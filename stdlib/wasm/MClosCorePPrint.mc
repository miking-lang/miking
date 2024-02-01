include "MClosCore.mc"

include "string.mc"

lang MClosCorePPrint = MClosCore
    sem pprintExpr = 
    | TmInt(i) -> join ["TmInt(", (int2string i), ")"]
    | TmEnvVar(env, id) -> 
        let sEnv = pprintEnv env in 
        join ["TmEnvVar(", sEnv, ", ", id, ")"]
    | TmVar(id) -> join ["TmVar(", id, ")"]
    | TmFunc(id) -> join ["TmFunc(", id, ")"]
    | TmApp(e1, e2) -> 
        let s1 = pprintExpr e1 in
        let s2 = pprintExpr e2 in 
        join ["TmApp(", s1, ", ", s2, ")"]
    | TmEnvAdd(env, id, expr) ->
        let sEnv = pprintEnv env in 
        let sExpr = pprintExpr expr in
        join ["TmEnvAdd(", sEnv, ", ", id, ", ", sExpr, ")"]
    sem pprintEnv = 
    | BasicEnv r -> 
        join ["BasicEnv({wasmTypeAlias=", r.wasmTypeAlias, "})"]

    sem pprintDef = 
    | FuncDef(env, argId, body) -> 
        let s1 = pprintEnv env in
        let s2 = pprintExpr body in 
        join ["FuncDef(", s1, ", ", argId, ", ", s2, ")"]
end

mexpr
use MClosCorePPrint in 
let env1 = BasicEnv {envVars = [], wasmTypeAlias="sometype"} in
utest pprintExpr (TmInt 10) with "TmInt(10)" in 
utest pprintExpr (TmEnvVar (env1, "x")) with "TmEnvVar(BasicEnv({wasmTypeAlias=sometype}), x)" in 
utest pprintExpr (TmVar "y") with "TmVar(y)" in 
utest pprintExpr (TmFunc "f") with "TmFunc(f)" in 
utest pprintExpr (TmApp (TmFunc "f", TmInt 10)) with 
    "TmApp(TmFunc(f), TmInt(10))" in 
utest pprintExpr (TmEnvAdd (env1, "x", TmInt 10)) with
    "TmEnvAdd(BasicEnv({wasmTypeAlias=sometype}), x, TmInt(10))" in 
utest pprintEnv env1 with
    "BasicEnv({wasmTypeAlias=sometype})" in
utest pprintDef (FuncDef (env1, "x", TmVar "x")) with 
    "FuncDef(BasicEnv({wasmTypeAlias=sometype}), x, TmVar(x))" in 
()