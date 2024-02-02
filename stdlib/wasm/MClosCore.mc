lang MClosCore
    syn Expr = 
    | TmApp(Expr, Expr)
    | TmAdd(Expr, Expr)
    | TmInt(Int)
    | TmEnvVar(Env, String)
    | TmVar(String)
    | TmFunc(String)
    | TmEnvAdd {
        src: Env,
        target: Env,
        newId: String,
        value: Expr
    }

    syn Env =
    | BasicEnv { 
        envVars: [{name: String, typeString: String}], 
        wasmTypeAlias: String
    }

    syn Def = 
    | FuncDef(String, Env, String, String, Expr)
end

mexpr
use MClosCore in 
utest TmInt(10) with TmInt(10) in ()