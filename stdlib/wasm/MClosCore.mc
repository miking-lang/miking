lang MClosCore
    syn Expr = 
    | TmApp(Expr, Expr)
    | TmAdd(Expr, Expr)
    | TmInt(Int)
    | TmEnvVar(Env, String)
    | TmVar(String)
    | TmMatchVar String
    | TmFunc(String)
    | TmEnvAdd {
        src: Env,
        target: Env,
        newId: String,
        value: Expr
    }
    | TmConstruct {
        ident: String,
        args: [Expr]
    }
    | TmMatch {
        target: Expr,
        pat: Pat,
        thn: Expr,
        els: Expr
    }

    syn Pat = 
    | Wildcard
    | IntPat Int
    | ADTPat (String, [String])

    syn Env =
    | BasicEnv { 
        envVars: [{name: String, typeString: String}], 
        wasmTypeAlias: String
    }

    syn Def = 
    | FuncDef(String, Env, String, String, Expr)
    | ADTDef {
        ident: String,
        constructors: [{
            ident: String,
            argTypes: [String]
        }]
    }
end

mexpr
use MClosCore in 
utest TmInt(10) with TmInt(10) in ()