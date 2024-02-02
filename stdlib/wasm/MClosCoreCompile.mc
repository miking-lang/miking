include "MClosCore.mc"
include "wasm-ast.mc"
include "wasm-pprint.mc"
include "string.mc"
include "common.mc"

type Context = {
    nameToFP: [(String, Int)]
}

recursive
let findName = lam l: [(String, Int)]. lam name: String. 
    match l with []
        then error "Name not found"
        else match head l with (id, fp)
            then 
                if eqString id name 
                    then fp 
                    else (findName (tail l) name)
            else error "Error unexpected mismatch!"
end

lang MClosCoreCompile = MClosCore + WasmAST
    sem compileExpr: Context -> Expr -> Instr
    sem compileExpr ctx = 
    | TmApp(e1, e2) -> 
        let res1 = compileExpr ctx e1 in
        let res2 = compileExpr ctx e2 in 
        Call ("apply", [res1, res2])
    | TmInt(i) -> 
        Call ("box", [I32Const i])
    | TmAdd(e1, e2) -> 
        let unbox = lam e. Call ("unbox", [e]) in
        let r1 = unbox (compileExpr ctx e1) in
        let r2 = unbox (compileExpr ctx e2) in 
        let addInstr = I32Add(r1, r2) in
        Call ("box", [addInstr])
    | TmFunc(id) -> 
        let fp = findName ctx.nameToFP id in
        let envName = concat id "-env" in
        StructNew {
            typeAlias = "clos",
            values = [I32Const fp, StructNew {typeAlias = envName, values = []}]
        }
    | TmVar(id) -> LocalGet id
    | TmEnvVar(env, id) -> match env with BasicEnv r
        then 
            StructGet {
                typeAlias = r.wasmTypeAlias,
                field = id,
                value = (RefCast {
                    typeAlias = r.wasmTypeAlias,
                    value = LocalGet "env"
                })
            }
        else error "Only BasicEnv is supported!"
    | TmEnvAdd r -> 
        let idToTMEnvVar = lam env. lam id. TmEnvVar(env, id) in
        let allValues = lam env.
            match env with BasicEnv r
                then
                    let tmEnvVars = map (idToTMEnvVar env) r.envVars in
                    map (compileExpr ctx) tmEnvVars
                else error "???" in
        match r.target with BasicEnv targetEnv
            then match r.src with BasicEnv sourceEnv
                then StructNew {
                    typeAlias = targetEnv.wasmTypeAlias,
                    values = cons (compileExpr ctx r.value) (allValues r.src)
                } 
            else error "???"
        else error "???"

    sem compileDef: Context -> Def -> Func
    sem compileDef ctx = 
    | FuncDef(fname, env, id, body) -> match env with BasicEnv r
        then
            let envType = r.wasmTypeAlias in
            let locals = [
                {name = "env", typeAlias=join["(ref $", envType, ")"]},
                {name=id, typeAlias="(ref $i32box)"}
            ] in
            let body = compileExpr ctx body in 
            let setLocal = LocalSet (
                "env",
                RefCast {typeAlias = envType, value = LocalGet "arg0"}) in
            let setLocal2 = LocalSet (
                id,
                RefCast {typeAlias = "i32box", value = LocalGet "arg1"}) in
            Function {
                name = fname,
                args = ["arg0", "arg1"],
                locals = locals,
                instructions = [setLocal, setLocal2, body]
            }
        else 
            error "error"

    sem compileEnvToWasmType: Env -> WasmType
    sem compileEnvToWasmType = 
    | BasicEnv r -> 
        let var2wasmfield = lam var. {name = var, typeString = "(ref $i32box)"} in
        StructType {
            name = r.wasmTypeAlias,
            fields = map var2wasmfield r.envVars
        }

    sem wrapExprInMExpr: Instr -> Func
    sem wrapExprInMExpr = 
    | instr -> 
        let setResultInstr = LocalSet("result", instr) in
        let unboxResultInstr = Call(
            "unbox", 
            [RefCast {
                typeAlias = "i32box", 
                value = LocalGet "result"}]) in
        Function {
            name = "mexpr",
            args = [],
            locals = [{name = "result", typeAlias="anyref"}],
            instructions = [setResultInstr, unboxResultInstr]
        }

    sem createCtx: [Def] -> Context
    sem createCtx = 
    | defs -> 
        let def2tuple = lam index. lam def. 
            match def with FuncDef(name, _, _, _)
                then (name, index)
                else error "Unsupported Def"
        in {nameToFP = mapi def2tuple defs}

    -- sem compile: [Def] -> Expr -> Context
    sem compile defs = 
    | expr -> 
        let def2env = lam def. match def with FuncDef(_, env, _, _)
            then env 
            else error "Unknown Def"
        in 
        let def2name = lam def. match def with FuncDef(name, _, _, _)
            then name 
            else error "Unknown Def"
        in 
        let ctx = createCtx defs in 
        let envs = map def2env defs in 
        let fnames = map def2name defs in 
        let table = Table {size = length fnames, typeString = "funcref"} in
        let elem = Elem {offset = I32Const 0, funcNames = fnames} in 
        let types = map compileEnvToWasmType envs in 
        let functions = map (compileDef ctx) defs in
        let main = wrapExprInMExpr (compileExpr ctx expr) in 
        Module {
            functions = concat functions [main],
            table = table,
            elem = elem,
            types = types,
            exports = ["mexpr"]
        }
    -- Module {functions = [], exports = []}
end

mexpr
-- let h lam env. lam z. x + y + z
use MClosCoreCompile in 
let h_env = BasicEnv {wasmTypeAlias = "h-env", envVars=["y", "x"]} in
let h = FuncDef("h", h_env, "z", TmAdd(
    TmAdd(
        TmEnvVar(h_env, "x"), 
        TmEnvVar(h_env, "y")
    ), TmVar("z"))) in

let g_env = BasicEnv {wasmTypeAlias = "g-env", envVars=["x"]} in
let g = FuncDef("g", g_env, "y", TmApp(TmFunc("h"), TmEnvAdd {
    src = g_env,
    target = h_env, 
    newId = "y",
    value = TmVar("y")
})) in

let f_env = BasicEnv {wasmTypeAlias = "f-env", envVars=[]} in
let f = FuncDef("f", f_env, "x", TmApp(TmFunc("g"), TmEnvAdd {
    src = f_env,
    target = f_env, 
    newId = "x",
    value = TmVar("x")
})) in

let gEnvType = compileEnvToWasmType g_env in 
let gEnvTypeStr = (use WasmPPrint in pprintType 0 gEnvType) in 

let mod = compile [f, g, h] (TmInt 10) in
let s = (use WasmPPrint in pprintMod mod) in 
(printLn s)
-- utest gEnvTypeStr with "(type $g-env\n    (struct\n        (field $x (ref $i32box))))" in 
-- utest compileExpr (TmInt 10) with Call ("box", [I32Const 10]) in

-- -- let mcc1 = TmApp(TmFunc("f"), TmInt(10)) in
-- -- let wasm1 = compileExpr mcc1 in
-- -- let str1 = (use WasmPPrint in (pprintInstr 0 wasm1)) in

-- -- let mcc2 = TmApp(TmFunc("f"), 
-- --     TmEnvVar(BasicEnv {wasmTypeAlias = "some-env", envVars = ["x"]}, "x")) in
-- -- let wasm2 = compileExpr mcc2 in
-- -- let str2 = (use WasmPPrint in (pprintInstr 0 wasm2)) in 

-- -- let mcc3 = TmEnvAdd {
-- --     src = BasicEnv {envVars = ["y"], wasmTypeAlias = "base"},
-- --     target = BasicEnv {envVars = ["x", "y"], wasmTypeAlias = "base-with-x"},
-- --     newId = "x",
-- --     value = TmInt(10)
-- -- } in 
-- -- let wasm3 = compileExpr mcc3 in 
-- -- let str3 = (use WasmPPrint in (pprintInstr 0 wasm3)) in

-- -- let make_f = compileDef f in
-- -- let f_str = (use WasmPPrint in5r (pprintFunc make_f)) in 
-- -- let make_g = compileDef g in
-- -- let g_str = (use WasmPPrint in (pprintFunc make_g)) in 
-- -- let make_h = compileDef h in
-- -- let h_str = (use WasmPPrint in (pprintFunc make_h)) in 
-- -- -- (printLn "Function body f:");
-- -- (printLn f_str);
-- -- -- (printLn "Function body g:");
-- -- (printLn g_str);
-- -- -- (printLn "Function body h:");
-- -- (printLn h_str)

-- -- (printLn str1);
-- -- (printLn str2)
-- -- (printLn str3)

-- let e = TmApp(TmApp(TmApp(TmFunc("f"), TmInt(10)), TmInt(20)), TmInt(30)) in 
-- let e = TmApp(TmApp(TmApp(TmFunc("f"), TmInt(10)), TmInt(2)), TmInt(42)) in 
-- let wasm = compileExpr ctx e in
-- let main = wrapExprInMExpr wasm in
-- let str = (use WasmPPrint in (pprintFunc main)) in
-- -- ()
-- let str = (use WasmPPrint in (pprintInstr 0 wasm)) in
-- (printLn str)