include "mexpr/pprint.mc"
include "mexpr/lamlift.mc"
include "mexpr/lamlift.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

include "wasm-ast.mc"
include "wasm-pprint.mc"
include "wasm-stdlib.mc"
include "wasm-apply.mc"
include "mclos-ast.mc"
include "mclos-transpile.mc"

include "string.mc"
include "seq.mc"
include "map.mc"
include "tuple.mc"

-- type FunctionSignature = {
--     ident: String,
--     args: [{ident: String, ty: (use WasmAST in WasmType)}],
--     resultTy: (use WasmAST in WasmType)
-- }

type WasmCompileContext = {
    defs: [(use WasmAST in Def)],
    ident2fp: Map String Int,
    nextFp: Int,
    mainExpr: (use MClosAst in Option Expr)
}

let accArity = lam acc: Set Int. lam def: (use WasmAST in Def).
    use WasmAST in 
    match def with FunctionDef funDef
        then setInsert (length funDef.args) acc
        else acc


let findFuncDef = lam ctx : WasmCompileContext. lam ident : String. 
    use WasmAST in 
    find 
        (lam def. match def with FunctionDef f then eqString ident f.ident else false)
        ctx.defs

let emptyCompileCtx : WasmCompileContext = {
    defs = [],
    ident2fp = mapEmpty cmpString,
    nextFp = 0,
    mainExpr = None ()
}

type WasmExprContext = {
    locals: [{ident: String, ty: (use WasmAST in WasmType)}],
    instructions: [(use WasmAST in Instr)],
    result: Either (use WasmAST in Instr) String,
    nextLocal: Int
}

let emptyExprCtx : WasmExprContext = {
    locals = [],
    instructions = [],
    result = Left (use WasmAST in I32Const 0), -- This is a temp value, should maybe throw exception.
    nextLocal = 0
}

let extractResult = lam ctx : WasmExprContext.
    use WasmAST in 
    match ctx.result with Left instr
        then instr
        else match ctx.result with Right ident in LocalGet ident

let ctxInstrResult = lam ctx: WasmExprContext . lam instr : (use WasmAST in Instr). 
    {ctx with result = Left instr}

let ctxLocalResult = lam ctx : WasmExprContext. lam ident : String. 
    {ctx with result = Right ident}

let ctxWithFuncDef = lam ctx. lam def. 
    use WasmAST in 
    match def with FunctionDef f 
        then 
            {ctx with 
                defs = snoc ctx.defs def,
                nextFp = addi 1 ctx.nextFp,
                ident2fp = mapInsert f.ident ctx.nextFp ctx.ident2fp}
        else 
            {ctx with defs = snoc ctx.defs def}

let createClosureStruct = lam arity: Int. lam fp: Int. 
    use WasmAST in 
    let closure = StructNew {
        structIdent = "clos",
        values = [
            I32Const fp,
            I32Const arity,
            I32Const 0,
            ArrayNew {
                tyIdent = "args-array",
                initValue = GlobalGet "null-like",
                size = I32Const arity
            }
        ]
    } in 
    match arity with 0
        then Call ("exec-0", [closure])
        else closure

let createClosure = lam globalCtx: WasmCompileContext. lam exprCtx. lam ident: String.
    use WasmAST in 
    match findFuncDef globalCtx ident with Some def
        then 
            match def with FunctionDef f in
            let arity = length f.args in 
            match mapLookup f.ident globalCtx.ident2fp with Some (fp) in 
            ctxInstrResult exprCtx (createClosureStruct arity fp) 
        else 
            error (join ["Identifier '", ident, "' is not a function!"])

let createArithOpClosure = lam globalCtx. lam exprCtx. lam opIdent. 
    use WasmAST in 
    createClosure globalCtx exprCtx opIdent

lang WasmCompiler = MClosAst + WasmAST
    sem compileConst : WasmCompileContext -> WasmExprContext -> Const -> WasmExprContext
    sem compileConst globalCtx exprCtx = 
    | CInt {val = i} -> ctxInstrResult exprCtx (I31Cast (I32Const i))
    | CAddi _ -> createArithOpClosure globalCtx exprCtx "addi"
    | CMuli _ -> createArithOpClosure globalCtx exprCtx "muli"
    | CSubi _ -> createArithOpClosure globalCtx exprCtx "subi"

    sem compileExpr : WasmCompileContext -> WasmExprContext -> Expr -> WasmExprContext
    sem compileExpr globalCtx exprCtx = 
    | TmConst {val = c} -> 
        compileConst globalCtx exprCtx c
    | TmVar {ident = ident} ->
        match findFuncDef globalCtx (nameGetStr ident) with Some d
            then
                createClosure globalCtx exprCtx (nameGetStr ident)
                -- match d with FunctionDef f in
                -- let arity = length f.args in 
                -- match mapLookup f.ident globalCtx.ident2fp with Some (fp) in 
                -- ctxInstrResult exprCtx (createClosure arity fp) 
            else ctxLocalResult exprCtx (nameGetStr ident)
    | TmApp {lhs = lhs, rhs = rhs} ->
        let leftCtx = compileExpr globalCtx exprCtx lhs in 
        let rightCtx = compileExpr globalCtx leftCtx rhs in 
        let applyInstr = Call ("apply", [
            extractResult leftCtx,
            extractResult rightCtx
        ]) in 
        ctxInstrResult rightCtx applyInstr


    sem ctxAcc : WasmCompileContext -> Expr -> WasmCompileContext
    sem ctxAcc globalCtx = 
    | TmFuncDef f -> 
        let args = map (lam arg. {ident = nameGetStr arg.ident, ty = Anyref()}) f.args in
        -- let args = create (length f.args) 
        --     (lam i. {ident = concat "arg" (int2string i), 
        --              ty = Anyref()}) in 
        let exprCtx = compileExpr globalCtx emptyExprCtx f.body in 
        ctxWithFuncDef globalCtx (FunctionDef {
            ident = nameGetStr  f.funcIdent,
            args = args,
            locals = exprCtx.locals,
            resultTy = Anyref(), 
            instructions = snoc exprCtx.instructions (extractResult exprCtx)
        })
    | mainExpr -> 
        match globalCtx.mainExpr with Some _ 
            then 
                error "Main expression is already set!"
            else 
                let exprCtx = compileExpr globalCtx emptyExprCtx mainExpr in 
                let resultExpr = I31GetS (RefCast {
                    ty = I31Ref (),
                    value = (extractResult exprCtx)
                }) in 
                ctxWithFuncDef globalCtx (FunctionDef {
                    ident = "mexpr",
                    args = [],
                    locals = exprCtx.locals,
                    resultTy = Tyi32 (), 
                    instructions = snoc exprCtx.instructions resultExpr
                })


    sem createCtx : WasmCompileContext -> [Expr] -> WasmCompileContext
    sem createCtx ctx = 
    | exprs -> foldl ctxAcc ctx exprs

    sem compile : [Expr] -> Mod
    sem compile = 
    | exprs -> 
        -- Add stdlib definitions
        let stdlibDefs = [addiWasm, subiWasm, muliWasm] in 
        let ctx = emptyCompileCtx in
        let ctx = foldl ctxWithFuncDef ctx stdlibDefs in 

        -- Compile functions
        let ctx = createCtx ctx exprs in 

        -- Add apply, exec and dispatch based on aritites
        let arities = foldl accArity (setEmpty subi) ctx.defs in 
        let arities = setToSeq arities in 
        let genericTypes = map genGenericType arities in 
        let execs = map genExec arities in 
        let dispatch = genDispatch arities in 
        let ctx = {ctx with
            defs = join [[argsArrayType, closDef, nullLikeDef], genericTypes, execs, [dispatch, apply], ctx.defs]
        } in 

        let sortedKVs = sort (tupleCmp2 (lam s1. lam s2. 0) subi) (mapToSeq ctx.ident2fp) in
        let sortedNames = map (lam kv. match kv with (k, v) in k) sortedKVs in 
        Module {
            definitions = ctx.defs,
            table = Table {size = mapSize ctx.ident2fp, typeString = "funcref"},
            elem = Elem {offset = I32Const 0, funcNames = sortedNames},
            types = [],
            exports = ["mexpr"]
        }
end

let compileMCoreToWasm = lam ast.
    use MExprLowerNestedPatterns in 
    let ast = lowerAll ast in 
    use MExprLambdaLift in
    let ast = liftLambdas ast in
    use MClosTranspiler in 
    let exprs = transpile ast in
    use WasmCompiler in 
    let wasmModule = compile exprs in
    use WasmPPrint in 
    printLn (pprintMod wasmModule) ;
    -- (printLn "Lifted Lambdas: ");
    -- (printLn (use MExprPrettyPrint in expr2str ast));
    -- use MExprClosAst in
    -- let ast =  closureConvert ast in
    -- (printLn (use MExprPrettyPrint in expr2str ast)) ;
    ""

mexpr
use WasmCompiler in 
-- let body = (int_ 10) in 
let myadd = ulet_ "myadd" (ulam_ "x" (ulam_ "y" (int_ 0))) in 
let body = (app_ (app_ (var_ "muli") (int_ 1)) (int_ 2)) in 
let g = ulet_ "g" body in 
let expr = app_ (app_ (var_ "g") (int_ 10)) (int_ 20) in 
let prog = bind_ myadd (bind_ g expr) in 
let transpiled = (use MClosTranspiler in transpile body) in 
-- let ctx = createCtx transpiled in 
let mod = compile transpiled in 
use WasmPPrint in 
printLn (pprintMod mod)
-- let str = pprintDef 0 (head ctx.defs) in 
-- let str2 = pprintDef 0 (head (tail ctx.defs)) in 
-- printLn str ;
-- printLn str2 ;
-- printLn (mapLookupApplyOrElse int2string (lam. "fallback") "g" ctx.ident2fp) 
-- ;
-- ()