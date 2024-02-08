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


let createClosure = lam arity. lam fp. 
    use WasmAST in 
    StructNew {
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
    }

lang WasmCompiler = MClosAst + WasmAST
    sem compileConst : WasmCompileContext -> WasmExprContext -> Const -> WasmExprContext
    sem compileConst globalCtx exprCtx = 
    | CInt {val = i} -> ctxInstrResult exprCtx (Call ("box", [I32Const i]))

    sem compileExpr : WasmCompileContext -> WasmExprContext -> Expr -> WasmExprContext
    sem compileExpr globalCtx exprCtx = 
    | TmConst {val = c} -> 
        compileConst globalCtx exprCtx c
    | TmVar {ident = ident} ->
        match findFuncDef globalCtx (nameGetStr ident) with Some d
            then
                match d with FunctionDef f in
                let arity = length f.args in 
                match mapLookup f.ident globalCtx.ident2fp with Some (fp) in 
                ctxInstrResult exprCtx (createClosure arity fp) -- todo create closure
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
        let args = create (length f.args) 
            (lam i. {ident = concat "arg" (int2string i), 
                     ty = Anyref()}) in 
        let exprCtx = compileExpr globalCtx emptyExprCtx f.body in 
        ctxWithFuncDef globalCtx (FunctionDef {
            ident = nameGetStr  f.funcIdent,
            args = args,
            locals = exprCtx.locals,
            resultTy = Anyref(), 
            instructions = snoc exprCtx.instructions (extractResult exprCtx)
        })
    -- | _ -> globalCtx
    | mainExpr -> 
        match globalCtx.mainExpr with Some _ 
            then 
                error "Main expression is already set!"
            else 
                let exprCtx = compileExpr globalCtx emptyExprCtx mainExpr in 
                let resultExpr = Call ("unbox", [
                    RefCast {
                        ty = Ref "i32box",
                        value = (extractResult exprCtx)
                    }
                ]) in 
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
        let stdlibDefs = [nullLikeDef, genericType2Def, argsArrayType, closType, i32boxDef, apply, box, unbox, addiWasm] in 
        let ctx = emptyCompileCtx in
        let ctx = foldl ctxWithFuncDef ctx stdlibDefs in 
        let ctx = createCtx ctx exprs in 
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
    -- (printLn "Lifted Lambdas: ");
    -- (printLn (use MExprPrettyPrint in expr2str ast));
    -- use MExprClosAst in
    -- let ast =  closureConvert ast in
    (printLn (use MExprPrettyPrint in expr2str ast)) ;
    ""

mexpr
use WasmCompiler in 
-- let body = (int_ 10) in 
let myadd = ulet_ "myadd" (ulam_ "x" (ulam_ "y" (int_ 0))) in 
let body = (app_ (app_ (var_ "addi") (int_ 1)) (int_ 2)) in 
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