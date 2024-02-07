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
include "mclos-ast.mc"
include "mclos-transpile.mc"

include "string.mc"
include "seq.mc"

type WasmCompileContext = {
    defs: [(use WasmAST in Def)],
    mainExpr: (use MClosAst in Option Expr)
}

let findFuncDef = lam ctx : WasmCompileContext. lam ident : String. 
    use WasmAST in 
    find 
        (lam def. match def with FunctionDef f then eqString ident f.ident else false)
        ctx.defs

let emptyCompileCtx : WasmCompileContext = {
    defs = [],
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



let ctxWithDef = lam ctx. lam def. {ctx with defs = snoc ctx.defs def}

lang WasmCompiler = MClosAst + WasmAST
    sem compileConst : WasmCompileContext -> WasmExprContext -> Const -> WasmExprContext
    sem compileConst globalCtx exprCtx = 
    | CInt {val = i} -> ctxInstrResult exprCtx (I32Const i)

    sem compileExpr : WasmCompileContext -> WasmExprContext -> Expr -> WasmExprContext
    sem compileExpr globalCtx exprCtx = 
    | TmConst {val = c} -> 
        compileConst globalCtx exprCtx c
    | TmVar {ident = ident} ->
        match findFuncDef globalCtx (nameGetStr ident) with Some _
            then never -- todo create closure
            else ctxLocalResult exprCtx (nameGetStr ident)

    sem ctxAcc : WasmCompileContext -> Expr -> WasmCompileContext
    sem ctxAcc globalCtx = 
    | TmFuncDef f -> 
        let args = create (length f.args) 
            (lam i. {ident = concat "arg" (int2string i), 
                     ty = Anyref()}) in 
        let exprCtx = compileExpr globalCtx emptyExprCtx f.body in 
        ctxWithDef globalCtx (FunctionDef {
            ident = nameGetStr  f.funcIdent,
            args = args,
            locals = exprCtx.locals,
            resultTy = Anyref(), 
            instructions = snoc exprCtx.instructions (extractResult exprCtx)
        })
    | _ -> globalCtx

    sem createCtx : [Expr] -> WasmCompileContext
    sem createCtx = 
    | exprs -> foldl ctxAcc emptyCompileCtx exprs
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
let body = (var_ "x") in 
let g = ulet_ "g" (ulam_ "x" (ulam_ "y" body)) in 
let expr = app_ (app_ (var_ "g") (int_ 10)) (int_ 20) in 
let prog = bind_ g expr in 
let transpiled = (use MClosTranspiler in transpile prog) in 
let ctx = createCtx transpiled in 
use WasmPPrint in 
let str = pprintDef 0 (head ctx.defs) in 
printLn str ;
()