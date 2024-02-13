include "mexpr/pprint.mc"
include "mexpr/lamlift.mc"
include "mexpr/lamlift.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/type-lift.mc"
include "mexpr/ast.mc"
include "mexpr/symbolize.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

include "wasm-ast.mc"
include "wasm-pprint.mc"
include "wasm-stdlib.mc"
include "wasm-type-compiler.mc"
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

let fst = lam pair. match pair with (x, _) in x
let snd = lam pair. match pair with (_, x) in x

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

lang WasmCompiler = MClosAst + WasmAST + WasmTypeCompiler + WasmPPrint
    -- sem addType : WasmCompileContext -> (Name, Type) -> WasmCompileContext
    -- sem addType ctx = 
    -- | (name, TyVariant v) ->
    --     let constructors = mapToSeq v.constrs in
    --     let constr2def = lam index. lam constr.
    --         -- let ty = snd constr in 
    --         let kv2field = lam kv.
    --             {ident = nameGetStr (fst kv), ty = Anyref ()} in
    --         let x = printLn (use MExprPrettyPrint in type2str (snd constr)) in
    --         StructTypeDef {
    --             -- ident = join [nameGetStr name, "_", (nameGetStr (fst constr))],
    --             ident = nameGetStr (fst constr),
    --             fields = [{ident = "_typeid", ty = Tyi32 ()}]
    --         } in
    --     let newDefs = mapi constr2def constructors in 
    --     {ctx with defs = concat newDefs ctx.defs}
    -- | (name, other) -> 
    --     printLn (join ["Found other type '", nameGetStr name, "'"]) ;
    --     let x = printLn (use MExprPrettyPrint in type2str other) in
    --     ctx

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
    | TmRecord {bindings = bindings, ty = ty} -> 
        -- We rely on the type lifting pass to have created a type
        -- definition for this TmRecord. 
        -- We then rely on the TypeCompiler to have created a 
        -- struct definition that matches the new of this type def.
        let tyStr = 
            (match ty with TyCon {ident = ident} in nameGetStr ident) in 

        -- TODO: Fix ordering of parameters
        -- Currenlty it is assumed that the order is the same
        -- in the def as in the TmRecord but this is of course
        -- not normally the case.
        let bindingPairs = mapToSeq bindings in 
        let work = lam ctxAccPair. lam pair.
            match ctxAccPair with (ctx, acc) in 
            match pair with (sid, expr) in 
            let ident = sidToString sid in 
            let ctx = compileExpr globalCtx ctx expr in 
            let acc = cons (ident, extractResult ctx) acc in 
            (ctx, acc) in
        match foldl work (exprCtx, []) bindingPairs with (ctx, acc) in 
        let structNewInstr = StructNew {
            structIdent = tyStr,
            values = map snd acc
        } in 
        ctxInstrResult ctx structNewInstr
    | _ -> exprCtx


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

    -- sem compile : [Expr] -> Mod
    sem compile typeEnv =
    | exprs -> 
        -- Add stdlib definitions
        let stdlibDefs = [addiWasm, subiWasm, muliWasm] in 
        let ctx = emptyCompileCtx in
        let ctx = foldl ctxWithFuncDef ctx stdlibDefs in 

        -- Compile Types
        -- let ctx = foldl addType ctx typeEnv in 
        let typeCtx = compileTypes typeEnv in 
        -- iter (lam def. (printLn (pprintDef 0 def))) typeCtx.defs ; 
        let ctx = {ctx with defs = concat ctx.defs typeCtx.defs} in 

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
    use MExprTypeLift in 
    match typeLift ast with (env, ast) in
    -- iter (lam pair. (printLn (nameGetStr (fst pair))) ; 
    --                 (printLn (type2str (snd pair)))) env ;
    -- use MExprPrettyPrint in 
    -- let variantMap = env.variants in 
    -- let variantKVs = mapToSeq variantMap in 
    -- let variants = map fst env in 
    -- let variants = map nameGetStr variants in 
    -- iter (lam kv. printLn (nameGetStr (fst kv)) ; printLn (type2str (snd kv))) env ;
    -- let x = map (lam kv. match kv with (k, v) in printLn (nameGetStr k)) (mapToSeq env.variants) in 
    -- printLn (expr2str ast) ;
    use MClosTranspiler in 
    let exprs = transpile ast in
    use WasmCompiler in 
    let wasmModule = compile env exprs in
    -- wasmModule
    use WasmPPrint in 
    printLn (pprintMod wasmModule) ;
    -- (printLn "Lifted Lambdas: ");
    -- (printLn (use MExprPrettyPrint in expr2str ast));
    -- use MExprClosAst in
    -- let ast =  closureConvert ast in
    -- (printLn (use MExprPrettyPrint in expr2str ast)) ;
    ""

lang TestLang = WasmCompiler + MExprTypeCheck + MExprPrettyPrint +
                WasmPPrint + Sym
end

mexpr
use TestLang in 
-- let variantTyName = nameSym "FooBar" in 
-- let fooName = nameSym "Foo" in 
-- let barName = nameSym "Bar" in 
-- let variant = typeCheck (symbolize (bindall_ [
--     ntype_ variantTyName [] (tyvariant_ []),
--     ncondef_ fooName (tyarrow_ tyint_ (ntycon_ variantTyName)),
--     ncondef_ barName (tyarrow_ tystr_ (ntycon_ variantTyName)),
--     uunit_
-- ])) in 
-- compileMCoreToWasm variant
-- ; 
-- let recordTyName = nameSym "MyRecordType" in 
-- let recordTypeDef = typeCheck (symbolize (bindall_ [
--     ntype_ recordTyName [] (tyrecord_ [("x", tyint_)]),
--     record_
-- ])) in 
let recordExpr = typeCheck (symbolize (
    urecord_ [("x", int_ 10), ("y", int_ 20)]
)) in 
compileMCoreToWasm recordExpr