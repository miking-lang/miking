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

let fst = lam pair. match pair with (x, _) in x
let snd = lam pair. match pair with (_, x) in x

type FunctionSignature = {
    ident: Name,
    arity: Int,
    fp: Int
}

type WasmCompileContext = {
    defs: [(use WasmAST in Def)],
    ident2sig: Map Name FunctionSignature,
    nextFp: Int,
    mainExpr: (use MClosAst in Option Expr),
    constr2typeid: Map Name Int
}

type WasmExprContext = {
    locals: [{ident: Name, ty: (use WasmAST in WasmType)}],
    instructions: [(use WasmAST in Instr)],
    result: Either (use WasmAST in Instr) Name,
    nextLocal: Int
}

let accArity = lam acc: Set Int. lam def: (use WasmAST in Def).
    use WasmAST in 
    match def with FunctionDef funDef
        then setInsert (length funDef.args) acc
        else acc


let findSignature = lam ctx : WasmCompileContext. lam ident : Name. 
    mapLookup ident ctx.ident2sig

let emptyCompileCtx : WasmCompileContext = {
    defs = [],
    ident2sig = mapEmpty nameCmp,
    nextFp = 0,
    mainExpr = None (),
    constr2typeid = mapEmpty nameCmp
}

let emptyExprCtx : WasmExprContext = {
    locals = [],
    instructions = [],
    result = Left (use WasmAST in I31Cast (I32Const 0)), -- This is a temp value, should maybe throw exception.
    nextLocal = 0
}

let extractResult = lam ctx : WasmExprContext.
    use WasmAST in 
    match ctx.result with Left instr
        then instr
        else match ctx.result with Right ident in LocalGet ident

let ctxInstrResult = lam ctx : WasmExprContext . lam instr : (use WasmAST in Instr). 
    {ctx with result = Left instr}

let ctxLocalResult = lam ctx : WasmExprContext. lam ident : Name. 
    {ctx with result = Right ident}

let ctxWithSignature = lam ctx. lam ident. lam arity. 
    let sig = {
        ident = ident,
        arity = arity,
        fp = ctx.nextFp
    } in 
    {ctx with 
        ident2sig = mapInsert ident sig ctx.ident2sig,
        nextFp = addi 1 ctx.nextFp}

let ctxWithSignatureWasmDef = lam ctx. lam def. 
    use WasmAST in 
    match def with FunctionDef f in 
    ctxWithSignature ctx (f.ident) (length f.args)

let ctxWithSignatureMExprDef = lam ctx. lam expr.
    use MClosAst in 
    match expr with TmFuncDef f 
        then ctxWithSignature ctx (f.funcIdent) (length f.args)
        else ctx


let ctxWithFuncDef = lam ctx. lam def. 
    {ctx with defs = snoc ctx.defs def}

let createClosureStruct = lam arity: Int. lam fp: Int. 
    use WasmAST in 
    let closure = StructNew {
        structIdent = nameNoSym "clos",
        values = [
            I32Const fp,
            I32Const arity,
            I32Const 0,
            ArrayNew {
                tyIdent = nameNoSym "args-array",
                initValue = GlobalGet (nameNoSym "null-like"),
                size = I32Const arity
            }
        ]
    } in 
    match arity with 0
        then Call (nameNoSym "exec-0", [closure])
        else closure

let createClosure = lam globalCtx: WasmCompileContext. lam exprCtx. lam ident: Name.
    use WasmAST in 
    match findSignature globalCtx ident with Some sig
        then 
            ctxInstrResult exprCtx (createClosureStruct sig.arity sig.fp) 
        else 
            error (join ["Identifier '", nameGetStr ident, "' is not a function!"])

let createArithOpClosure = lam globalCtx. lam exprCtx. lam opIdent. 
    use WasmAST in 
    createClosure globalCtx exprCtx opIdent

lang WasmCompiler = MClosAst + WasmAST + WasmTypeCompiler + WasmPPrint
    sem compileConst : WasmCompileContext -> WasmExprContext -> Const -> WasmExprContext
    sem compileConst globalCtx exprCtx = 
    | CInt {val = i} -> ctxInstrResult exprCtx (I31Cast (I32Const i))
    -- Integer Arithmatic Operators
    | CAddi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "addi")
    | CMuli _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "muli")
    | CSubi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "subi")
    | CDivi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "divi")
    | CModi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "modi")
    | CNegi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "negi")
    | CSlli _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "slli")
    | CSrli _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "srli")
    | CSrai _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "srai")
    -- Integers Comparison Operators
    | CEqi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "eqi")
    | CNeqi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "neqi")
    | CLti _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "lti")
    | CGti _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "gti")
    | CLeqi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "leqi")
    | CGeqi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "geqi")

    sem compileExpr : WasmCompileContext -> WasmExprContext -> Expr -> WasmExprContext
    sem compileExpr globalCtx exprCtx = 
    | TmConst {val = c} -> 
        compileConst globalCtx exprCtx c
    | TmVar {ident = ident} ->
        match findSignature globalCtx ident with Some _
            then
                createClosure globalCtx exprCtx ident
            else 
                ctxLocalResult exprCtx ident
    | TmApp {lhs = lhs, rhs = rhs} ->
        let leftCtx = compileExpr globalCtx exprCtx lhs in 
        let rightCtx = compileExpr globalCtx leftCtx rhs in 
        let applyInstr = Call (nameNoSym "apply", [
            extractResult leftCtx,
            extractResult rightCtx
        ]) in 
        ctxInstrResult rightCtx applyInstr
    | TmRecord {bindings = bindings, ty = ty} -> 
        match mapIsEmpty bindings with true
            then ctxInstrResult exprCtx (GlobalGet (nameNoSym "null-like"))
            else 
                -- We rely on the type lifting pass to have created a type
                -- definition for this TmRecord. 
                -- We then rely on the TypeCompiler to have created a 
                -- struct definition that matches the new of this type def.
                let tyStr = (match ty with TyCon {ident = ident} in ident) in 

                -- The fields are ordered by the SID of the field identifiers
                let bindingPairs = mapToSeq bindings in 
                -- We reverse because we accumulate in the fold later which
                -- reverses the order.
                let bindingPairs = reverse (sort
                    (lam p1. lam p2. match p1 with (sid1, _) in match p2 with (sid2, _) in cmpSID sid1 sid2)
                    bindingPairs)
                in

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
    | TmConApp r ->
        let exprCtx = compileExpr globalCtx exprCtx r.body in 
        let structIdent = r.ident in 
        let typeid = 
            (match mapLookup r.ident globalCtx.constr2typeid with Some t in t) in 
        ctxInstrResult exprCtx (StructNew {
            structIdent = structIdent,
            values = [
                extractResult exprCtx,
                I32Const typeid
            ]
        })
    | TmMatch r -> 
        let targetCtx = compileExpr globalCtx exprCtx r.target in 
        let patCtx = compilePat globalCtx exprCtx (extractResult targetCtx) r.pat in
        let thnCtx = compileExpr globalCtx {patCtx with instructions = []} r.thn in 
        let elsCtx = compileExpr globalCtx {thnCtx with instructions = []} r.els in 

        let resultLocalIdent = nameNoSym (concat "match-result" (int2string elsCtx.nextLocal)) in 

        let result = {patCtx with 
            nextLocal = addi elsCtx.nextLocal 1,
            locals = cons 
                {ident = resultLocalIdent, ty = Anyref ()}
                elsCtx.locals ,
            instructions = snoc patCtx.instructions (IfThenElse {
                cond = extractResult patCtx,
                thn = concat 
                    thnCtx.instructions 
                    [LocalSet (resultLocalIdent, extractResult thnCtx)],
                els = concat 
                    elsCtx.instructions 
                    [LocalSet (resultLocalIdent, extractResult elsCtx)]
            })} in 
        ctxLocalResult result resultLocalIdent
    | _ -> exprCtx

    -- sem compilePat : WasmCompileContext -> WasmExprContext -> Pat -> WasmExprContext
    sem compilePat globalCtx ctx targetInstr = 
    | PatNamed {ident = PWildcard ()} -> 
        -- print "PatNamed PWildcard";
        ctxInstrResult ctx (I32Const 1)
    | PatNamed {ident = PName name} ->
        let ident = nameGetStr name in 
        -- print "PatNamed PName" ;
        -- printLn ident ;
        ctxInstrResult ctx (I32Const 1)
    | PatInt {val = val} ->
        let eqInstr = I32Eq (
            I32Const val,
            I31GetS (RefCast {
                ty = I31Ref (),
                value = targetInstr
            })
        ) in
        ctxInstrResult ctx eqInstr
    | PatCon {ident = ident, subpat = PatNamed {ident = PName innerName}} ->
        let structIdent = ident in 
        let typeid = (match mapLookup ident globalCtx.constr2typeid with Some t in t) in 

        let refTest = RefTest {
            ty = Ref structIdent,
            value = targetInstr
        } in 

        let typeidTest = I32Eq (
            I32Const typeid, 
            StructGet {
                structIdent = structIdent,
                field = nameNoSym "_typeid",
                value = RefCast {
                    ty = Ref structIdent,
                    value = targetInstr
                }
            }
        ) in 

        let innerIdent = innerName in 
        let setInnerIdent = LocalSet (
            innerIdent,
            StructGet {
                structIdent = structIdent,
                field = nameNoSym "value",
                value = RefCast {
                    ty = Ref structIdent,
                    value = targetInstr
                }
            }
        ) in 

        let resultLocal = nameNoSym (concat "patcon" (int2string ctx.nextLocal)) in 

        let setResultLocal = lam i. LocalSet (resultLocal, I32Const i) in 

        let ite = IfThenElse {
            cond = refTest,
            thn = [IfThenElse {
                cond = typeidTest,
                thn = [setResultLocal 1, setInnerIdent],
                els =[setResultLocal 0]
            }],
            els = [setResultLocal 0]
        } in 

        let ctx = {ctx with
            locals = concat
                [
                    {ident = resultLocal, ty = Tyi32 ()}, 
                    {ident = innerIdent, ty = Anyref ()}
                ]
                ctx.locals,
            nextLocal = addi 1 ctx.nextLocal,
            instructions = cons ite ctx.instructions} in  

        ctxLocalResult ctx resultLocal
    | PatRecord {bindings = bindings, ty = ty} ->
        let bindingPairs = mapToSeq bindings in 
        -- let updatename2ident = lam ctx. lam i. lam pair. 
        --     match pair with (_, pat) in
        --     match pat with PatNamed {ident = PName name} in
        --     let uniqueIdent = concat (nameGetStr name) (int2string i) in 
        --     {ctx with name2ident = mapInsert name uniqueIdent ctx.name2ident} in
        -- let ctx = foldli updatename2ident ctx bindingPairs in 
        let tyStr = (match ty with TyCon {ident = ident} in ident) in 

        let pair2localIdent = lam index. lam pair. 
            match pair with (_, pat) in 
            match pat with PatNamed {ident = PName innerName} in
            {ident = innerName, ty = Anyref ()} in 
        let locals = mapi pair2localIdent bindingPairs in 
        let pair2setIntruction = lam index. lam pair.
            match pair with (sid, pat) in 
            match pat with PatNamed {ident = PName innerName} in 
            let structFieldIdent = nameNoSym (sidToString sid) in 
            let localIdent = innerName in 
            LocalSet (localIdent, StructGet {
                structIdent = tyStr,
                field = structFieldIdent, 
                value = RefCast {
                    ty = Ref tyStr,
                    value = targetInstr
                } 
            }) in 
        let localSetters = mapi pair2setIntruction bindingPairs in 
        let ctx = {ctx with 
            locals = concat ctx.locals locals,
            instructions = concat ctx.instructions localSetters} in 
        ctxInstrResult ctx (I32Const 1)

    sem compileFunction : WasmCompileContext -> Expr -> WasmCompileContext
    sem compileFunction globalCtx = 
    | TmFuncDef f -> 
        let args = map (lam arg. {ident = arg.ident, ty = Anyref()}) f.args in
        let exprCtx = compileExpr globalCtx emptyExprCtx f.body in 
        ctxWithFuncDef globalCtx (FunctionDef {
            ident = f.funcIdent,
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
                    value = extractResult exprCtx
                 }) in
                let funcDef = (FunctionDef {
                    ident = nameNoSym "mexpr",
                    args = [],
                    locals = exprCtx.locals,
                    resultTy = Tyi32 (), 
                    instructions = snoc exprCtx.instructions resultExpr
                }) in 
                let globalCtx = ctxWithSignatureWasmDef globalCtx funcDef in 
                ctxWithFuncDef globalCtx funcDef

    -- sem compile : [Expr] -> Mod
    sem compile typeEnv =
    | exprs -> 
        -- Add stdlib definitions
        let stdlibDefs = integerIntrinsics in 
        let ctx = emptyCompileCtx in
        let ctx = foldl ctxWithSignatureWasmDef ctx stdlibDefs in 
        let ctx = foldl ctxWithFuncDef ctx stdlibDefs in 

        -- Compile Types
        let typeCtx = compileTypes typeEnv in 
        let ctx = 
            {ctx with 
                defs = concat ctx.defs typeCtx.defs,
                constr2typeid = typeCtx.constr2typeid} in 

        -- Add function signature to ctx *before* compilation
        -- to support (mutual) recursion
        let ctx = foldl ctxWithSignatureMExprDef ctx exprs in

        -- Compile functions
        let ctx = foldl compileFunction ctx exprs in 

        -- Add apply, exec and dispatch based on aritites
        let arities = foldl accArity (setEmpty subi) ctx.defs in 
        let arities = setToSeq arities in 
        let genericTypes = map genGenericType arities in 
        let execs = map genExec arities in 
        let dispatch = genDispatch arities in 
        let ctx = {ctx with
            defs = join [[argsArrayType, closDef, nullLikeDef], genericTypes, execs, [dispatch, apply], ctx.defs]
        } in 

        -- Sort function names by function pointer so they can be added
        -- to the 'elem' instruction in the proper order.
        let name2sigPairs = mapToSeq ctx.ident2sig in 
        let name2fpPairs = map (lam ns. match ns with (n, s) in (n, s.fp)) name2sigPairs in 
        let sortedKVs = sort (tupleCmp2 (lam s1. lam s2. 0) subi) name2fpPairs in
        let sortedNames = map (lam kv. match kv with (k, v) in k) sortedKVs in 

        Module {
            definitions = ctx.defs,
            table = Table {size = mapSize ctx.ident2sig, typeString = "funcref"},
            elem = Elem {offset = I32Const 0, funcNames = sortedNames},
            types = [],
            exports = [nameNoSym "mexpr"]
        }
end

let compileMCoreToWasm = lam ast.
    use MExprLowerNestedPatterns in 
    let ast = lowerAll ast in 
    use MExprLambdaLift in
    let ast = liftLambdas ast in
    use MExprTypeLift in 
    match typeLift ast with (env, ast) in

    -- (use MClosPrettyPrint in printLn (expr2str ast) );

    use MClosTranspiler in 
    let exprs = transpile ast in

    -- (use MClosPrettyPrint in (iter (lam e. printLn (expr2str e)) exprs));

    use WasmCompiler in 
    let wasmModule = compile env exprs in
    -- wasmModule
    use WasmPPrint in 
    printLn (pprintMod wasmModule) ;
    ""

lang TestLang = WasmCompiler + MExprTypeCheck + MExprPrettyPrint +
                WasmPPrint + Sym
end

mexpr
use TestLang in 
-- let variantTyName = nameSym "FooBar" in 
-- let iName = nameSym "i" in 
-- let fooName = nameSym "Foo" in 
-- let barName = nameSym "Bar" in 
-- let target = (nconapp_ fooName (int_ 12)) in 
-- let pat = npcon_ fooName (npvar_ iName) in 
-- let thn = nvar_ iName in 
-- let els = int_ -1 in 
-- let matchExpr = typeCheck (symbolize (
--     match_ target pat thn els
-- )) in 
-- let expr = typeCheck (symbolize (bindall_ [
--     ntype_ variantTyName [] (tyvariant_ []),
--     ncondef_ fooName (tyarrow_ tyint_ (ntycon_ variantTyName)),
--     ncondef_ barName (tyarrow_ tyint_ (ntycon_ variantTyName)),
--     uunit_
--     -- (ulet_ "f" (nconapp_ fooName (int_ 12))),
--     -- (ulet_ "g" (nconapp_ barName (int_ 42))),
--     -- matchExpr
-- ])) in 

-- compileMCoreToWasm variant
-- ; 
let target = urecord_ [("x", int_ 23), ("y", int_ 42)] in
let pat = PatRecord {
    bindings = mapFromSeq cmpSID [
        -- (stringToSid "x", PatNamed {ident = PName (nameNoSym "foo"), info=NoInfo(), ty = tyunknown_})
        (stringToSid "x", npvar_ (nameNoSym "foo")),
        (stringToSid "y", npvar_ (nameNoSym "bar"))
        -- (stringToSid "x", pint_ 25),
        -- (stringToSid "y", pint_ 25)
    ],
    info = NoInfo (),
    ty = TyUnknown {info = NoInfo()}
} in 
let thn = addi_ (nvar_ (nameNoSym "bar")) (nvar_ (nameNoSym "foo")) in 
-- let thn = int_ 1 in 
let els = int_ (-1) in 
let expr = match_ target pat thn els in 
compileMCoreToWasm target