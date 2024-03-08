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
include "bool.mc"
include "seq.mc"
include "map.mc"
include "tuple.mc"
include "stringid.mc"

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
    constr2typeid: Map Name Int,
    globalInitDefs: [(use WasmAST in Def)],
    record2fields: Map Name [Name]
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

let isLocal = lam ctx : WasmExprContext. lam ident : Name. 
    let idents = map (lam local. local.ident) ctx.locals in 
    match find (nameEq ident) idents with Some _ then true else false

let isGlobal = lam ctx : WasmCompileContext. lam ident: Name. 
    use WasmAST in 
    let globalDefs = filter 
        (lam d. match d with GlobalDef _ then true else false)
        ctx.defs in 
    let globalNames = map (lam d. match d with GlobalDef g in g.ident) globalDefs in 
    match find (nameEq ident) globalNames with Some _ then true else false

let emptyCompileCtx : WasmCompileContext = {
    defs = [],
    ident2sig = mapEmpty nameCmp,
    nextFp = 0,
    mainExpr = None (),
    constr2typeid = mapEmpty nameCmp,
    globalInitDefs = [],
    record2fields = mapEmpty nameCmp
}

let emptyExprCtx : WasmExprContext = {
    locals = [],
    instructions = [],
    result = Left (use WasmAST in I31Cast (I32Const 0)), -- This is a temp value, should maybe throw exception.
    nextLocal = 0
}

let mapiOption
  : all a. all b.
     (Int -> a -> Option b)
  -> [a]
  -> [b]
  = lam f.
    recursive let work = lam i. lam as.
      match as with [a] ++ as then
        match f i a with Some b
        then cons b (work (addi 1 i) as)
        else work (addi 1 i) as
      else []
    in work 0

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

lang WasmCompiler = MClosAst + WasmAST + WasmTypeCompiler + WasmPPrint + MClosPrettyPrint
    sem compileConst : WasmCompileContext -> WasmExprContext -> Const -> WasmExprContext
    sem compileConst globalCtx exprCtx = 
    | CInt {val = i} -> ctxInstrResult exprCtx (I31Cast (I32Const i))
    | CBool {val = true} -> ctxInstrResult exprCtx (I31Cast (I32Const 1))
    | CBool {val = false} -> ctxInstrResult exprCtx (I31Cast (I32Const 0))
    | CChar {val = c} -> ctxInstrResult exprCtx (I31Cast (I32Const (char2int c)))
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
    -- Floating Point Comparison Operators (WIP)
    | CEqf _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "eqf")
    | CFloat2string _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "id")
    -- Character Operations
    -- Since characters are represented as i31, we simply re-use the integer ops
    | CEqc _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "eqi")
    | CInt2Char _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "id")
    | CChar2Int _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "id")
    -- Sequence Operations
    | CHead _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "head")
    | CTail _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "tail")
    | CCons _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "cons")
    | CSnoc _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "snoc")
    | CConcat _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "concat")
    | CLength _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "length")
    | CGet _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "get")
    | CSet _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "set")
    | CReverse _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "reverse")
    | CSubsequence _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "subsequence")
    | CCreate _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "create")
    | CNull _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "null")
    | CIter _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "iter")
    | CIteri _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "iteri")
    | CMap _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "map")
    | CMapi _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "mapi")
    | CFoldl _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "foldl")
    | CFoldr _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "foldr")
    | CSplitAt _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "splitat")
    -- Since we only have ropes, we can not create lists. Therefore we 
    -- simply say that ropes are also lists. Creating a rope or list is then
    -- just the identity operation.
    | CCreateRope _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "id")
    | CCreateList _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "id")
    | CIsList _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "const-true")
    | CIsRope _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "const-true")

    -- Refererence Operations
    | CRef _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "ref")
    | CDeRef _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "deref")
    | CModRef _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "modref")
    -- IOAST 
    | CPrint _ -> createArithOpClosure globalCtx exprCtx (nameNoSym "print")
    | CExit _ -> ctxInstrResult exprCtx (Unreachable ())
    -- Fallback
    | other -> ctxInstrResult exprCtx (Unreachable ())
    sem compileExpr : WasmCompileContext -> WasmExprContext -> Expr -> WasmExprContext
    sem compileExpr globalCtx exprCtx = 
    | TmConst {val = c} -> 
        compileConst globalCtx exprCtx c
    | TmVar {ident = ident} ->
        match findSignature globalCtx ident with Some _
            then
                createClosure globalCtx exprCtx ident
            else 
                if isGlobal globalCtx ident then
                    ctxInstrResult exprCtx (GlobalGet ident)
                else 
                    -- if isLocal exprCtx ident then 
                        ctxLocalResult exprCtx ident
                    -- else 
                    --     let nameStr = pprintName ident in 
                    --     error (join [
                    --         "TmVar '",
                    --         nameStr,
                    --         "' is not a signature, global or local!"
                    --     ])
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
    | TmRecordUpdate {rec = r, key = key, value = value, ty = ty} -> 
        let tyStr = (match ty with TyCon {ident = ident} in ident) in 

        -- We assume that the fields are already sorted by SID
        let fields = 
            (match mapLookup tyStr globalCtx.record2fields with Some f in f) in
        
        let valueCtx = compileExpr globalCtx exprCtx value in 

        let rIdent = nameSym "r" in
        let rCtx = compileExpr globalCtx valueCtx r in 

        let field2instr = lam field. 
            if eqString (nameGetStr field) (sidToString key) then
                extractResult valueCtx
            else
                StructGet {
                    structIdent = tyStr,
                    field = field,
                    value = LocalGet rIdent
                }
        in 

        let newStruct = StructNew {
            structIdent = tyStr,
            values = map field2instr fields
        } in 

        {rCtx with 
            instructions = snoc
                rCtx.instructions
                (LocalSet (rIdent, RefCast {
                    ty = Ref tyStr,
                    value = extractResult rCtx
                })),
            locals = snoc rCtx.locals {ident = rIdent, ty = Ref tyStr},
            result = Left newStruct
        }
    | TmSeq {tms = tms} -> 
        let localName = nameSym "arr" in
        let sizeInstr = I32Const (length tms) in 
        let local = {ident = localName, ty = Ref argsArrayName} in 
        let exprCtx = {exprCtx with locals = cons local exprCtx.locals} in 
        let initLocal = LocalSet (localName, ArrayNew {
            tyIdent = argsArrayName,
            initValue = I31Cast (I32Const 0),
            size = sizeInstr
        }) in 
        let exprCtx = {exprCtx with instructions = snoc exprCtx.instructions initLocal} in 
        let work = lam ctx. lam i. lam tm. 
            let ctx = compileExpr globalCtx ctx tm in 
            let arraySet = ArraySet {
                tyIdent = argsArrayName,
                value = LocalGet localName,
                index = I32Const i,
                value2 = extractResult ctx
            } in 
            let ctx = {ctx with instructions = snoc ctx.instructions arraySet} in 
            ctxInstrResult ctx (Unreachable())
        in 
        let ctx = foldli work exprCtx tms in 
        ctxInstrResult ctx (StructNew {
            structIdent = leafName,
            values = [
                sizeInstr,
                LocalGet localName
            ]
        })
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
    | TmLet {ident = ident, body = body, inexpr = inexpr} -> 
        let bodyCtx = compileExpr globalCtx exprCtx body in 
        let setLocal = LocalSet (ident, extractResult bodyCtx) in 
        let newCtx = {bodyCtx with 
            locals = cons {ident = ident, ty = Anyref ()} bodyCtx.locals,
            instructions = snoc bodyCtx.instructions setLocal
        } in 
        compileExpr globalCtx newCtx inexpr
    | TmNever _ ->
        ctxInstrResult exprCtx (Unreachable ())
    | TmUtest {test = lhs, expected = rhs, next = next} ->
        error "TmUtest is not supported!"
        -- let leftCtx = compileExpr globalCtx exprCtx lhs in 
        -- let rightCtx = compileExpr globalCtx leftCtx rhs in 
        -- let ite = IfThenElse {
        --     cond = I32Eq (
        --         anyref2i32 (extractResult leftCtx),
        --         anyref2i32 (extractResult rightCtx)
        --     ),
        --     thn = [Call (nameNoSym "utestSucc", [])],
        --     els = [Call (nameNoSym "utestFail", [])]
        -- } in 
        -- let ctx = {rightCtx with instructions = snoc rightCtx.instructions ite} in
        -- compileExpr globalCtx ctx next

    | other -> error "Unsupported Expression!"
        -- error (concat 
        --     "Enountered unsupported expression: " 
        --     (use MExprPrettyPrint in expr2str other))

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
    | PatBool {val = true} -> 
        let eqInstr = I32Ne (
            I32Const 0,
            I31GetS (RefCast {
                ty = I31Ref (),
                value = targetInstr
            })
        ) in 
        ctxInstrResult ctx eqInstr
    | PatBool {val = false} -> 
        let eqInstr = I32Eq (
            I32Const 0,
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
    | PatRecord {bindings = bindings, ty = ty} & x->
        let bindingPairs = mapToSeq bindings in 

        let pair2localIdent = lam index. lam pair. 
            match pair with (_, pat) in 
            match pat with PatNamed {ident = PName innerName} in
            {ident = innerName, ty = Anyref ()} in 
        let locals = mapi pair2localIdent bindingPairs in 
        -- This is a bit of a hack needed for pattern matching
        -- This uses split-at which created a 2-tuple which
        -- is not caught by the type lifting!
        let tyStr = (match ty with TyCon {ident = ident} 
            then ident
            else nameNoSym "split-2-tuple") in 

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
    | PatSeqTot {pats = pats} ->
        let n = nameSym "n" in 
        let result = nameSym "result" in 

        let pat2ident = lam pat. 
            match pat with PatNamed {ident = PName (ident)}
                then Some (ident)
                else None ()
        in
        let localIdents = mapOption pat2ident pats in 
        let locals = concat
            [{ident = n, ty = Tyi32 ()}, {ident = result, ty = Tyi32()}]
            (map (lam ident. {ident = ident, ty = Anyref ()}) localIdents) 
        in 

        let pat2localSetter = lam setters. lam i. lam pat. 
            match pat with PatNamed {ident = PName (ident)}
                then cons 
                    (LocalSet (ident, Call (nameNoSym "get", [targetInstr, I31Cast (I32Const i)])))
                    setters
                else setters
        in
        let localSetters = foldli pat2localSetter [] pats in 

        let ctx = {ctx with
            locals = concat ctx.locals locals,
            instructions = [
                LocalSet (n, I31GetU (
                    RefCast {
                        ty = I31Ref (),
                        value = Call (nameNoSym "length", [targetInstr])
                    }
                )),
                IfThenElse {
                    cond = I32Eq (
                        LocalGet n,
                        I32Const (length pats)
                    ),
                    thn = cons (LocalSet (result, I32Const 1))localSetters,
                    els = [LocalSet (result, I32Const 0)]
                }

            ]
        } in 
        ctxLocalResult ctx result
    | PatSeqEdge {prefix = prefix, middle = middle, postfix = postfix} ->
        -- After the 'shallow-pattern' transformation there are 2 possible patterns
        -- of this type:
        -- 1) If the pattern was already shallow (so every sub-pattern is a PatNamed),
        --    the transformation leads the pattern untouched.
        -- 2) If the pattern was not shallow, it is transformed into a 
        --    nested structure. The PatSeqEdge will always be in the form of:
        --    [_, ..., _] ++ _ ++ [] and therefore be replaced by a simple
        --    check: length(target) >= len(prefix) 

        let patNameIsWildCard = lam pn .
            match pn with PWildcard _ then true else false
        in

        let patIsWildCard = lam pat. 
            match pat with PatNamed {ident = PWildcard _} then true else false
        in

        let lenInstr = I31GetU (
            RefCast {
                ty = I31Ref (),
                value = Call (nameNoSym "length", [targetInstr])
            }
        ) in 

        if and (and (forAll patIsWildCard prefix) (null postfix)) (patNameIsWildCard middle) then
            -- The pattern was not already shallow so it has now been transformed
            -- by the 'lowerAll' transformation to a pattern in the form of
            -- [_, ..., _] ++ _ ++ []
            ctxInstrResult ctx (I32LeS (I32Const (length prefix), lenInstr))
        else
            let flatIdent = nameSym "flat" in 
            let flatLocal = {ident = flatIdent, ty = Anyref ()} in 
            let setFlat = LocalSet (flatIdent, Call(nameNoSym "_flatten-rope", [targetInstr])) in 

            let resultIdent = nameSym "res" in 
            let resultLocal = {ident = resultIdent, ty = Tyi32 ()} in 

            let pat2local = lam pat. 
                match pat with PatNamed {ident = PName ident} 
                    then Some {ident = ident, ty = Anyref ()}
                    else None ()
            in 
            let patternLocals = mapOption pat2local (concat prefix postfix) in

            let pat2prefixSetter = lam i. lam pat.
                match pat with PatNamed {ident = PName ident} 
                    then Some (LocalSet (ident, Call (nameNoSym "get", [
                        LocalGet flatIdent,
                        I31Cast (I32Const i)
                    ])))
                    else None ()
            in
            let prefixSetters = mapiOption pat2prefixSetter prefix in 
            let pat2postFixSetter = lam i. lam pat.
                match pat with PatNamed {ident = PName ident} 
                    then Some (LocalSet (ident, Call (nameNoSym "get", [
                        LocalGet flatIdent,
                        I31Cast (I32Sub(lenInstr, I32Const (addi i 1)))
                    ])))
                    else None ()
            in
            let postfixSetters = mapiOption pat2postFixSetter postfix in 

            let midLocals = match middle with PName ident then [{ident = ident, ty = Anyref ()}] else [] in 
            let newLocals = join [
                patternLocals,
                midLocals,
                [resultLocal, flatLocal]
            ] in 

            let midSetters = match middle with PName ident 
                then [LocalSet (ident, Call (nameNoSym "subsequence", [
                    LocalGet flatIdent,
                    I31Cast (I32Const (length prefix)),
                    I31Cast (I32Sub (
                        lenInstr,
                        I32Const (length postfix)
                    ))]))]
                else []
            in


            let ite = IfThenElse {
                cond = I32LeS (I32Const (addi (length prefix) (length postfix)), lenInstr),
                thn = join [
                    [
                        LocalSet (resultIdent, I32Const 1),
                        setFlat
                    ],
                    prefixSetters,
                    midSetters,
                    postfixSetters
                ],
                els = [
                    LocalSet (resultIdent, I32Const 0)
                ]
            } in 

            {ctx with 
                instructions = snoc ctx.instructions ite,
                locals = concat newLocals ctx.locals,
                result = Right resultIdent}
    | _ -> error "Missing pattern"

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
    | _ -> error "Expected TmFuncDef when compiling function definitions!"

    sem compileInitGlobals: WasmCompileContext -> {ident: Name, value: Expr} -> WasmCompileContext
    sem compileInitGlobals ctx =
    | glob -> 
        match glob with {ident = ident, value = value} in 
        let globalDef = GlobalDef {
            ident = ident,
            ty = Mut (Anyref ()),
            initValue = RefNull "i31"
        } in 
        let initIdent = nameSym (concat "init-" (nameGetStr ident)) in 
        let bodyCtx = compileExpr ctx emptyExprCtx value in 
        let setGlobal = GlobalSet (ident, extractResult bodyCtx) in 
        let initDef = FunctionDef {
            ident = initIdent,
            args = [],
            locals = bodyCtx.locals,
            resultTy = Anyref (),
            instructions = concat bodyCtx.instructions [setGlobal, GlobalGet ident]
        } in 
        {ctx with
            defs = cons globalDef ctx.defs,
            globalInitDefs = snoc ctx.globalInitDefs initDef}

    sem compileMainExpr : WasmCompileContext -> Expr -> WasmCompileContext
    sem compileMainExpr globalCtx = 
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
                let globalDef2call = lam def.
                    match def with FunctionDef f in 
                    Drop (Call (f.ident, []))
                in 
                let globalInits = map globalDef2call globalCtx.globalInitDefs in 
                let funcDef = (FunctionDef {
                    ident = nameNoSym "mexpr",
                    args = [],
                    locals = exprCtx.locals,
                    resultTy = Tyi32 (), 
                    instructions = concat globalInits (snoc exprCtx.instructions resultExpr)
                }) in 
                let globalCtx = ctxWithSignatureWasmDef globalCtx funcDef in 
                ctxWithFuncDef globalCtx funcDef

    -- sem compile : [Expr] -> Mod
    sem compile typeEnv =
    | transpileEnv -> 
        -- Add integer stdlib definitions
        let stdlibDefs = integerIntrinsics in 
        let ctx = emptyCompileCtx in
        let ctx = foldl ctxWithSignatureWasmDef ctx stdlibDefs in 
        let ctx = foldl ctxWithFuncDef ctx stdlibDefs in 

        -- Add list stdlib definitions
        let ctx = foldl ctxWithFuncDef ctx [anyrefArrDef, leafDef, sliceDef, concatDef, anyrefBoxDef] in 

        -- Compile Types
        let typeCtx = compileTypes typeEnv in 
        let ctx = 
            {ctx with 
                record2fields = typeCtx.record2fields,
                defs = concat ctx.defs typeCtx.defs,
                constr2typeid = typeCtx.constr2typeid} in 

        -- Add function signature to ctx *before* compilation
        -- to support (mutual) recursion
        let ctx = foldl ctxWithSignatureMExprDef ctx transpileEnv.functionDefs in

        -- Compile Globals
        let ctx = foldl compileInitGlobals ctx transpileEnv.globals in

        -- Compile functions
        let ctx = foldl compileFunction ctx transpileEnv.functionDefs in 

        let ctx = (match transpileEnv.mainExpr with Some mainExpr 
            then compileMainExpr ctx mainExpr
            else error "Unable to compile a MExpr program without a main expression!")
        in

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
            definitions = concat ctx.defs ctx.globalInitDefs,
            table = Table {size = mapSize ctx.ident2sig, typeString = "funcref"},
            elem = Elem {offset = I32Const 0, funcNames = sortedNames},
            types = [],
            imports = [
                {
                    jsObjIdent="imports", 
                    jsFieldIdent="utestSuccess", 
                    wasmIdent=nameNoSym "utestSucc",
                    paramTys=[]
                },
                {
                    jsObjIdent="imports",
                    jsFieldIdent="utestFailure",
                    wasmIdent=nameNoSym "utestFail",
                    paramTys=[]
                },
                {
                    jsObjIdent="imports",
                    jsFieldIdent="callPrintJS",
                    wasmIdent=nameNoSym "callPrintJS",
                    paramTys=[Tyi32 ()]
                }
            ],
            memory = Memory {n = 1},
            exports = [
                FunctionExport {ident = nameNoSym "mexpr"},
                MemoryExport {ident = nameNoSym "printmemory", n = 0}
            ]
        }
end

let compileMCoreToWasm = lam ast.
    -- use MExprLowerNestedPatterns in 
    -- let ast = lowerAll ast in 

    -- printLn "=== PATTERNS LOWERED ===" ;
    -- (use MClosPrettyPrint in printLn (expr2str ast) );

    use MExprLambdaLift in
    let ast = liftLambdas ast in

    -- printLn "=== LAMBDA LIFTED ===" ;
    -- (use MClosPrettyPrint in printLn (expr2str ast) );

    use MExprTypeLift in 
    match typeLift ast with (env, ast) in

    -- printLn "=== TYPE LIFTED ===" ;
    -- (use MClosPrettyPrint in printLn (expr2str ast) );

    use MClosTranspiler in 
    let transpileCtx = transpile ast in

    -- printLn "=== TRANSPILED ===" ;
    -- (use MClosPrettyPrint in (iter (lam e. printLn (expr2str e)) transpileCtx.functionDefs));

    use WasmCompiler in 
    let wasmModule = compile env transpileCtx in
    use WasmPPrint in 
    printLn (pprintMod wasmModule) ;
    ""

lang TestLang = WasmCompiler + MExprTypeCheck + MExprPrettyPrint +
                WasmPPrint + Sym
end

mexpr
use TestLang in 
-- compileMCoreToWasm (utest_ (addi_ (int_ 3) (int_ 4)) (int_ 7) uunit_)
-- compileMCoreToWasm (get_ (snoc_ (cons_ (int_ 42) (seq_ [int_ 1, int_ 2, int_ 3])) (int_ 23)) (int_ 4))
-- compileMCoreToWasm (get_ (concat_ (seq_ [int_ 4, int_ 5]) (seq_ [int_ 1, int_ 2, int_ 3])) (int_ 2))
-- compileMCoreToWasm (head_ (tail_ (tail_ (seq_ [int_ 1, int_ 2, int_ 3]))))
compileMCoreToWasm (head_ (reverse_ (concat_ (seq_ [int_ 1, int_ 2, int_ 3]) (seq_ [int_ 4, int_ 5, int_ 6]))))