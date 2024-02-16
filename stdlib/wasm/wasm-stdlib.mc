include "wasm-ast.mc"
include "wasm-pprint.mc"


-- Integer Operations
let createIntBinop = lam ident. lam instrProducer.
    use WasmAST in 
    FunctionDef {
        ident = (nameNoSym ident),
        args = [
            {ident=(nameNoSym "lhs"), ty=Anyref ()},
            {ident=(nameNoSym "rhs"), ty=Anyref()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                instrProducer 
                    (I31GetS (RefCast {ty = I31Ref (), value = LocalGet (nameNoSym "lhs")}))
                    (I31GetS (RefCast {ty = I31Ref(), value = LocalGet (nameNoSym "rhs")}))
            )
        ]
    }

let addiWasm = 
    use WasmAST in 
    createIntBinop "addi" (lam l. lam r. I32Add (l, r))

let subiWasm = 
    use WasmAST in 
    createIntBinop "subi" (lam l. lam r. I32Sub (l, r))

let muliWasm = 
    use WasmAST in 
    createIntBinop "muli" (lam l. lam r. I32Mul (l, r))

let diviWasm = 
    use WasmAST in 
    createIntBinop "divi" (lam l. lam r. I32DivS (l, r))

let modiWasm = 
    use WasmAST in 
    createIntBinop "modi" (lam l. lam r. I32RemS (l, r))

let negiWasm = 
    use WasmAST in 
    FunctionDef {
        ident = (nameNoSym "negi"),
        args = [
            {ident=(nameNoSym "arg"), ty=Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                I32Sub (
                    I32Const 0,
                    (I31GetS (RefCast {ty = I31Ref(), value = LocalGet (nameNoSym "arg")}))
                )
            )
        ]
    }

-- slli = shift left logical integer
let slliWasm =
    use WasmAST in 
    createIntBinop "slli" (lam l. lam r. I32Shl (l, r))

-- TODO: Test difference between srli and srai. 
-- srli = shift right logical integer
let srliWasm =
    use WasmAST in 
    createIntBinop "srli" (lam l. lam r. I32ShrU (l, r))

-- srai = shift right arithmatic integer
let sraiWasm =
    use WasmAST in 
    createIntBinop "srai" (lam l. lam r. I32ShrS (l, r))

let eqiWasm = 
    use WasmAST in
    createIntBinop "eqi" (lam l. lam r. I32Eq (l, r))

let neqiWasm = 
    use WasmAST in
    createIntBinop "neqi" (lam l. lam r. I32Ne (l, r))

let ltiWasm = 
    use WasmAST in
    createIntBinop "lti" (lam l. lam r. I32LtS (l, r))

let gtiWasm = 
    use WasmAST in
    createIntBinop "gti" (lam l. lam r. I32GtS (l, r))

let leqiWasm = 
    use WasmAST in
    createIntBinop "leqi" (lam l. lam r. I32LeS (l, r))

let geqiWasm = 
    use WasmAST in
    createIntBinop "geqi" (lam l. lam r. I32GeS (l, r))



-- List Operations
let consStructName = nameSym "_cons-struct" 
let valFieldName = nameSym "_value" 
let remFieldName = nameSym "_remainder"
let nilStructName = nameSym "_nil-struct"

let consStructDef = 
    use WasmAST in 
    StructTypeDef {
        ident = consStructName,
        fields = [
            {ident = valFieldName, ty = Anyref ()},
            {ident = remFieldName, ty = Anyref ()}
        ]
    }

let nilStructDef = 
    use WasmAST in 
    StructTypeDef {
        ident = nilStructName,
        fields = []
    }

let extractFieldFromList = lam s : String. lam fieldIdent : Name. 
    use WasmAST in 
    let arg = nameSym "arg" in 
    let res = nameSym "result" in 
    FunctionDef {
        ident = nameNoSym s,
        args = [{ident = arg, ty = Anyref ()}],
        locals = [{ident = res, ty = Anyref ()}],
        resultTy = Anyref (),
        instructions = [
            IfThenElse {
                cond = RefTest {
                    ty = Ref consStructName,
                    value = LocalGet arg
                },
                thn = [LocalSet (
                    res, 
                    StructGet {
                        structIdent = consStructName,
                        field = fieldIdent, 
                        value = RefCast {
                            ty = Ref consStructName,
                            value = LocalGet arg
                        }
                    }
                )],
                els = [Unreachable ()]
            },
            LocalGet res
        ]
    }

let headWasm = extractFieldFromList "head" valFieldName
let tailWasm = extractFieldFromList "tail" remFieldName

-- Tail Recursive Helper function for length
let lengthHelperWasm = 
    use WasmAST in 
    let fident = nameNoSym "_lengthhelper" in 
    let arg = nameSym "arg" in 
    let acc = nameSym "acc"  in 
    let res = nameSym "result" in 
    FunctionDef {
        ident = fident,
        args = [
            {ident = arg, ty = Anyref ()},
            {ident = acc, ty = Tyi32 ()}
        ],
        locals = [{ident = res, ty = Tyi32 ()}],
        resultTy = Tyi32 (),
        instructions = [
            IfThenElse {
                cond = RefTest {
                    ty = Ref consStructName,
                    value = LocalGet arg
                },
                thn = [Return (Call (fident, [
                    StructGet {
                        structIdent = consStructName,
                        field = remFieldName, 
                        value = RefCast {
                            ty = Ref consStructName,
                            value = LocalGet arg
                        }
                    },
                    I32Add (I32Const 1, LocalGet acc)
                ]))],
                els = [Return (LocalGet acc)]
            }
        ]
    }

let lengthWasm = 
    use WasmAST in 
    let arg = nameSym "arg" in 
    FunctionDef {
        ident = nameNoSym "length",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (Call (nameNoSym "_lengthhelper", [
                LocalGet arg,
                I32Const 0
            ]))
        ]
    }

let integerIntrinsics = [
    addiWasm,
    subiWasm,
    muliWasm,
    modiWasm,
    diviWasm,
    negiWasm,
    slliWasm,
    srliWasm,
    sraiWasm,
    eqiWasm,
    neqiWasm,
    ltiWasm,
    gtiWasm,
    leqiWasm,
    geqiWasm,
    headWasm,
    tailWasm,
    lengthHelperWasm,
    lengthWasm
]