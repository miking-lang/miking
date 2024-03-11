include "wasm-ast.mc"
include "wasm-pprint.mc"

let floatBoxIdent = nameSym "floatBox"

let floatBoxDef = 
    use WasmAST in 
    StructTypeDef {
        ident = floatBoxIdent,
        fields = [
            {ident = nameNoSym "value", ty = Tyf64 ()}
        ]
    }

let anyref2float = lam anyref. 
    use WasmAST in 
    StructGet {
        structIdent = floatBoxIdent,
        field = nameNoSym "value",
        value = RefCast {
            ty = Ref floatBoxIdent, 
            value = anyref
        }
    }  

let float2box = lam f. 
    use WasmAST in 
    StructNew {
        structIdent = floatBoxIdent,
        values = [f]
    }

let createFloatBinOp = lam str. lam binop. 
    use WasmAST in 
    let l = nameSym "l" in 
    let r = nameSym "r" in 
    FunctionDef {
        ident = nameNoSym str,
        args = [
            {ident = l, ty = Anyref ()},
            {ident = r, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            float2box (F64BinOp (
                binop,
                (anyref2float (LocalGet l)),
                (anyref2float (LocalGet r))
            ))
        ]
    }

let createBoolBinOp = lam str. lam binop. 
    use WasmAST in 
    let l = nameSym "l" in 
    let r = nameSym "r" in 
    FunctionDef {
        ident = nameNoSym str,
        args = [
            {ident = l, ty = Anyref ()},
            {ident = r, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                F64BinOp (
                    binop,
                    (anyref2float (LocalGet l)),
                    (anyref2float (LocalGet r))
                )
            )
        ]
    }

let createIntUnOp = lam str. lam op. 
    use WasmAST in 
    let l = nameSym "l" in 
    FunctionDef {
        ident = nameNoSym str,
        args = [
            {ident = l, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                I32TruncF64S (
                    F64UnOp (
                        op,
                        (anyref2float (LocalGet l))
                    )
                )
            )
        ]
    }

let addfWasm = 
    use WasmAST in 
    createFloatBinOp "addf" (FloatAdd {})
let subfWasm = 
    use WasmAST in 
    createFloatBinOp "subf" (FloatSub {})
let mulfWasm = 
    use WasmAST in 
    createFloatBinOp "mulf" (FloatMul {})
let divfWasm = 
    use WasmAST in 
    createFloatBinOp "divf" (FloatDiv {})
let eqfWasm = 
    use WasmAST in 
    createBoolBinOp "eqf" (FloatEq {})
let neqfWasm = 
    use WasmAST in 
    createBoolBinOp "neqf" (FloatNe {})
let gtfWasm = 
    use WasmAST in 
    createBoolBinOp "gtf" (FloatGt {})
let ltfWasm = 
    use WasmAST in 
    createBoolBinOp "ltf" (FloatLt {})
let geqfWasm = 
    use WasmAST in 
    createBoolBinOp "geqf" (FloatGe {})
let leqfWasm = 
    use WasmAST in 
    createBoolBinOp "leqf" (FloatLe {})

let negfWasm = 
    use WasmAST in 
    let l = nameSym "l" in 
    FunctionDef {
        ident = nameNoSym "negf",
        args = [
            {ident = l, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            float2box (
                F64UnOp (
                    (FloatNeg {}),
                    (anyref2float (LocalGet l))
                )
            )
        ]
    }

-- let floorfiWasm = 
--     use WasmAST in 
--     createIntUnOp "floorfi" (FloatFloor {}) 

-- let ceilfiWasm = 
--     use WasmAST in 
--     createIntUnOp "ceilfi" (FloatCeil {}) 

-- let roundfiWasm = 
--     use WasmAST in 
--     createIntUnOp "roundfi" (FloatNearest {}) 