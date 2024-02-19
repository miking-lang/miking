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

let idWasm = 
    use WasmAST in 
    let arg = nameSym "arg" in 
    FunctionDef {
        ident = nameNoSym "id",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [LocalGet arg]
    }