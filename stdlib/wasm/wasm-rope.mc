include "wasm-ast.mc"
include "wasm-pprint.mc"

include "name.mc"

let leafName = nameSym "_leaf"
let sliceName = nameSym "_slice"
let concatName = nameSym "_concat"

let lhsName = nameSym "_lhs"
let rhsName = nameSym "_rhs"
let lenName = nameSym "_len"
let arrName = nameSym "_arr"
let offName = nameSym "_off"

let anyrefArrName = nameSym "_anyref-arr"
let anyrefArrDef = 
    use WasmAST in 
    ArrayTypeDef {
        ident = anyrefArrName,
        paramTys = [Anyref ()]
    }

let leafDef = 
    use WasmAST in 
    StructTypeDef {
        ident = leafName,
        fields = [
            {ident=lenName, ty=Tyi32 ()},
            {ident=arrName, ty=Ref anyrefArrName}
        ]
    }

let sliceDef = 
    use WasmAST in 
    StructTypeDef {
        ident = sliceName,
        fields = [
            {ident=lenName, ty=Tyi32 ()},
            {ident=offName, ty=Tyi32 ()},
            {ident=arrName, ty=Ref anyrefArrName}
        ]
    }

let concatDef = 
    use WasmAST in 
        StructTypeDef {
        ident = concatName,
        fields = [
            {ident=lenName, ty=Tyi32 ()},
            {ident=lhsName, ty=Anyref ()},
            {ident=rhsName, ty=Anyref ()}
        ]
    }

let lengthWasm = 
    use WasmAST in 
    let arg = nameSym "arg" in 
    let res = nameSym "res" in 
    let genRefTest = lam n. (RefTest {
        ty = Ref n,
        value = LocalGet arg
    }) in 
    let genGetLen = lam n. (StructGet {
        structIdent = n,
        field = lenName,
        value = RefCast {
            ty = Ref n,
            value = LocalGet arg
        }
    }) in 
    FunctionDef {
        ident = nameNoSym "length",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [{ident = res, ty = Tyi32 ()}],
        resultTy = Anyref (),
        instructions = [
            IfThenElse {
                cond = genRefTest leafName,
                thn = [LocalSet (res, genGetLen leafName)],
                els = [
                    IfThenElse {
                        cond = genRefTest concatName,
                        thn = [LocalSet (res, genGetLen concatName)],
                        els = [
                            IfThenElse {
                                cond = genRefTest sliceName,
                                thn = [LocalSet (res, genGetLen sliceName)],
                                els = [Unreachable ()]
                            }
                        ]
                    }
                ]
            },
            I31Cast (LocalGet res)
        ]
    }

let concatWasm = 
    use WasmAST in 
    let l = nameSym "l" in 
    let r = nameSym "r" in 

    let getLen = lam ident. I31GetU (RefCast {
        ty = I31Ref (),
        value = (Call (nameNoSym "length", [LocalGet ident]))
    }) in 

    FunctionDef {
        ident = nameNoSym "concat",
        args = [
            {ident = l, ty = Anyref ()},
            {ident = r, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [StructNew {
            structIdent = concatName,
            values = [
                I32Add (getLen l, getLen r),
                LocalGet l,
                LocalGet r
            ]
        }]
    }