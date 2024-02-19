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

let genRefTest = lam n. lam target.
    use WasmAST in 
    RefTest {
        ty = Ref n,
        value = target
    }

let anyref2i32 = lam target.
    use WasmAST in 
    I31GetS (RefCast {
        ty = I31Ref (),
        value = target
    })



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


let switchOnType = lam target. lam res. lam onLeaf. lam onSlice. lam onConcat. 
    use WasmAST in 
    IfThenElse {
        cond = genRefTest leafName target,
        thn = onLeaf (RefCast {ty=Ref leafName, value=target}),
        els = [
            IfThenElse {
                cond = genRefTest concatName target,
                thn = onConcat (RefCast {ty=Ref concatName, value=target}),
                els = [
                    IfThenElse {
                        cond = genRefTest sliceName target,
                        thn = onSlice (RefCast {ty=Ref sliceName, value=target}),
                        els = [Unreachable ()]
                    }
                ]
            }
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

let getWasm =
    use WasmAST in 
    let i_uncast = nameSym "i_uncast" in 
    let i = nameSym "i" in 
    let n = nameSym "n" in 
    let arg = nameSym "arg" in 
    let res = nameSym "res" in 
    FunctionDef {
        ident = nameNoSym "get",
        args = [
            {ident = arg, ty = Anyref ()},
            {ident = i_uncast, ty = Anyref ()}
        ],
        locals = [
            {ident = res, ty = Anyref ()},
            {ident = n, ty = Tyi32 ()},
            {ident = i, ty = Tyi32 ()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet (i, anyref2i32 (LocalGet i_uncast)),
            switchOnType 
                (LocalGet arg)
                res 
                (lam leaf. [LocalSet (res, ArrayGet {
                    tyIdent = anyrefArrName,
                    value = StructGet {
                        structIdent = leafName,
                        field = arrName,
                        value = leaf
                    },
                    index = LocalGet i
                })])
                (lam slice. [(LocalSet (res, ArrayGet {
                    tyIdent = anyrefArrName,
                    value = StructGet {
                        structIdent = sliceName,
                        field = arrName,
                        value = slice
                    },
                    index = I32Add (
                        LocalGet i,
                        StructGet {
                            structIdent = sliceName,
                            field = offName,
                            value = slice
                        }
                    )
                }))])
                (lam cnct. [
                    LocalSet (n, I31GetS 
                        (RefCast {
                            ty = I31Ref (), 
                            value = (Call ((nameNoSym "length"), [StructGet {
                                structIdent = concatName,
                                field = lhsName,
                                value = cnct
                            }]))
                        }
                    )),
                    IfThenElse {
                        cond = I32LtS(LocalGet i, LocalGet n),
                        thn = [Return (Call ((nameNoSym "get"), [
                            StructGet {
                                structIdent = concatName,
                                field = lhsName,
                                value = cnct
                            },
                            LocalGet i_uncast
                        ]))],
                        els = [Return (Call ((nameNoSym "get"), [
                            StructGet {
                                structIdent = concatName,
                                field = rhsName,
                                value = cnct
                            },
                            I31Cast (I32Sub(LocalGet i, LocalGet n))
                        ]))]
                    }
                ]),
            LocalGet res
        ]
    }

let consWasm = 
    use WasmAST in 
    let x = nameSym "x" in 
    let xs = nameSym "xs" in 

    let getLen = lam ident. I31GetU (RefCast {
        ty = I31Ref (),
        value = (Call (nameNoSym "length", [LocalGet ident]))
    }) in 

    let newLeaf = StructNew {
        structIdent = leafName,
        values = [
            I32Const 1,
            ArrayNew {
                tyIdent = anyrefArrName,
                initValue = LocalGet x,
                size = I32Const 1
            }
        ]
    } in 

    FunctionDef {
        ident = nameNoSym "cons",
        args = [
            {ident = x, ty = Anyref ()},
            {ident = xs, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [StructNew {
            structIdent = concatName,
            values = [
                I32Add (getLen xs, I32Const 1),
                newLeaf,
                LocalGet xs
            ]
        }]
    }

let snocWasm = 
    use WasmAST in 
    let x = nameSym "x" in 
    let xs = nameSym "xs" in 

    let getLen = lam ident. I31GetU (RefCast {
        ty = I31Ref (),
        value = (Call (nameNoSym "length", [LocalGet ident]))
    }) in 

    let newLeaf = StructNew {
        structIdent = leafName,
        values = [
            I32Const 1,
            ArrayNew {
                tyIdent = anyrefArrName,
                initValue = LocalGet x,
                size = I32Const 1
            }
        ]
    } in 

    FunctionDef {
        ident = nameNoSym "snoc",
        args = [
            {ident = xs, ty = Anyref ()},
            {ident = x, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [StructNew {
            structIdent = concatName,
            values = [
                I32Add (getLen xs, I32Const 1),
                LocalGet xs,
                newLeaf

            ]
        }]
    }