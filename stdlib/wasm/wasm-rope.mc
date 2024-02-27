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


let switchOnType = lam target. lam onLeaf. lam onSlice. lam onConcat. 
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

let headWasm = 
    use WasmAST in 
    let xs = nameSym "xs" in 
    FunctionDef {
        ident = nameNoSym "head",
        args = [
            {ident = xs, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            Call (nameNoSym "get", [
                LocalGet xs,
                I31Cast (I32Const 0)
            ])
        ]
    }

let tailWasm = 
    use WasmAST in 
    let xs = nameSym "xs" in 
    let res = nameSym "res" in 
    FunctionDef {
        ident = nameNoSym "tail",
        args = [
            {ident = xs, ty = Anyref ()}
        ],
        locals = [{ident = res, ty = Anyref ()}],
        resultTy = Anyref (),
        instructions = [
            switchOnType 
                (LocalGet xs)
                (lam leaf. [LocalSet (res, StructNew {
                    structIdent = sliceName,
                    values = [
                        -- Length
                        I32Sub (
                            StructGet {
                                structIdent = leafName,
                                field = lenName,
                                value = leaf
                            }, 
                            I32Const (1)
                        ),
                        -- Offset
                        I32Const 1,
                        -- Array
                        StructGet {
                            structIdent = leafName,
                            field = arrName,
                            value = leaf
                        }
                    ]
                })])
                (lam slice. [LocalSet (res, StructNew {
                    structIdent = sliceName,
                    values = [
                        -- Length
                        I32Sub(
                            StructGet {
                                structIdent = sliceName,
                                field = lenName,
                                value = slice
                            }, 
                            I32Const (1)
                        ),
                        -- Offset
                        I32Add(
                            StructGet {
                                structIdent = sliceName,
                                field = offName,
                                value = slice
                            }, 
                            I32Const (1)
                        ),
                        StructGet {
                            structIdent = sliceName,
                            field = arrName,
                            value = slice
                        }
                    ]
                })])
                -- Todo: Implement this!
                (lam cnct. [Unreachable()]),
            LocalGet res
        ]
    }

let arrayCopyName = nameSym "arraycopy"
let arrayCopyWasm =
    use WasmAST in 
    let n = nameSym "n" in
    let orig = nameSym "orig" in 
    let dest = nameSym "dest" in 
    let origOffset = nameSym "orig-offset" in 
    let destOffset = nameSym "dest-offset" in 

    let loopIdent = nameSym "copy-loop" in 
    let i = nameSym "i" in 

    FunctionDef {
        ident = arrayCopyName,
        args = [
            {ident = orig, ty = Ref anyrefArrName},
            {ident = dest, ty = Ref anyrefArrName},
            {ident = n, ty = Tyi32 ()},
            {ident = origOffset, ty = Tyi32 ()},
            {ident = destOffset, ty = Tyi32 ()}
        ],
        locals = [{ident = i, ty = Tyi32 ()}],
        resultTy = Ref anyrefArrName,
        instructions = [
            Loop {
                ident = loopIdent,
                body = [
                    ArraySet {
                        tyIdent = anyrefArrName,
                        value = LocalGet dest,
                        index = I32Add (LocalGet i, LocalGet destOffset),
                        value2 = ArrayGet {
                            tyIdent = anyrefArrName,
                            index = I32Add (LocalGet i, LocalGet origOffset),
                            value = LocalGet orig
                        }
                    },
                    LocalSet (i, I32Add(LocalGet i, I32Const 1)),
                    BrIf {
                        ident = loopIdent,
                        cond = I32LtS (LocalGet i, LocalGet n)
                    }
                ]
            },
            LocalGet dest
        ]
    }
    

let flattenWasm = 
    use WasmAST in 
    let xs = nameSym "xs" in 
    let res = nameSym "res" in
    let i = nameSym "i" in
    let loop1 = nameSym "loop1" in
    let newArr = nameSym "newArr" in
    let leftResult = nameSym "leftResult" in
    let rightResult = nameSym "leftResult" in

    let onLeaf = lam leaf. [LocalSet(res, leaf)] in 

    let onCnct = lam cnct. [
        LocalSet (newArr, ArrayNew {
            tyIdent = anyrefArrName,
            initValue = I31Cast (I32Const 0),
            size = StructGet {
                structIdent = concatName,
                field = lenName,
                value = cnct
            }
        }),
        (LocalSet (leftResult, RefCast {
            ty = Ref leafName,
            value = (Call (nameNoSym "_flatten-rope", [StructGet {
                structIdent = concatName,
                field = lhsName,
                value = cnct
            }]))
        })),
        (LocalSet (rightResult, RefCast {
            ty = Ref leafName,
            value = (Call (nameNoSym "_flatten-rope", [StructGet {
                structIdent = concatName,
                field = rhsName,
                value = cnct
            }]))
        })),
        (LocalSet (newArr, Call (arrayCopyName, [
            StructGet {
                structIdent = leafName,
                field = arrName,
                value = LocalGet leftResult
            },
            LocalGet newArr,
            StructGet {
                structIdent = leafName,
                field = lenName,
                value = LocalGet leftResult
            },
            I32Const 0,
            I32Const 0
        ]))),
        (LocalSet (newArr, Call (arrayCopyName, [
            StructGet {
                structIdent = leafName,
                field = arrName,
                value = LocalGet rightResult
            },
            LocalGet newArr,
            StructGet {
                structIdent = leafName,
                field = lenName,
                value = LocalGet rightResult
            },
            I32Const 0,
            StructGet {
                structIdent = leafName,
                field = lenName,
                value = LocalGet leftResult
            }
        ]))),
        (LocalSet (res, StructNew {
            structIdent = leafName,
            values = [
                StructGet {
                    structIdent = concatName,
                    field = lenName,
                    value = cnct
                },
                LocalGet newArr
            ]
        }))
    ] in 

    let onSlice = lam slice. [
        LocalSet (newArr, ArrayNew {
            tyIdent = anyrefArrName,
            initValue = I31Cast (I32Const 0),
            size = StructGet {
                structIdent = sliceName,
                field = lenName,
                value = slice
            }
        }),
        (LocalSet (newArr, Call (arrayCopyName, [
            StructGet {
                structIdent = sliceName,
                field = arrName,
                value = slice
            },
            LocalGet newArr,
            StructGet {
                structIdent = sliceName,
                field = lenName,
                value = slice
            },
            StructGet {
                structIdent = sliceName,
                field = offName,
                value = slice
            },
            I32Const 0
        ]))),
        (LocalSet (res, StructNew {
            structIdent = leafName,
            values = [
                StructGet {
                    structIdent = sliceName,
                    field = lenName,
                    value = slice
                },
                LocalGet newArr
            ]
        }))
    ] in 

    FunctionDef {
        ident = nameNoSym "_flatten-rope",
        args = [{ident = xs, ty = Anyref ()}],
        locals = [
            {ident = newArr, ty = Ref anyrefArrName},
            {ident = res, ty = Anyref ()},
            {ident = i, ty = Tyi32 ()},
            {ident = leftResult, ty = Ref leafName},
            {ident = rightResult, ty = Ref leafName}
        ],
        resultTy = Anyref (),
        instructions = [
            (switchOnType 
                (LocalGet xs) 
                onLeaf
                onSlice
                onCnct),
            LocalGet res
        ]
    }

let reverseWasm = 
    use WasmAST in 
    let flat = nameSym "flat" in 
    let xs = nameSym "xs" in 
    let i = nameSym "i" in
    let mid = nameSym "mid" in 
    let loopIdent = nameSym "revLoop" in 
    let tmp = nameSym "tmp" in 
    let lenMinusOne = nameSym "lenMinusOne" in 
    FunctionDef {
        ident = nameNoSym "reverse",
        args = [
            {ident = xs, ty = Anyref ()}
        ],
        locals = [
            {ident = flat, ty = Ref leafName},
            {ident = tmp, ty = Anyref ()},
            {ident = i, ty = Tyi32()},
            {ident = mid, ty = Tyi32()},
            {ident = lenMinusOne, ty = Tyi32()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet (flat, RefCast {
                ty = Ref leafName,
                value = Call (nameNoSym "_flatten-rope", [LocalGet xs])
            }),

            LocalSet (mid, I32DivS (
                StructGet {
                    structIdent = leafName,
                    field = lenName,
                    value = LocalGet flat
                },
                I32Const 2
            )),

            LocalSet (lenMinusOne, I32Sub (
                StructGet {
                    structIdent = leafName,
                    field = lenName,
                    value = LocalGet flat
                },
                I32Const 1
            )),


            -- Reverse loop
            Loop {
                ident = loopIdent,
                body = [
                    -- tmp = arr[n - i]
                    LocalSet (tmp, ArrayGet {
                        tyIdent = anyrefArrName,
                        value = StructGet {
                            structIdent = leafName,
                            field = arrName,
                            value = LocalGet flat
                        },
                        index = I32Sub(LocalGet lenMinusOne, LocalGet i)
                    }),

                    -- arr [n-i] = arr[i]
                    ArraySet {
                        tyIdent = anyrefArrName,
                        value = StructGet {
                            structIdent = leafName,
                            field = arrName,
                            value = LocalGet flat
                        },
                        index = I32Sub(LocalGet lenMinusOne, LocalGet i),
                        value2 = ArrayGet {
                            tyIdent = anyrefArrName,
                            value = StructGet {
                                structIdent = leafName,
                                field = arrName,
                                value = LocalGet flat
                            },
                            index = LocalGet i
                        }
                    },

                    -- arr[i] = tmp
                    ArraySet {
                        tyIdent = anyrefArrName,
                        value = StructGet {
                            structIdent = leafName,
                            field = arrName,
                            value = LocalGet flat
                        },
                        index = LocalGet i,
                        value2 = LocalGet tmp
                    },

                    LocalSet (i, I32Add(LocalGet i, I32Const 1)),

                    BrIf {
                        ident = loopIdent,
                        cond = I32LeS(LocalGet i, LocalGet mid)
                    }
                ]
            },

            LocalGet flat
        ]
    }
    
let iterArrayName = nameSym "iter-array"
let iteriArrayName = nameSym "iteri-array"
let iterArrayFactory = lam useIndex: Bool. 
    use WasmAST in 
    let arr = nameSym "arr" in 
    let f = nameSym "f" in 
    let offset = nameSym "offset" in 
    let n = nameSym "n" in 
    let i = nameSym "i" in 
    let loopIdent = nameSym "loopIdent" in 

    let call = 
        if useIndex then 
            Call (nameNoSym "apply", [
                Call (nameNoSym "apply", [
                    LocalGet f,
                    I31Cast (LocalGet i)
                ]),
                ArrayGet {
                    tyIdent = anyrefArrName,
                    value = LocalGet arr,
                    index = I32Add(LocalGet i, LocalGet offset)
                }
            ])
        else
            Call (nameNoSym "apply", [
                LocalGet f,
                ArrayGet {
                    tyIdent = anyrefArrName,
                    value = LocalGet arr,
                    index = I32Add(LocalGet i, LocalGet offset)
                }
            ])
    in 

    FunctionDef {
        ident = if useIndex then iteriArrayName else iterArrayName,
        locals = [{ident = i, ty = Tyi32 ()}],
        args = [
            {ident = arr, ty = Ref anyrefArrName},
            {ident = f, ty = Anyref ()},
            {ident = offset, ty = Tyi32 ()},
            {ident = n, ty = Tyi32 ()}
        ],
        resultTy = Tyi32 (),
        instructions = [
            Loop {
                ident = loopIdent,
                body = [
                    Drop call,
                    LocalSet (i, I32Add(LocalGet i, I32Const 1)),
                    BrIf {
                        ident = loopIdent,
                        cond = I32LtS (LocalGet i, LocalGet n)
                    }
                ]
            },
            I32Const 0
        ]
    }

let iterFactoryWasm = lam useIndex: Bool.  
    use WasmAST in 
    let rope = nameSym "rope" in 
    let f = nameSym "f" in 

    let arrayFunctionName = if useIndex then iteriArrayName else iterArrayName in
    let funcName = if useIndex then nameNoSym "iteri" else nameNoSym "iter" in 

    let onLeaf = lam leaf. [
        Drop (Call (arrayFunctionName, [
            StructGet {
                structIdent = leafName,
                field = arrName,
                value = leaf
            },
            LocalGet f,
            I32Const 0,
            StructGet {
                structIdent = leafName,
                field = lenName,
                value = leaf
            }
        ]))]
    in

    let onSlice = lam slice. [
        Drop (Call (arrayFunctionName, [
            StructGet {
                structIdent = sliceName,
                field = arrName,
                value = slice
            },
            LocalGet f,
            StructGet {
                structIdent = sliceName,
                field = offName,
                value = slice
            },
            StructGet {
                structIdent = sliceName,
                field = lenName,
                value = slice
            }
        ]))]
    in 

    let onConcat = lam cnct. [
        Drop (
            Call (funcName, [
                LocalGet f,
                StructGet {
                    structIdent = concatName,
                    field = lhsName,
                    value = cnct
                }
            ])
        ),
        Drop (
            Call (funcName, [
                LocalGet f,
                StructGet {
                    structIdent = concatName,
                    field = rhsName,
                    value = cnct
                }
            ])
        )
    ] in 

    FunctionDef {
        ident = funcName,
        args = [
            {ident = f, ty = Anyref ()},
            {ident = rope, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            switchOnType
                (LocalGet rope)
                onLeaf
                onSlice
                onConcat,
            I31Cast (I32Const 0)
        ]
    }

let foldlArrayName = nameSym "foldl-array"
let foldrArrayName = nameSym "foldr-array"
let foldlArrayFactory = lam left: Bool. 
    use WasmAST in 
    let arr = nameSym "arr" in 
    let f = nameSym "f" in 
    let acc = nameSym "acc" in 
    let offset = nameSym "offset" in 
    let n = nameSym "n" in 
    let i = nameSym "i" in 
    let loopIdent = nameSym "loopIdent" in 

    let work = 
        LocalSet (acc, Call (nameNoSym "apply", [
            Call (nameNoSym "apply", [
                LocalGet f,
                LocalGet acc
            ]),
            ArrayGet {
                tyIdent = anyrefArrName,
                value = LocalGet arr,
                index = I32Add(LocalGet i, LocalGet offset)
            }
        ]))
    in 

    let initI = if left then I32Const 0 else I32Sub (LocalGet n, I32Const 1) in
    let updateI = if left 
        then I32Add(LocalGet i, I32Const 1)
        else I32Sub(LocalGet i, I32Const 1)
    in
    let brCond = if left
        then I32LtS (LocalGet i, LocalGet n)
        else I32GeS (LocalGet i, I32Const 0)
    in

    FunctionDef {
        ident = if left then foldlArrayName else foldrArrayName,
        locals = [{ident = i, ty = Tyi32 ()}],
        args = [
            {ident = arr, ty = Ref anyrefArrName},
            {ident = f, ty = Anyref ()},
            {ident = acc, ty = Anyref ()},
            {ident = offset, ty = Tyi32 ()},
            {ident = n, ty = Tyi32 ()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet (i, initI),
            Loop {
                ident = loopIdent,
                body = [
                    work,
                    LocalSet (i, updateI),
                    BrIf {
                        ident = loopIdent,
                        cond = brCond
                    }
                ]
            },
            LocalGet acc
        ]
    }

let foldlFactoryWasm = lam left: Bool.  
    use WasmAST in 
    let rope = nameSym "rope" in 
    let f = nameSym "f" in 
    let acc = nameSym "acc" in 

    let arrayFunctionName = if left then foldlArrayName else foldrArrayName in
    let funcName = if left then nameNoSym "foldl" else nameNoSym "foldr" in 

    let onLeaf = lam leaf. [
        LocalSet (acc, (Call (arrayFunctionName, [
            StructGet {
                structIdent = leafName,
                field = arrName,
                value = leaf
            },
            LocalGet f,
            LocalGet acc,
            I32Const 0,
            StructGet {
                structIdent = leafName,
                field = lenName,
                value = leaf
            }
        ])))]
    in

    let onSlice = lam slice. [
        LocalSet (acc, (Call (arrayFunctionName, [
            StructGet {
                structIdent = sliceName,
                field = arrName,
                value = slice
            },
            LocalGet f,
            LocalGet acc,
            StructGet {
                structIdent = sliceName,
                field = offName,
                value = slice
            },
            StructGet {
                structIdent = sliceName,
                field = lenName,
                value = slice
            }
        ])))]
    in 

    let fst = if left
        then lhsName
        else rhsName
    in 

    let snd = if left
        then rhsName
        else lhsName
    in

    let onConcat = lam cnct. [
        LocalSet (acc,
            Call (funcName, [
                LocalGet f,
                LocalGet acc,
                StructGet {
                    structIdent = concatName,
                    field = fst,
                    value = cnct
                }
            ])
        ),
        LocalSet (acc,
            Call (funcName, [
                LocalGet f,
                LocalGet acc,
                StructGet {
                    structIdent = concatName,
                    field = snd,
                    value = cnct
                }
            ])
        )
    ] in 

    FunctionDef {
        ident = funcName,
        args = [
            {ident = f, ty = Anyref ()},
            {ident = acc, ty = Anyref ()},
            {ident = rope, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            switchOnType
                (LocalGet rope)
                onLeaf
                onSlice
                onConcat,
            LocalGet acc
        ]
    }

let iteriArrayWasm = iterArrayFactory true
let iterArrayWasm = iterArrayFactory false
let iteriWasm = iterFactoryWasm true
let iterWasm = iterFactoryWasm false

let foldlArrayWasm = foldlArrayFactory true
let foldrArrayWasm = foldlArrayFactory false
let foldlWasm = foldlFactoryWasm true
let foldrWasm = foldlFactoryWasm false