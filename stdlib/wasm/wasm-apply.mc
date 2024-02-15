include "wasm-ast.mc"
include "wasm-pprint.mc"

include "string.mc"
include "seq.mc"

let argsArrayName = nameNoSym "args-array"

let nullLikeDef = 
    use WasmAST in
    GlobalDef {
        ident = nameNoSym "null-like",
        ty = Anyref (),
        initValue = I31Cast (I32Const 0)
    }

let argsArrayType = 
    use WasmAST in 
    ArrayTypeDef {
        ident = argsArrayName,
        paramTys = [Anyref ()]
    }

let closDef = 
    use WasmAST in (StructTypeDef {
    ident = nameNoSym "clos",
    fields = [
        {ident = nameNoSym "func-pointer", ty = Tyi32 ()},
        {ident = nameNoSym "max-arity", ty = Tyi32 ()},
        {ident = nameNoSym "cur-arity", ty = Tyi32 ()},
        {ident = nameNoSym "args", ty = Ref argsArrayName}
    ]})

let genGenericType = lam arity. 
    use WasmAST in 
    FunctionTypeDef {
        ident = nameNoSym (concat "generic-type-" (int2string arity)),
        paramTys = make arity (Anyref ()),
        resultTy = Anyref ()
    }

let genExec = lam arity. 
    use WasmAST in 
    let getArg = lam i. 
        ArrayGet {
            tyIdent = argsArrayName,
            value = StructGet {
                structIdent = nameNoSym "clos",
                field = nameNoSym "args",
                value = LocalGet (nameNoSym "cl")
            },
            index = I32Const i
        } in 
    let args = map getArg (range 0 arity 1) in 
    FunctionDef {
        ident = nameNoSym (concat "exec-" (int2string arity)), 
        args = [{ident = nameNoSym "cl", ty = Ref (nameNoSym "clos")}],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            CallIndirect {
                ty = nameNoSym (concat "generic-type-" (int2string arity)),
                args = args,
                fp = StructGet {
                    structIdent = nameNoSym "clos",
                    field = nameNoSym "func-pointer",
                    value = LocalGet (nameNoSym "cl")
                }
            }
        ]
    }

let genDispatch = lam arities: [Int]. 
    use WasmAST in 
    recursive
    let work = lam remaining: [Int].
        match remaining with []
            -- Should throw error on this case.
            then 
                LocalSet (nameNoSym "result", GlobalGet (nameNoSym "null-like"))
            else 
                let arity = head remaining in 
                IfThenElse {
                    cond = I32Eq (
                        LocalGet (nameNoSym "arity"),
                        I32Const arity
                    ),
                    thn = [LocalSet ((nameNoSym "result"), Call (
                            nameNoSym (concat "exec-" (int2string arity)),
                            [LocalGet (nameNoSym "cl")]
                        ))],
                    els = [work (tail remaining)]
                } 
    in 
    FunctionDef {
        ident = nameNoSym "dispatch",
        args = [{ident = nameNoSym"cl", ty = Ref (nameNoSym "clos")}],
        locals = [
            {ident = nameNoSym "arity", ty = Tyi32 ()},
            {ident = nameNoSym "result", ty = Anyref()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet ((nameNoSym "arity"), StructGet {
                structIdent = nameNoSym "clos",
                field = nameNoSym "max-arity",
                value = LocalGet (nameNoSym "cl")
            }),
            work arities,
            LocalGet (nameNoSym "result")
        ]
    }

let apply =  
    use WasmAST in 
    let copyIndex = lam instr. 
        ArraySet {
            tyIdent = nameNoSym "args-array",
            value = LocalGet (nameNoSym "new-array"),
            index = instr,
            value2 = ArrayGet {
                tyIdent = nameNoSym "args-array",
                value = StructGet {
                    structIdent = nameNoSym "clos",
                    field = nameNoSym "args",
                    value = LocalGet (nameNoSym "cl")
                },
                index = instr
            }
        } in 
    FunctionDef {
        ident = nameNoSym "apply",
        args = [
            {ident = nameNoSym "lhs", ty = Anyref ()},
            {ident = nameNoSym "arg", ty = Anyref ()}
        ],
        locals = [
            {ident = nameNoSym "cl", ty = Ref (nameNoSym "clos")},
            {ident = nameNoSym "new-array", ty = Ref (nameNoSym "args-array")},
            {ident = nameNoSym "result", ty = Anyref ()},
            {ident = nameNoSym "new-clos", ty = Ref (nameNoSym "clos")},
            {ident = nameNoSym "i", ty = Tyi32 ()}
        ],
        resultTy = Anyref (), 
        instructions = [
            LocalSet (nameNoSym "cl", 
                RefCast {
                    ty = Ref (nameNoSym "clos"),
                    value = LocalGet (nameNoSym "lhs")
                }
            ),
            LocalSet (nameNoSym "new-array", 
                ArrayNew {
                    tyIdent = nameNoSym "args-array",
                    initValue = GlobalGet (nameNoSym "null-like"),
                    size = StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "max-arity",
                        value = LocalGet (nameNoSym "cl")
                    }
                }
            ),
            IfThenElse {
                cond = I32Ne (I32Const 0, StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "max-arity",
                        value = LocalGet (nameNoSym "cl")
                    }),
                thn = [Loop {
                    ident = nameNoSym "args-copy-loop",
                    body = [
                        copyIndex (LocalGet (nameNoSym "i")),
                        LocalSet (nameNoSym "i", I32Add (LocalGet (nameNoSym "i"), I32Const 1)),
                        BrIf {
                            ident = nameNoSym "args-copy-loop",
                            cond = I32Ne (
                                LocalGet (nameNoSym "i"),
                                StructGet {
                                    structIdent = nameNoSym "clos",
                                    field = nameNoSym "max-arity",
                                    value = LocalGet (nameNoSym "cl")
                                }    
                            )
                        }
                    ]},
                    ArraySet {
                        tyIdent = nameNoSym "args-array",
                        value = LocalGet (nameNoSym "new-array"),
                        index = StructGet {
                            structIdent = nameNoSym "clos",
                            field = nameNoSym "cur-arity",
                            value = LocalGet (nameNoSym "cl")
                        },
                        value2 = LocalGet (nameNoSym "arg")
                    }],
                els = []
            },
            LocalSet (nameNoSym "new-clos", StructNew {
                structIdent = nameNoSym "clos", 
                values = [
                    StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "func-pointer",
                        value = LocalGet (nameNoSym "cl")
                    },
                    StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "max-arity",
                        value = LocalGet (nameNoSym "cl")
                    },
                    I32Add (
                        I32Const 1,
                        StructGet {
                            structIdent = nameNoSym "clos",
                            field = nameNoSym "cur-arity",
                            value = LocalGet (nameNoSym "cl")
                        }
                    ),
                    LocalGet (nameNoSym "new-array")
                ]
            }),
            IfThenElse {
                cond = I32Eq (
                    StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "cur-arity",
                        value = LocalGet (nameNoSym "new-clos")
                    },
                    StructGet {
                        structIdent = nameNoSym "clos",
                        field = nameNoSym "max-arity",
                        value = LocalGet (nameNoSym "new-clos")
                    }
                ),
                thn = [LocalSet (nameNoSym "result", Call (nameNoSym "dispatch", [LocalGet (nameNoSym "new-clos")]))],
                els = [LocalSet (nameNoSym "result", LocalGet (nameNoSym "new-clos"))]
            },
            LocalGet (nameNoSym "result")
        ]
    }

mexpr 
let res = genDispatch [0, 1, 2] in 
let a = apply in 
use WasmPPrint in 
-- printLn (pprintDef 0 res)
printLn (pprintDef 0 a)