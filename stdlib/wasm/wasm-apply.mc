include "wasm-ast.mc"
include "wasm-pprint.mc"

include "string.mc"
include "seq.mc"

let nullLikeDef = 
    use WasmAST in
    GlobalDef {
        ident = "null-like",
        ty = Anyref (),
        initValue = StructNew {
            structIdent = "i32box",
            values = [I32Const 0]
        }
    }

let argsArrayType = 
    use WasmAST in 
    ArrayTypeDef {
        ident = "args-array",
        paramTys = [Anyref ()]
    }

let closDef = 
    use WasmAST in (StructTypeDef {
    ident = "clos",
    fields = [
        {ident = "func-pointer", ty = Tyi32 ()},
        {ident = "max-arity", ty = Tyi32 ()},
        {ident = "cur-arity", ty = Tyi32 ()},
        {ident = "args", ty = Ref "args-array"}
    ]})

let genGenericType = lam arity. 
    use WasmAST in 
    FunctionTypeDef {
        ident = concat "generic-type-" (int2string arity),
        paramTys = make arity (Anyref ()),
        resultTy = Anyref()
    }

let genExec = lam arity. 
    use WasmAST in 
    let getArg = lam i. 
        ArrayGet {
            tyIdent = "args-array",
            value = StructGet {
                structIdent = "clos",
                field = "args",
                value = LocalGet "cl"
            },
            index = I32Const i
        } in 
    let args = map getArg (range 0 arity 1) in 
    FunctionDef {
        ident = concat "exec-" (int2string arity), 
        args = [{ident = "cl", ty = Ref "clos"}],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            CallIndirect {
                ty = concat "generic-type-" (int2string arity),
                args = args,
                fp = StructGet {
                    structIdent = "clos",
                    field = "func-pointer",
                    value = LocalGet "cl"
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
                LocalSet ("result", GlobalGet "null-like")
            else 
                let arity = head remaining in 
                IfThenElse {
                    cond = I32Eq (
                        LocalGet "arity",
                        I32Const arity
                    ),
                    thn = [LocalSet ("result", Call (
                            concat "exec-" (int2string arity),
                            [LocalGet "cl"]
                        ))],
                    els = [work (tail remaining)]
                } 
    in 
    FunctionDef {
        ident = "dispatch",
        args = [{ident = "cl", ty = Ref "clos"}],
        locals = [
            {ident = "arity", ty = Tyi32 ()},
            {ident = "result", ty = Anyref()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet ("arity", StructGet {
                structIdent = "clos",
                field = "max-arity",
                value = LocalGet "cl"
            }),
            work arities,
            LocalGet "result"
        ]
    }

let apply =  
    use WasmAST in 
    let copyIndex = lam instr. 
        ArraySet {
            tyIdent = "args-array",
            value = LocalGet "new-array",
            index = instr,
            value2 = ArrayGet {
                tyIdent = "args-array",
                value = StructGet {
                    structIdent = "clos",
                    field = "args",
                    value = LocalGet "cl"
                },
                index = instr
            }
        } in 
    FunctionDef {
        ident = "apply",
        args = [
            {ident = "lhs", ty = Anyref ()},
            {ident = "arg", ty = Anyref ()}
        ],
        locals = [
            {ident = "cl", ty = Ref "clos"},
            {ident = "new-array", ty = Ref "args-array"},
            {ident = "result", ty = Anyref ()},
            {ident = "new-clos", ty = Ref "clos"},
            {ident = "i", ty = Tyi32 ()}
        ],
        resultTy = Anyref (), 
        instructions = [
            LocalSet ("cl", 
                RefCast {
                    ty = Ref "clos",
                    value = LocalGet "lhs"
                }
            ),
            LocalSet ("new-array", 
                ArrayNew {
                    tyIdent = "args-array",
                    initValue = GlobalGet "null-like",
                    size = StructGet {
                        structIdent = "clos",
                        field = "max-arity",
                        value = LocalGet "cl"
                    }
                }
            ),
            IfThenElse {
                cond = I32Ne (I32Const 0, StructGet {
                        structIdent = "clos",
                        field = "max-arity",
                        value = LocalGet "cl"
                    }),
                thn = [Loop {
                    ident = "args-copy-loop",
                    body = [
                        copyIndex (LocalGet "i"),
                        LocalSet ("i", I32Add (LocalGet "i", I32Const 1)),
                        BrIf {
                            ident = "args-copy-loop",
                            cond = I32Ne (
                                LocalGet "i",
                                StructGet {
                                    structIdent = "clos",
                                    field = "max-arity",
                                    value = LocalGet "cl"
                                }    
                            )
                        }
                    ]}],
                els = [LocalSet ("i", I32Const 0)]
            },
            ArraySet {
                tyIdent = "args-array",
                value = LocalGet "new-array",
                index = StructGet {
                    structIdent = "clos",
                    field = "cur-arity",
                    value = LocalGet "cl"
                },
                value2 = LocalGet "arg"
            },
            LocalSet ("new-clos", StructNew {
                structIdent = "clos", 
                values = [
                    StructGet {
                        structIdent = "clos",
                        field = "func-pointer",
                        value = LocalGet "cl"
                    },
                    StructGet {
                        structIdent = "clos",
                        field = "max-arity",
                        value = LocalGet "cl"
                    },
                    I32Add (
                        I32Const 1,
                        StructGet {
                            structIdent = "clos",
                            field = "cur-arity",
                            value = LocalGet "cl"
                        }
                    ),
                    LocalGet "new-array"
                ]
            }),
            IfThenElse {
                cond = I32Eq (
                    StructGet {
                        structIdent = "clos",
                        field = "cur-arity",
                        value = LocalGet "new-clos"
                    },
                    StructGet {
                        structIdent = "clos",
                        field = "max-arity",
                        value = LocalGet "new-clos"
                    }
                ),
                thn = [LocalSet ("result", Call ("dispatch", [LocalGet "new-clos"]))],
                els = [LocalSet ("result", LocalGet "new-clos")]
            },
            LocalGet "result"
        ]
    }

mexpr 
let res = genDispatch [0, 1, 2] in 
let a = apply in 
use WasmPPrint in 
-- printLn (pprintDef 0 res)
printLn (pprintDef 0 a)