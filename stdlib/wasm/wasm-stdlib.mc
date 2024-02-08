include "wasm-ast.mc"
include "wasm-pprint.mc"

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

let genericType2Def =
    use WasmAST in 
    FunctionTypeDef {
        ident = "generic-type",
        paramTys = [Anyref (), Anyref ()],
        resultTy = Anyref()
    }

let closType = 
    use WasmAST in (StructTypeDef {
    ident = "clos",
    fields = [
        {ident = "func-pointer", ty = Tyi32 ()},
        {ident = "max-arity", ty = Tyi32 ()},
        {ident = "cur-arity", ty = Tyi32 ()},
        {ident = "args", ty = Ref "args-array"}
    ]})

let i32boxDef = 
    use WasmAST in 
    StructTypeDef {
        ident = "i32box",
        fields = [{
            ident = "value",
            ty = Tyi32 ()
        }]
    }

let apply = 
    use WasmAST in 
    let copyIndex = lam i. 
        ArraySet {
            tyIdent = "args-array",
            value = LocalGet "new-array",
            index = I32Const i,
            value2 = ArrayGet {
                tyIdent = "args-array",
                value = StructGet {
                    structIdent = "clos",
                    field = "args",
                    value = LocalGet "cl"
                },
                index = I32Const i
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
            {ident = "new-clos", ty = Ref "clos"}
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
            copyIndex 0,
            copyIndex 1,
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
                thn = [LocalSet ("result", CallIndirect {
                    ty = "generic-type",
                    args = [
                        ArrayGet {
                            tyIdent = "args-array",
                            value = LocalGet "new-array",
                            index = I32Const 0
                        },
                        ArrayGet {
                            tyIdent = "args-array",
                            value = LocalGet "new-array",
                            index = I32Const 1
                        }
                    ],
                    fp = StructGet {
                        structIdent = "clos",
                        field = "func-pointer",
                        value = LocalGet "new-clos"
                    }
                })],
                els = [LocalSet ("result", LocalGet "new-clos")]
            },
            LocalGet "result"
        ]
    }

let box = 
    use WasmAST in 
    FunctionDef {
        ident = "box",
        args = [{ident="x", ty=Tyi32 ()}],
        locals = [],
        resultTy = Ref "i32box",
        instructions = [StructNew {
            structIdent = "i32box",
            values = [LocalGet "x"]
        }]
    }

let unbox = 
    use WasmAST in 
    FunctionDef {
        ident = "unbox",
        args = [{ident="box", ty=Anyref ()}],
        locals = [],
        resultTy = Tyi32 (),
        instructions = [StructGet {
            structIdent = "i32box",
            field="value",
            value = RefCast {
                ty = Ref "i32box",
                value = LocalGet "box" 
            }
        }]
    }

let createIntBinop = lam ident. lam instrProducer.
    use WasmAST in 
    FunctionDef {
        ident = ident,
        args = [{ident="lhs", ty=Anyref ()}, {ident="rhs", ty=Anyref()}],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            Call ("box", [
                instrProducer 
                    (Call ("unbox", [RefCast {ty = Ref "i32box", value = LocalGet "lhs"}]))
                    (Call ("unbox", [RefCast {ty = Ref "i32box", value = LocalGet "rhs"}]))
            ])
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

-- let addiWasm = 
--     use WasmAST in
--     FunctionDef {
--         ident = "addi",
--         args = [{ident="lhs", ty=Anyref ()}, {ident="rhs", ty=Anyref()}],
--         locals = [],
--         resultTy = Anyref (),
--         instructions = [
--             Call ("box", [
--                 I32Add(
--                     Call ("unbox", [RefCast {ty = Ref "i32box", value = LocalGet "lhs"}]),
--                     Call ("unbox", [RefCast {ty = Ref "i32box", value = LocalGet "rhs"}])
--                 )
--             ])
--         ]
-- }

mexpr
use WasmPPrint in 
let s = pprintDef 0 apply in
printLn s