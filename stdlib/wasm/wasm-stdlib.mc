include "wasm-ast.mc"
include "wasm-pprint.mc"

let closType = 
    use WasmAST in (StructTypeDef {
    ident = "clos",
    fields = [
        {ident = "func-pointer", ty = Tyi32 ()},
        {ident = "max-arity", ty = Tyi32 ()},
        {ident = "cur-arity", ty = Tyi32 ()},
        {ident = "args", ty = Array (Anyref ())}
    ]})

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
                    I32Add (
                        I32Const 1,
                        StructGet {
                            structIdent = "clos",
                            field = "cur-arity",
                            value = LocalGet "cl"
                        }
                    ),
                    StructGet {
                        structIdent = "clos",
                        field = "max-arity",
                        value = LocalGet "cl"
                    },
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

mexpr
use WasmPPrint in 
let s = pprintDef 0 apply in
printLn s