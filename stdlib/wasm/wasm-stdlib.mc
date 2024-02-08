include "wasm-ast.mc"
include "wasm-pprint.mc"

let i32boxDef = 
    use WasmAST in 
    StructTypeDef {
        ident = "i32box",
        fields = [{
            ident = "value",
            ty = Tyi32 ()
        }]
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
