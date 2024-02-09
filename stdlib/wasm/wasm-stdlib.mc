include "wasm-ast.mc"
include "wasm-pprint.mc"

let createIntBinop = lam ident. lam instrProducer.
    use WasmAST in 
    FunctionDef {
        ident = ident,
        args = [{ident="lhs", ty=Anyref ()}, {ident="rhs", ty=Anyref()}],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                instrProducer 
                    (I31GetS (RefCast {ty = I31Ref (), value = LocalGet "lhs"}))
                    (I31GetS (RefCast {ty = I31Ref(), value = LocalGet "rhs"}))
            )
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
