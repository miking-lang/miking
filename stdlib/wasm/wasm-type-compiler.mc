include "mexpr/pprint.mc"
include "mexpr/lamlift.mc"
include "mexpr/lamlift.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/type-lift.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/symbolize.mc"
include "mexpr/type.mc"
include "mexpr/type-check.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

include "wasm-ast.mc"
include "wasm-pprint.mc"
include "wasm-stdlib.mc"
include "wasm-apply.mc"
include "mclos-ast.mc"
include "mclos-transpile.mc"

include "string.mc"
include "seq.mc"
include "map.mc"
include "tuple.mc"
include "assoc-seq.mc"

let fst = lam pair. 
    match pair with (f, _) in f

let snd = lam pair. 
    match pair with (_, n) in n

let pprintTuple = lam kv. 
    use MClosAst in 
    (match snd kv with TyVariant {constrs = constrs} 
        then iter (lam x. printLn "constr") (mapToSeq constrs) 
        else (printLn "Not a variant")) ; 
    use MExprPrettyPrint in 
    let nameStr = nameGetStr (fst kv) in
    let tyStr = type2str (snd kv) in 
    printLn (join ["typedef ", nameStr, " = ", tyStr])

type WasmTypeContext = {
    defs: [(use WasmAST in Def)]
}

let emptyTypeCtx = {
    defs = []
}

lang WasmTypeCompiler = MClosAst + WasmAST + MExprPrettyPrint
    sem compileTypes : (AssocSeq Name Type) -> WasmTypeContext
    sem compileTypes = 
    | env -> foldl compileType emptyTypeCtx env
        -- iter pprintTuple env ;
        -- Module {
        --     definitions = [],
        --     table = Table {size = 0, typeString = "funcref"},
        --     elem = Elem {offset = I32Const 0, funcNames = []},
        --     types = [],
        --     exports = []
        -- }

    sem compileType : WasmTypeContext -> (Name, Type) -> WasmTypeContext
    sem compileType ctx =
    | (name, TyVariant {constrs = constrs}) -> 
        let constr2def = lam constrPair.
            StructTypeDef {
                ident = nameGetStr (fst constrPair),
                fields = [
                    {ident = "value", ty = Anyref ()},
                    {ident = "_typeid", ty = Anyref ()}
                ]
            } in
        let constrPairs = mapToSeq constrs in 
        {ctx with defs = concat ctx.defs (map constr2def constrPairs)}
end
