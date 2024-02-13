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

let fst : all a. all b. (a, b) -> a = lam x. x.0
let snd : all a. all b. (a, b) -> b = lam x. x.1

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
    name2ident : Map Name String,
    constr2typeid: Map String Int,
    defs : [(use WasmAST in Def)]
}

let emptyTypeCtx = {
    defs = [],
    name2ident = mapEmpty nameCmp,
    constr2typeid = mapEmpty cmpString
}

lang WasmTypeCompiler = MClosAst + WasmAST + MExprPrettyPrint
    sem compileTypes : (AssocSeq Name Type) -> WasmTypeContext
    sem compileTypes = 
    | env -> 
        -- iter pprintTuple env ;    
        foldl compileType emptyTypeCtx env
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
                ident = join [
                    nameGetStr name,
                    "-",
                    nameGetStr (fst constrPair)
                ],
                fields = [
                    {ident = "value", ty = Anyref ()},
                    {ident = "_typeid", ty = Tyi32 ()}
                ]
            } in
        let constrPairs = mapToSeq constrs in 
        let newMap = foldli 
            (lam m. lam i. lam c. mapInsert (nameGetStr (fst c)) i m)
            ctx.constr2typeid
            constrPairs in 
        {ctx with 
            constr2typeid = newMap,
            defs = concat ctx.defs (map constr2def constrPairs)}
    | (name, TyRecord {fields = f}) ->
        let f = mapToSeq f in  
        let f = map (lam pair. pair.0) f in 
        let f = map sidToString f in 
        let str2field = lam s. {ident = s, ty = Anyref ()} in 
        {ctx with defs = cons (StructTypeDef {
            ident = nameGetStr name, 
            fields = map str2field f
        }) ctx.defs}
    | (name, TyVar {ident = ident}) -> 
        error "TyVar" ;
        ctx
    | (name, TyAlias _) -> 
        error "TyAlias" ;
        ctx
    | (name, TyUnknown _) -> 
        error "TyUnknown" ;
        ctx
    | (name,  TyArrow _) -> 
        error "TyArrow" ;
        ctx
    | (name,  TyCon {ident = ident}) -> 
        error "TyCon"
        -- let newMap = mapInsert name (nameGetStr ident) ctx.name2ident in
        -- {ctx with name2ident = newMap}
    | (name,  TyApp _) -> 
        error "TyApp" ;
        ctx
    | (name, ty) ->
        printLn (type2str ty) ; 
        error (join ["unknown typedef for '", nameGetStr name, "'!"]) ;
        ctx
end
