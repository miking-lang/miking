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

type WasmTypeContext = {
    constr2typeid: Map Name Int,
    defs : [(use WasmAST in Def)],
    -- We expect the value list to be sorted by the SID of the
    -- String value of the Name.
    record2fields: Map Name [Name]
}

let emptyTypeCtx = {
    defs = [],
    constr2typeid = mapEmpty nameCmp,
    record2fields = mapEmpty nameCmp
}

lang WasmTypeCompiler = MClosAst + WasmAST + MExprPrettyPrint
    sem compileTypes : (AssocSeq Name Type) -> WasmTypeContext
    sem compileTypes = 
    | env -> foldl compileType emptyTypeCtx env

    sem compileType : WasmTypeContext -> (Name, Type) -> WasmTypeContext
    sem compileType ctx =
    | (name, TyVariant {constrs = constrs}) -> 

        let constr2def = lam constrPair.
            StructTypeDef {
                ident = fst constrPair,
                fields = [
                    {ident = nameNoSym "value", ty = Anyref ()},
                    {ident = nameNoSym "_typeid", ty = Tyi32 ()}
                ]
            } in
        let constrPairs = mapToSeq constrs in 
        let newMap = foldli 
            (lam m. lam i. lam c. mapInsert (fst c) i m)
            ctx.constr2typeid
            constrPairs in 
        {ctx with 
            constr2typeid = newMap,
            defs = concat ctx.defs (map constr2def constrPairs)}
    | (name, TyRecord {fields = f}) ->
        let f = mapToSeq f in  
        let f = map (lam pair. pair.0) f in 
        -- The fields of the record are ordered by 
        -- the SIDs of the record field identifiers
        let f = sort cmpSID f in 
        let f = map sidToString f in 
        let f = map nameNoSym f in 
        let str2field = lam s. {ident = s, ty = Anyref ()} in 

        let ctx = {ctx with record2fields = mapInsert name f ctx.record2fields} in 

        {ctx with defs = cons (StructTypeDef {
            ident = name, 
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
    | (name,  TyApp _) -> 
        error "TyApp" ;
        ctx
    | (name, TyBool _) -> 
        error "TyBool" 
    | (name, TyInt _) -> 
        error "TyInt" 
    | (name, TyFloat _) -> 
        error "TyFloat" 
    | (name, TyChar _) ->
        error "TyChar" 
    | (name, TySeq _) -> 
        error "TySeq" 
    | (name, ty) ->
        -- printLn (type2str ty) ; 
        error (join ["unknown typedef for '", nameGetStr name, "'!"]) ;
        ctx
end
