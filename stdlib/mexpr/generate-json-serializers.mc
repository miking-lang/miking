-- TODO Comment describing the functionality in the file

include "ast.mc"
include "eq.mc"
include "cmp.mc"
include "boot-parser.mc"
include "pprint.mc"
include "symbolize.mc"

include "json.mc"
include "stdlib.mc"

lang GenerateJsonSerializers = MExprAst + BootParser + MExprSym + MExprCmp

  -- TODO Probably just have Map Type (Expr,Expr) as the base result, to allow
  -- for flexibility. We can have a wrapper function that also does other
  -- things.
  type GJSRes = (Map Type (Name,Name), Expr)

  type GJSEnv = {
    namedTypes: Map Name Expr, -- Expr only TmType
    constructors: Map Name Expr, -- Expr only TmConDef
    jsonLibMap: Map String Name,
    jsonLib: Expr
  }

  -- First Expr is serializer, second is deserializer
  type GJSAcc = Map Type (Expr,Expr)

  sem generateJsonSerializers: Set Type -> Expr -> GJSRes
  sem generateJsonSerializers tys =
  | expr ->
    let jsonLib = _jsonLib () in
    let env: GJSEnv =
      { namedTypes = mapEmpty nameCmp, constructors = mapEmpty nameCmp,
        jsonLibMap = jsonLib.1, jsonLib = jsonLib.0 } in
    let env: GJSEnv = foldPre_Expr_Expr _addType env expr in
    let acc: GJSAcc = mapEmpty cmpType in
    let acc: GJSAcc = setFold (_generateType env) acc tys in
    let funs = join (map (lam t. [t.0,t.1]) (mapValues acc)) in
    let funs = if null funs then unit_ else bindall_ funs in
    let additions = symbolize (bind_ env.jsonLib funs) in
    let expr = bindWithEnd_ expr additions in
    let acc = mapMap (lam v.
        match v with (TmLet t1, TmLet t2) then (t1.ident,t2.ident)
        else error "Impossible"
      ) acc in
    (acc, expr)

  sem _addType: GJSEnv -> Expr -> GJSEnv
  sem _addType env =
  | TmType r & t ->
    { env with namedTypes = mapInsert r.ident t env.namedTypes }
  | TmConDef r & t ->
    { env with constructors = mapInsert r.ident t env.constructors }
  | _ -> env

  sem _generateType: GJSEnv -> GJSAcc -> Type -> GJSAcc
  sem _generateType env acc =
  | TyInt _ & ty ->
    match mapLookup "JsonInt" env.jsonLibMap with Some ji in
    let serializer = ulet_ "serializeJsonInt" (ulam_ "x" (nconapp_ ji (var_ "x"))) in
    -- TODO let deserializer =
    mapInsert ty (serializer,serializer) acc
  | ty -> acc

  sem _addMapping : Set String -> Map String Name -> Expr -> Map String Name
  sem _addMapping names acc =
  | ( TmLet { ident = ident }
    | TmType { ident = ident }
    | TmConDef { ident = ident } ) ->
    mapInsert (nameGetStr ident) ident acc
  | _ -> acc

  sem _jsonLib: () -> (Expr, Map String Name)
  sem _jsonLib =
  | _ ->
    let parse = parseMCoreFile {
      defaultBootParserParseMCoreFileArg with
        eliminateDeadCode = false,
        keepUtests = false
    } in
    let ast = parse (join [stdlibLoc, "/", "json.mc"]) in
    let names = setOfSeq cmpString [
      "JsonValue", "JsonObject", "JsonArray", "JsonString", "JsonFloat",
      "JsonInt", "JsonBool", "JsonNull"
    ] in
    let m = foldPre_Expr_Expr (_addMapping names) (mapEmpty cmpString) ast in
    (ast,m)

end

lang Test = GenerateJsonSerializers + MExprPrettyPrint
end
mexpr
use Test in

let jsonLib = _jsonLib () in

let parseTest = parseMExprString {
  defaultBootParserParseMExprStringArg with
    allowFree = true
} in

let test: Bool -> [Type] -> String -> [(Type,String,String)] -> String -> Bool =
  lam debug. lam tys. lam expr. lam exp1. lam exp2.
  let tys = setOfSeq cmpType tys in
  let expr = parseTest expr in
  let res = generateJsonSerializers tys expr in
  let expr1 = mexprToString res.1 in
  let expr2 = mexprToString (bind_ jsonLib.0 (parseTest exp2)) in
  let m1 = mapMap (lam ntup. (nameGetStr ntup.0, nameGetStr ntup.1)) res.0 in
  let m2 = mapFromSeq cmpType (map (lam t. (t.0,(t.1,t.2))) exp1) in
  (if debug then
     printLn "--- Produced expression ---"; printLn expr1;
     printLn "--- Expected expression ---"; printLn expr2;
     let m1 = join ["[", strJoin "," (map (lam e.
         let t = type2str e.0 in
         let s = (e.1).0 in
         let d = (e.1).1 in
         join ["(", strJoin "," [t,s,d], ")"]
       ) (mapToSeq m1)), "]"] in
     printLn "--- Produced map ---"; printLn m1;
     let m2 = join ["[", strJoin "," (map (lam e.
         let t = type2str e.0 in
         let s = (e.1).0 in
         let d = (e.1).1 in
         join ["(", strJoin "," [t,s,d], ")"]
       ) (mapToSeq m2)), "]"] in
     printLn "--- Expected map ---"; printLn m2
   else ()
  );
  if not (eqString expr1 expr2) then false else
    mapEq (lam v1. lam v2.
        if eqString v1.0 v2.0 then eqString v1.1 v2.1 else false
      ) m1 m2
in

utest test true
  [tyint_]
  "
    let x = 1 in
    x
  "
  [(tyint_,"serializeJsonInt","deserializeJsonInt")]
  "
    let serializeJsonInt =
      lam x.
        JsonInt
          x
    in
    let serializeJsonInt =
      lam x.
        JsonInt
          x
    in
    let x = 1 in
    x
  "
with true in


()
