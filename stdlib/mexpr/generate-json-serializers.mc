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

  type Res = (Map Type (Name,Name), Expr)

  sem generateJsonSerializers: Set Type -> Expr -> Res
  sem generateJsonSerializers tys =
  | expr -> (mapEmpty cmpType, expr)

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
    let ast = symbolize (parse (join [stdlibLoc, "/", "json.mc"])) in
    let names = setOfSeq cmpString [
      "JsonValue", "JsonObject", "JsonArray", "JsonString", "JsonFloat",
      "JsonInt", "JsonBool", "JsonNull", "jsonParseExn", "json2string"
    ] in
    let m = foldPre_Expr_Expr (_addMapping names) (mapEmpty cmpString) ast in
    (ast,m)

end

lang Test = GenerateJsonSerializers + MExprPrettyPrint
end
mexpr
use Test in

let jsonLib = _jsonLib () in

let parseTest = parseMExprString defaultBootParserParseMExprStringArg in

let test: Bool -> [Type] -> String -> [(Type,String,String)] -> String -> Bool =
  lam debug. lam tys. lam expr. lam exp1. lam exp2.
  let tys = setOfSeq cmpType tys in
  let expr = parseTest expr in
  let res = generateJsonSerializers tys expr in
  let expr1 = mexprToString res.1 in
  let expr2 = mexprToString (parseTest exp2) in
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
    let x = 1 in
    x
  "
with true in


()
