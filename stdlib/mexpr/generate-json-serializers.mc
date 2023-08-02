-- TODO Comment describing the functionality in the file

include "ast.mc"
include "eq.mc"
include "cmp.mc"
include "boot-parser.mc"
include "pprint.mc"
include "symbolize.mc"
include "utils.mc"

include "json.mc"
include "stdlib.mc"

lang GenerateJsonSerializers =
  MExprAst + BootParser + MExprSym + MExprCmp + MExprFindSym + GetConDefType

  type GJSRes = Map Type {
      serializerName: Option Name, serializer: Expr,
      deserializerName: Option Name, deserializer: Expr
    }

  type GJSEnv = {
    namedTypes: Map Name Expr, -- Expr only TmTypes
    constructors: Map Name [Expr], -- [Expr] only TmConDefs
    jsonLib: Expr,
    -- For easy access to serializer/deserializer function names in jsonLib
    sBool: Name, dBool: Name, sInt: Name, dInt: Name,
    sFloat: Name, dFloat: Name, sChar: Name, dChar: Name,
    sString: Name, dString: Name, sSeq: Name, dSeq: Name,
    sTensor: Name, dTensor: Name
  }

  sem generateJsonSerializers: Set Type -> Expr -> GJSRes
  sem generateJsonSerializers tys =
  | expr ->
    let jsonLib = _jsonLib () in
    match findNamesOfStringsExn [
        "jsonSerializeBool", "jsonDeserializeBool", "jsonSerializeInt",
        "jsonDeserializeInt", "jsonSerializeFloat", "jsonDeserializeFloat",
        "jsonSerializeChar", "jsonDeserializeChar", "jsonSerializeString",
        "jsonDeserializeString", "jsonSerializeSeq", "jsonDeserializeSeq",
        "jsonSerializeTensor", "jsonDeserializeTensor"
      ] jsonLib with [
        sBool, dBool, sInt, dInt, sFloat, dFloat, sChar, dChar,
        sString, dString, sSeq, dSeq, sTensor, dTensor
      ] in
    let env: GJSEnv = {
      namedTypes = mapEmpty nameCmp, constructors = mapEmpty nameCmp,
      jsonLib = jsonLib,
      sBool = sBool, dBool = dBool, sInt = sInt, dInt = dInt,
      sFloat = sFloat, dFloat = dFloat, sChar = sChar, dChar = dChar,
      sString = sString, dString = dString, sSeq = sSeq, dSeq = dSeq,
      sTensor = sTensor, dTensor = dTensor
    } in
    let env: GJSEnv = foldPre_Expr_Expr _addType env expr in
    let acc: GJSRes = mapEmpty cmpType in
    let acc: GJSRes = setFold (_generateType env) acc tys in
    -- let funs = join (map (lam t. [t.0,t.1]) (mapValues acc)) in
    -- let funs = if null funs then unit_ else bindall_ funs in
    -- let additions = bind_ env.jsonLib funs in
    -- let expr = bindWithEnd_ expr additions in
    -- let acc = mapMap (lam v.
    --     match v with (TmLet t1, TmLet t2) then (t1.ident,t2.ident)
    --     else error "Impossible"
    --   ) acc in
    acc

  sem _addType: GJSEnv -> Expr -> GJSEnv
  sem _addType env =
  | TmType r & t ->
    { env with namedTypes = mapInsert r.ident t env.namedTypes }
  | TmConDef r & t ->
    match getConDefType r.tyIdent with TyCon c then
      let ident = c.ident in
      let condefs =
        match mapLookup ident env.constructors with Some condefs then condefs
        else []
      in
      { env with constructors = mapInsert ident (cons t condefs) env.constructors }
    else error "Not a TyCon at RHS of TmConDef type"
  | _ -> env

  sem _baseSerializer env =
  | TyBool _ -> env.sBool | TyInt _ -> env.sInt | TyFloat _ -> env.sFloat
  | TyChar _ -> env.sChar | TySeq { ty = TyChar _ } -> env.sString
  | TySeq _ -> env.sSeq | TyTensor _ -> env.sTensor

  sem _baseDeserializer env =
  | TyBool _ -> env.dBool | TyInt _ -> env.dInt | TyFloat _ -> env.dFloat
  | TyChar _ -> env.dChar | TySeq { ty = TyChar _ } -> env.dString
  | TySeq _ -> env.dSeq | TyTensor _ -> env.dTensor

  sem _generateType: GJSEnv -> GJSRes -> Type -> GJSRes
  sem _generateType env acc =
  | ty -> if mapMem ty acc then acc else _generateTypeH env acc ty

  sem _generateTypeH: GJSEnv -> GJSRes -> Type -> GJSRes
  sem _generateTypeH env acc =
  | TyVar _ -> error "TODO"
  | ( TyBool _ | TyInt _ | TyFloat _ | TyChar _ ) & ty ->
    mapInsert ty {
        serializerName = None (), serializer = nvar_ (_baseSerializer env ty),
        deserializerName = None (), deserializer = nvar_ (_baseDeserializer env ty)
      } acc
  | TySeq { ty = TyChar _ } & ty ->
    mapInsert ty {
        serializerName = None (), serializer = nvar_ (_baseSerializer env ty),
        deserializerName = None (), deserializer = nvar_ (_baseDeserializer env ty)
      } acc
  | TySeq t & ty ->
    let acc = _generateType env acc t.ty in
    let inner = mapFindExn t.ty acc in
    let serializerName = None () in
    let serializer = appf1_ (nvar_ (_baseSerializer env ty))
                       (match inner.serializerName with Some n then nvar_ n else inner.serializer) in
    let deserializerName = None () in
    let deserializer = appf1_ (nvar_ (_baseDeserializer env ty))
                         (match inner.deserializerName with Some n then nvar_ n else inner.deserializer) in
    mapInsert ty {
        serializerName = serializerName, serializer = serializer,
        deserializerName = deserializerName, deserializer = deserializer
      } acc
    -- | TyTensor _) & ty -> TODO Basically the same as TySeq

  sem _jsonLib: () -> Expr
  sem _jsonLib =
  | _ ->
    let parse = parseMCoreFile {
      defaultBootParserParseMCoreFileArg with
        eliminateDeadCode = false,
        keepUtests = false
    } in
    let ast = parse (join [stdlibLoc, "/", "json.mc"]) in
    symbolize ast

end

lang Test = GenerateJsonSerializers + MExprPrettyPrint + MExprEq
end
mexpr
use Test in

let jsonLib = _jsonLib () in

let parseTest = parseMExprString {
  defaultBootParserParseMExprStringArg with
    allowFree = true
} in

let debugPrintGJSRes: GJSRes -> () = lam res.
  mapMapWithKey (lam k. lam v.
     printLn (join [
       "Type: ", type2str k, "\n",
       match v.serializerName with Some n then
         join ["serializerName: ", nameGetStr n, "\n"]
       else "serializerName:\n",
       "serializer: \n", mexprToString v.serializer, "\n",
       match v.deserializerName with Some n then
         join ["deserializerName: ", nameGetStr n, "\n"]
       else "deserializerName:\n",
       "deserializer: \n", mexprToString v.deserializer, "\n"
     ]
    )) res; ()
in

let test: Bool -> [Type] -> String -> [(Type,String,String,String,String)] -> Bool =
  lam debug. lam tys. lam expr. lam expected.
  let tys = setOfSeq cmpType tys in
  let expr = parseTest expr in
  let res: GJSRes = generateJsonSerializers tys expr in
  let expected: GJSRes = foldl (lam m. lam t.
      mapInsert t.0 {
        serializerName = if null t.1 then None () else Some (nameNoSym t.1),
        serializer = parseTest t.2,
        deserializerName = if null t.3 then None () else Some (nameNoSym t.3),
        deserializer = parseTest t.4
      } m
    ) (mapEmpty cmpType) expected in
  (if debug then
     printLn "--- Result ---"; debugPrintGJSRes res;
     printLn "--- Expected ---"; debugPrintGJSRes expected
   else ()
  );
  mapEq (lam r. lam e.
      if optionEq nameEqStr r.serializerName e.serializerName then
        if optionEq nameEqStr r.deserializerName e.deserializerName then
          if eqExpr r.serializer e.serializer then
            eqExpr r.deserializer e.deserializer
          else false
        else false
      else false
    ) res expected
in

-- Base types. The specific names of the expressions are not actually checked,
-- only the expression structure (due to eqExpr).
utest test false
  [tybool_,tyint_,tyfloat_,tychar_,tystr_]
  "()"
  [
    (tybool_,
       "","jsonSerializeBool",
       "","jsonDeserializeBool"),
    (tyint_,
       "","jsonSerializeInt",
       "","jsonDeserializeInt"),
    (tyfloat_,
       "","jsonSerializeFloat",
       "","jsonDeserializeFloat"),
    (tychar_,
       "","jsonSerializeChar",
       "","jsonDeserializeChar"),
    (tystr_,
       "","jsonSerializeString",
       "","jsonDeserializeString")
  ]
with true in
utest test false
  [tyseq_ tyint_]
  "()"
  [
    (tyint_,
       "","jsonSerializeInt",
       "","jsonDeserializeInt"),
    (tyseq_ tyint_,
       "","jsonSerializeSeq jsonSerializeInt",
       "","jsonDeserializeSeq jsonDeserializeInt")
  ]
with true in

-- utest test false
--   [tycon_ "Option"]
--   "
--     type Option a in
--     con Some : all a. a -> Option a in
--     con None : all a. () -> Option a in
--     ()
--   "
--   [
--     (tycon_ "Option",
--        "someSerializerName","
--          lam f. lam x.
--            match x with Some a then JSONObject {type = Option, constr = Some, data = f a}
--            else match x with None a then JSONObject {type = Option, constr = None, data = serializerforEmptyRecord () }
--            else never
--        ",
--        "someDeserializerName","
--          lam f. lam x.
--            match x with JSONObject { type = Option, constr = constr, data = data } then
--              match constr with Some then
--                match f data with Some data then Some (Some data) else None ()
--              else match constr with None then
--                match deserializerforEmptyRecord () with Some data then Some (None data) else None ()
--            else None ()
--        ")
--   ]
-- with true in

()

