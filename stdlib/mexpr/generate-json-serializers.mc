-- TODO Comment describing the functionality in the file

include "ast.mc"
include "eq.mc"
include "cmp.mc"
include "boot-parser.mc"
include "pprint.mc"
include "symbolize.mc"
include "type.mc"
include "utils.mc"
include "duplicate-code-elimination.mc"

include "json.mc"
include "stdlib.mc"
include "stringid.mc"
include "map.mc"

let constructorKey = "__constructor__"
let dataKey = "__data__"

lang GenerateJsonSerializers =
  MExprAst + BootParser + MExprSym + MExprCmp + MExprFindSym + AppTypeUtils
  + MExprEliminateDuplicateCode

  type GJSSerializer = {
    serializer: Expr,
    deserializer: Expr
  }

  type GJSRes = Map Type GJSSerializer


  type GJSNamedSerializer = {
    serializerName: Name, serializer: Option Expr,
    deserializerName: Name, deserializer: Option Expr
  }

  type GJSAcc = Map Name GJSNamedSerializer -- The keys are only names of TyCon

  type GJSEnv = {

    -- Information from the given program
    namedTypes: Map Name Expr, -- Expr only TmTypes
    constructors: Map Name [Expr], -- [Expr] only TmConDefs

    -- Required libraries for the generation
    lib: Expr,

    -- Type variables currently bound
    varEnv: Map Name GJSSerializer,

    -- For easy access to lib names
    sBool: Name, dBool: Name, sInt: Name, dInt: Name,
    sFloat: Name, dFloat: Name, sChar: Name, dChar: Name,
    sString: Name, dString: Name, sSeq: Name, dSeq: Name,
    sTensor: Name, dTensorInt: Name, dTensorFloat: Name, dTensorDense: Name,
    jsonObject: Name, jsonString: Name,
    jsonParse: Name, jsonParseExn: Name, json2string: Name,
    mapInsert: Name, mapEmpty: Name, mapLookup: Name,
    cmpString: Name,
    some: Name, none: Name

  }

  sem addJsonSerializers: [Type] -> Expr -> (GJSRes, Expr, GJSEnv)
  sem addJsonSerializers tys =
  | expr ->
    match generateJsonSerializers tys expr with (acc, res, env) in
    let lib = env.lib in
    let eta = lam expr.
      match expr with TmLam _ then expr
      else let n = nameSym "x" in nulam_ n (app_ expr (nvar_ n))
    in
    let bs = join (map (lam s.
        [(s.serializerName,
          match s.serializer with Some s then eta s else error "Empty serializer"),
         (s.deserializerName,
          match s.deserializer with Some d then eta d else error "Empty deserializer")])
      (mapValues acc))
    in
    let rl = nureclets_ bs in
    let expr = bind_ expr lib in
    let expr = bind_ expr rl in
    let expr = eliminateDuplicateCode expr in
    (res,expr,env)

  -- Generate JSON serializers and deserializers. Returns an accumulator of
  -- generated functions and a map from types to serializers/deserializers
  sem generateJsonSerializers: [Type] -> Expr -> (GJSAcc, GJSRes, GJSEnv)
  sem generateJsonSerializers tys =
  | expr ->
    let lib = _lib () in
    match findNamesOfStringsExn [
        "jsonSerializeBool", "jsonDeserializeBool",
        "jsonSerializeInt", "jsonDeserializeInt",
        "jsonSerializeFloat", "jsonDeserializeFloat",
        "jsonSerializeChar", "jsonDeserializeChar",
        "jsonSerializeString", "jsonDeserializeString",
        "jsonSerializeSeq", "jsonDeserializeSeq",
        "jsonSerializeTensor",
        "jsonDeserializeTensorCArrayInt","jsonDeserializeTensorCArrayFloat",
        "jsonDeserializeTensorDense",
        "JsonObject", "JsonString",
        "jsonParse", "jsonParseExn", "json2string",
        "mapInsert", "mapEmpty", "mapLookup",
        "cmpString",
        "Some", "None"
      ] lib with [
        sb, db,
        si, di,
        sf, df,
        sc, dc,
        ss, ds,
        ssq, dsq,
        st, dti, dtf, dtd,
        jo, js,
        jp,jpe,j2s,
        mi,me,ml,
        cs,
        s,n
      ] in
    let env: GJSEnv = {
      namedTypes = mapEmpty nameCmp, constructors = mapEmpty nameCmp,
      lib = lib,
      varEnv = mapEmpty nameCmp,
      sBool = sb, dBool = db, sInt = si, dInt = di,
      sFloat = sf, dFloat = df, sChar = sc, dChar = dc,
      sString = ss, dString = ds, sSeq = ssq, dSeq = dsq,
      sTensor = st, dTensorInt = dti, dTensorFloat = dtf, dTensorDense = dtd,
      jsonObject = jo, jsonString = js,
      jsonParse = jp, jsonParseExn = jpe, json2string = j2s,
      mapInsert = mi, mapEmpty = me, mapLookup = ml,
      cmpString = cs,
      some = s, none = n
    } in
    let env: GJSEnv = foldPre_Expr_Expr _addType env expr in
    let acc: GJSAcc = mapEmpty nameCmp in
    let r: (GJSAcc, GJSRes) =
      foldl (lam t. lam ty.
          match _generateType env t.0 ty with (acc,s) in
          (acc, mapInsert ty s t.1)
        ) (acc, mapEmpty cmpType) tys
    in
    (r.0, r.1, env)

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

  sem _generateType: GJSEnv -> GJSAcc -> Type -> (GJSAcc, GJSSerializer)
  sem _generateType env acc =

  -- Basic types
  | TyBool _ ->
    let s = { serializer = nvar_ env.sBool, deserializer = nvar_ env.dBool } in
    (acc, s)
  | TyInt _ ->
    let s = { serializer = nvar_ env.sInt, deserializer = nvar_ env.dInt } in
    (acc, s)
  | TyFloat _ ->
    let s = { serializer = nvar_ env.sFloat, deserializer = nvar_ env.dFloat } in
    (acc, s)
  | TyChar _ ->
    let s = { serializer = nvar_ env.sChar, deserializer = nvar_ env.dChar } in
    (acc, s)
  | TySeq { ty = TyChar _ } ->
    let s = { serializer = nvar_ env.sString, deserializer = nvar_ env.dString } in
    (acc, s)

  -- Builtin type constructors
  | TySeq { ty = ! TyChar _ & tyi } & ty->
    match _generateType env acc tyi with (acc, si) in
    let serializer = appf1_ (nvar_ env.sSeq) si.serializer in
    let deserializer = appf1_ (nvar_ env.dSeq) si.deserializer in
    let s = { serializer = serializer, deserializer = deserializer } in
    (acc, s)
  | TyTensor { ty = tyi } & ty ->
    match _generateType env acc tyi with (acc, si) in
    let serializer = appf1_ (nvar_ env.sTensor) si.serializer in
    let dTensor =
      switch tyi
      case TyInt _ then env.dTensorInt
      case TyFloat _ then env.dTensorFloat
      case _ then env.dTensorDense
      end
    in
    let deserializer = appf1_ (nvar_ dTensor) si.deserializer in
    let s = { serializer = serializer, deserializer = deserializer } in
    (acc, s)

  -- Records
  | TyRecord t ->
    match mapMapAccum (lam acc. lam k. _generateType env acc) acc t.fields
    with (acc,iss) in
    let sarg = nameSym "r" in
    let m = nameSym "m" in
    let serializer =
      nulam_ sarg (
        (nconapp_ env.jsonObject
          (mapFoldWithKey (lam acc. lam k. lam s.
               let k = sidToString k in
               (appf3_ (nvar_ env.mapInsert)
                  (str_ k)
                  (app_ s.serializer (recordproj_ k (nvar_ sarg)))
                  acc))
             (app_ (nvar_ env.mapEmpty) (nvar_ env.cmpString)) iss)))
    in
    let darg = nameSym "jr" in
    let m = nameSym "m" in
    let iss = mapMap (lam s. (s,nameSym "rv")) iss in
    let inner = nconapp_ env.some
      (urecord_ (map (lam t. (sidToString t.0, (nvar_ (t.1).1))) (mapToSeq iss))) in
    let none = nconapp_ env.none unit_ in
    let deserializer =
      nulam_ darg (
          match_
            (nvar_ darg)
            (npcon_ env.jsonObject (npvar_ m))
            (mapFoldWithKey (lam acc. lam k. lam v.
                let k = sidToString k in
                let jrv = nameSym "jrv" in
                match_
                  (appf2_ (nvar_ env.mapLookup) (str_ k) (nvar_ m))
                  (npcon_ env.some (npvar_ jrv))
                  (match_
                    (app_ (v.0).deserializer (nvar_ jrv))
                    (npcon_ env.some (npvar_ v.1))
                    acc
                    none)
                  none)
              inner iss)
            none)
    in
    let s = { serializer = serializer, deserializer = deserializer } in
    (acc, s)

  | TyVar t ->
    match mapLookup t.ident env.varEnv with Some s then (acc,s)
    else error (join ["Type variable not found in environment: ", nameGetStr t.ident])
  | TyCon t ->
    match mapLookup t.ident acc with Some s then
      (acc, { serializer = nvar_ s.serializerName,
              deserializer = nvar_ s.deserializerName })
    else
      match mapLookup t.ident env.namedTypes with Some TmType tt then

        -- Variant type case
        match tt.tyIdent with TyVariant _ then
          match mapLookup t.ident env.constructors with Some tmConDefs then
            let pss =
              map (lam p. { sf = nameSym "sf", df = nameSym "df" }) tt.params
            in
            let serializerName = nameSym (join ["serialize", nameGetStr t.ident]) in
            let deserializerName = nameSym (join ["deserialize", nameGetStr t.ident]) in
            let acc = mapInsert t.ident {
                serializerName = serializerName,
                deserializerName = deserializerName,
                serializer = None (),
                deserializer = None ()
              } acc
            in
            match mapAccumL (lam acc. lam tcd.
                let tcd = match tcd with TmConDef tcd then tcd
                          else error "Impossible" in
                match stripTyAll tcd.tyIdent with (tyalls,tyIdent) in
                let varEnv = foldl2 (lam varEnv. lam ta. lam ps.
                    match ta with (n,_) in
                    mapInsert n { serializer = nvar_ ps.sf,
                                  deserializer = nvar_ ps.df } varEnv
                  ) env.varEnv tyalls pss in
                let env = { env with varEnv = varEnv } in
                match tyIdent with TyArrow t then
                  match _generateType env acc t.from with (acc, s) in
                  (acc, { name = tcd.ident, p = nameSym "d", s = s })
                else error "Not an arrow type in TmConDef"
              ) acc tmConDefs
            with (acc, conDefs) in
            let sarg = nameSym "c" in
            let serializer = nulams_ (map (lam ps. ps.sf) pss) (
                nulam_ sarg (
                  foldl (lam acc. lam cd.
                    match_
                      (nvar_ sarg)
                      (npcon_ cd.name (npvar_ cd.p))
                      (nconapp_ env.jsonObject
                        (appf3_ (nvar_ env.mapInsert)
                           (str_ constructorKey)
                           (nconapp_ env.jsonString (str_ (nameGetStr cd.name)))
                           (appf3_ (nvar_ env.mapInsert)
                              (str_ dataKey)
                              (app_ (cd.s).serializer (nvar_ cd.p))
                              (app_ (nvar_ env.mapEmpty) (nvar_ env.cmpString)))))
                      acc) never_ conDefs
                ))
            in
            let darg = nameSym "jc" in
            let none = nconapp_ env.none unit_ in
            let mv = nameSym "m" in
            let cv = nameSym "con" in
            let deserializer = nulams_ (map (lam ps. ps.df) pss) (
                nulam_ darg (
                  match_
                    (nvar_ darg)
                    (npcon_ env.jsonObject (npvar_ mv))
                    (match_
                      (appf2_ (nvar_ env.mapLookup) (str_ constructorKey) (nvar_ mv))
                      (npcon_ env.some (npcon_ env.jsonString (npvar_ cv)))
                      (foldl (lam acc. lam cd.
                         match_
                           (nvar_ cv)
                           (pstr_ (nameGetStr cd.name))
                           (let dv = nameSym "data" in
                            match_
                              (appf2_ (nvar_ env.mapLookup) (str_ dataKey) (nvar_ mv))
                              (npcon_ env.some (npvar_ dv))
                              (let d = nameSym "d" in
                               match_
                                 (app_ (cd.s).deserializer (nvar_ dv))
                                 (npcon_ env.some (npvar_ d))
                                 (nconapp_ env.some (nconapp_ cd.name (nvar_ d)))
                                 none)
                               none)
                           acc) none conDefs)
                      none)
                    none))
            in
            let acc = mapInsert t.ident {
                serializerName = serializerName,
                serializer = Some serializer,
                deserializerName = deserializerName,
                deserializer = Some deserializer
              } acc in
            let s = { serializer = nvar_ serializerName,
                      deserializer = nvar_ deserializerName } in
            (acc, s)

          else error (join ["Incorrect variant type: ", nameGetStr t.ident])

        -- Other types (cannot be self-recursive)
        else
          let params = map (lam p. { sf = nameSym "sf", df = nameSym "df", p = p })
                         tt.params in
          let varEnv = foldl (lam env. lam p.
              mapInsert p.p { serializer = nvar_ p.sf, deserializer = nvar_ p.df }
                env
            ) env.varEnv params
          in
          match _generateType {env with varEnv = varEnv } acc tt.tyIdent
          with (acc, si) in
          let serializer = foldl (lam s. lam p. nulam_ p.sf s) si.serializer params in
          let deserializer = foldl (lam d. lam p. nulam_ p.df d) si.deserializer params in
          let acc = mapInsert t.ident {
              serializerName = nameSym (join ["serialize", nameGetStr t.ident]),
              serializer = Some serializer,
              deserializerName = nameSym (join ["deserialize", nameGetStr t.ident]),
              deserializer = Some deserializer
            } acc in
          let s = { serializer = serializer, deserializer = deserializer } in
          (acc, s)

      else error (join ["Unknown type: ", nameGetStr t.ident])

  | TyApp t ->
    match _generateType env acc t.lhs with (acc, sl) in
    match _generateType env acc t.rhs with (acc, sr) in
    let s = { serializer = app_ sl.serializer sr.serializer,
              deserializer = app_ sl.deserializer sr.deserializer } in
    (acc, s)
  | ( TyUnknown _ | TyArrow _ | TyAll _ | TyAlias _ | TyVariant _ ) ->
    error "Not supported when generating JSON serializers"

  sem _lib: () -> Expr
  sem _lib =
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

let parseTest = parseMExprStringExn {
  defaultBootParserParseMExprStringArg with
    allowFree = true
} in

let debugTestPrint: GJSAcc -> GJSRes -> () = lam acc. lam res.
  printLn "## Acc";
  mapMapWithKey (lam k. lam v.
     printLn (join [
       "TyCon name: ", nameGetStr k, "\n",
       "serializerName: ", nameGetStr v.serializerName, "\n",
       match v.serializer with Some s then
         join ["serializer:\n", mexprToString s, "\n"]
       else "serializer:\n",
       "deserializerName: ", nameGetStr v.deserializerName, "\n",
       match v.deserializer with Some s then
         join ["deserializer:\n", mexprToString s, "\n"]
       else "deserializer:\n"
     ]
    )) acc;
  printLn "## Res";
  mapMapWithKey (lam k. lam v.
     printLn (join [
       "Type: ", type2str k, "\n",
       "serializer:\n", mexprToString v.serializer, "\n",
       "deserializer:\n", mexprToString v.deserializer, "\n"
     ]
    )) res;
  ()
in

let test: Bool -> [Type] -> String -> [(String,String,String,String,String)]
          -> [(Type,String,String)] -> Bool =
  lam debug. lam tys. lam expr. lam eAcc. lam eRes.
  let expr = parseTest expr in
  match generateJsonSerializers tys expr with (acc,res,_) in
  let eAcc: GJSAcc = foldl (lam m. lam t.
      mapInsert (nameNoSym t.0) {
        serializerName = nameNoSym t.1,
        serializer = if null t.2 then None () else Some (parseTest t.2),
        deserializerName = nameNoSym t.3,
        deserializer = if null t.4 then None () else Some (parseTest t.4)
      } m
    ) (mapEmpty nameCmp) eAcc
  in
  let eRes: GJSRes = foldl (lam m. lam t.
      mapInsert t.0 {
        serializer = parseTest t.1,
        deserializer = parseTest t.2
      } m
    ) (mapEmpty cmpType) eRes
  in
  (if debug then
     printLn "# Output"; debugTestPrint acc res;
     printLn "# Expected"; debugTestPrint eAcc eRes
   else ()
  );
  let eq1 =
    mapEq (lam r. lam e.
        if nameEqStr r.serializerName e.serializerName then
          if nameEqStr r.deserializerName e.deserializerName then
            if optionEq eqExpr r.serializer e.serializer then
              optionEq eqExpr r.deserializer e.deserializer
            else false
          else false
        else false
      ) acc eAcc
  in
  if eq1 then
    mapEq (lam r. lam e.
            if eqExpr r.serializer e.serializer then
              eqExpr r.deserializer e.deserializer
            else false
      ) res eRes
  else false

in

-- Base types. The specific names of the expressions are not actually checked,
-- only the expression structure (due to eqExpr).
utest test false
  [tybool_,tyint_,tyfloat_,tychar_,tystr_]
  "()"
  []
  [
    (tybool_,
       "jsonSerializeBool",
       "jsonDeserializeBool"),
    (tyint_,
       "jsonSerializeInt",
       "jsonDeserializeInt"),
    (tyfloat_,
       "jsonSerializeFloat",
       "jsonDeserializeFloat"),
    (tychar_,
       "jsonSerializeChar",
       "jsonDeserializeChar"),
    (tystr_,
       "jsonSerializeString",
       "jsonDeserializeString")
  ]
with true in

-- Sequences and tensors
utest test false
  [tyseq_ tyint_, tytensor_ tyint_, tytensor_ tyfloat_, tytensor_ tybool_]
  "()"
  []
  [
    (tyseq_ tyint_,
       "jsonSerializeSeq jsonSerializeInt",
       "jsonDeserializeSeq jsonDeserializeInt"),
    (tytensor_ tyint_,
       "jsonSerializeTensor jsonSerializeInt",
       "jsonDeserializeTensorCArrayInt jsonDeserializeInt"),
    (tytensor_ tyfloat_,
       "jsonSerializeTensor jsonSerializeFloat",
       "jsonDeserializeTensorCArrayFloat jsonDeserializeFloat"),
    (tytensor_ tybool_,
       "jsonSerializeTensor jsonSerializeBool",
       "jsonDeserializeTensorDense jsonDeserializeBool")
  ]
with true in

-- Records
utest test false
  [tyrecord_ [("a",tyint_), ("b",tyfloat_), ("c",tyseq_ tybool_)]]
  "()"
  []
  [
    (tyrecord_ [("a",tyint_), ("b",tyfloat_), ("c",tyseq_ tybool_)],
       "
         lam r.
           JsonObject
             (mapInsert \"c\"
                (jsonSerializeSeq jsonSerializeBool r.c)
                (mapInsert \"b\"
                   (jsonSerializeFloat r.b)
                   (mapInsert \"a\"
                      (jsonSerializeInt r.a)
                      (mapEmpty cmpString))))
       ",
       "
         lam jr.
           match jr with JsonObject m then
             match mapLookup \"c\" m with Some jrv then
               match jsonDeserializeSeq jsonDeserializeBool jrv with Some rv then
                 match mapLookup \"b\" m with Some jrv1 then
                   match jsonDeserializeFloat jrv1 with Some rv1 then
                     match mapLookup \"a\" m with Some jrv2 then
                       match jsonDeserializeInt jrv2 with Some rv2 then
                         Some { a = rv2, b = rv1, c = rv }
                       else None {}
                     else None {}
                   else None {}
                 else None {}
               else None {}
             else None {}
           else None {}
       ")
  ]
with true in

-- Type constructors
utest test false
  [tycon_ "Seq", tycon_ "Integer"]
  "
    type Seq a = [a] in
    type Integer = Int in
    ()
  "
  [("Seq", "serializeSeq", "lam sf. jsonSerializeSeq sf",
           "deserializeSeq", "lam df. jsonDeserializeSeq df"),
   ("Integer", "serializeInteger", "jsonSerializeInt",
               "deserializeInteger", "jsonDeserializeInt")]
  [(tycon_ "Seq", "lam sf. jsonSerializeSeq sf", "lam df. jsonDeserializeSeq df"),
   (tycon_ "Integer", "jsonSerializeInt", "jsonDeserializeInt")]
with true in

-- Variants and type applications
utest test false
  [tycon_ "Either", tycon_ "MyType"]
  "
    type Either a b in
    con Left: all a. all b. a -> Either a b in
    con Right: all a. all b. b -> Either a b in
    type MyType = Either Int Bool in
    ()
  "
  [("Either",
    "serializeEither","
      lam sf. lam sf1. lam c.
        match c with Left d then
          JsonObject
            (mapInsert \"__constructor__\" (JsonString \"Left\")
               (mapInsert \"__data__\" (sf d) (mapEmpty cmpString)))
        else match c with Right d1 in
          JsonObject
              (mapInsert \"__constructor__\" (JsonString \"Right\")
                 (mapInsert \"__data__\" (sf1 d1) (mapEmpty cmpString)))
    ",
    "deserializeEither","
      lam df. lam df1. lam jc.
        match jc with JsonObject m then
          match mapLookup \"__constructor__\" m with Some (JsonString con1) then
            match con1 with \"Left\" then
              match mapLookup \"__data__\" m with Some data then
                match df data with Some d1 then Some (Left d1) else None {}
              else None {}
            else match con1 with \"Right\" then
              match mapLookup \"__data__\" m with Some data then
                match df1 data with Some d2 then Some (Right d2) else None {}
              else None {}
            else None {}
          else None {}
        else None {}
    "),
    ("MyType", "serializeMyType", "serializeEither jsonSerializeInt jsonSerializeBool",
              "deserializeMyType", "deserializeEither jsonDeserializeInt jsonDeserializeBool")
  ]
  [(tycon_ "Either", "serializeEither", "deserializeEither"),
   (tycon_ "MyType", "serializeEither jsonSerializeInt jsonSerializeBool",
                     "deserializeEither jsonDeserializeInt jsonDeserializeBool")]
with true in

-- Recursive types
utest test false
  [tycon_ "List"]
  "
    type List a in
    con Node: all a. List a -> List a in
    con Leaf: all a. () -> List a in
    ()
  "
  [("List", "serializeList", "
      lam sf. lam c.
        match c with Node d then
          JsonObject
            (mapInsert \"__constructor__\" (JsonString \"Node\")
              (mapInsert \"__data__\" (serializeList sf d)
                 (mapEmpty cmpString)))
          else match c with Leaf d1 in
            JsonObject
              (mapInsert \"__constructor__\" (JsonString \"Leaf\")
                (mapInsert \"__data__\" ((lam r.  JsonObject (mapEmpty cmpString)) d1)
                  (mapEmpty cmpString)))
    ",
    "deserializeList", "
      lam df. lam jc.
          match jc with JsonObject m then
            match mapLookup \"__constructor__\" m with Some (JsonString con1) then
              match con1 with \"Node\" then
                match mapLookup \"__data__\" m with Some data then
                  match deserializeList df data with Some d1 then Some (Node d1) else None {}
                else None {}
              else match con1 with \"Leaf\" then
                match mapLookup \"__data__\" m with Some data then
                  match (lam jr. match jr with JsonObject m1 then Some {} else None {}) data
                  with Some d2 then Some (Leaf d2) else None {}
                else None {}
              else None {}
            else None {}
          else None {}
    ")]
  [(tycon_ "List", "serializeList", "deserializeList")]
with true in

utest test false
  [tycon_ "TestType"]
  "
    type TestType in
    con TestTypeCon: Tensor[Float] -> TestType in
    ()
  "
  [("TestType",
    "serializeTestType","
      lam c.
        match c with TestTypeCon d in
        JsonObject
            (mapInsert \"__constructor__\"
               (JsonString \"TestTypeCon\")
               (mapInsert
                  \"__data__\"
                  (jsonSerializeTensor jsonSerializeFloat d)
                  (mapEmpty cmpString)))
    ",
    "deserializeTestType","
      lam jc.
        match jc with JsonObject m then
          match mapLookup \"__constructor__\" m with Some (JsonString con1) then
            match con1 with \"TestTypeCon\" then
              match mapLookup \"__data__\" m with Some data then
                match
                  jsonDeserializeTensorCArrayFloat
                    jsonDeserializeFloat
                    data
                with Some d then
                  Some (TestTypeCon d)
                else None {}
              else None {}
            else None {}
          else None {}
        else None {}
    ")
  ]
  [(tycon_ "TestType", "serializeTestType", "deserializeTestType")]
with true in

-- let res = addJsonSerializers
--   [tycon_ "List", tycon_ "Seq"]
--   (parseTest "
--   type List a in
--   con Node: all a. { element: a, rest: List a } -> List a in
--   con Leaf: all a. {} -> List a in
--   type Seq a = List a in
--   ()
--   ") in
-- let res2 = mexprToString res.1 in
-- printLn res2;

()

