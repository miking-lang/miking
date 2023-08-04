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
include "stringid.mc"
include "map.mc"

lang GenerateJsonSerializers =
  MExprAst + BootParser + MExprSym + MExprCmp + MExprFindSym + GetConDefType

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
    sTensor: Name, dTensor: Name,
    jsonObject: Name,
    mapInsert: Name, mapEmpty: Name, mapLookup: Name,
    cmpString: Name,
    some: Name, none: Name

  }

  sem generateJsonSerializers: [Type] -> Expr -> (GJSAcc, GJSRes)
  sem generateJsonSerializers tys =
  | expr ->
    let lib = _lib () in
    match findNamesOfStringsExn [
        "jsonSerializeBool", "jsonDeserializeBool", "jsonSerializeInt",
        "jsonDeserializeInt", "jsonSerializeFloat", "jsonDeserializeFloat",
        "jsonSerializeChar", "jsonDeserializeChar", "jsonSerializeString",
        "jsonDeserializeString", "jsonSerializeSeq", "jsonDeserializeSeq",
        "jsonSerializeTensor", "jsonDeserializeTensor",
        "JsonObject",
        "mapInsert", "mapEmpty", "mapLookup",
        "cmpString",
        "Some", "None"
      ] lib with [
        sb, db, si, di, sf, df, sc, dc,
        ss, ds, ssq, dsq, st, dt,
        jo,
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
      sTensor = st, dTensor = dt,
      jsonObject = jo,
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
    -- let funs = join (map (lam t. [t.0,t.1]) (mapValues acc)) in
    -- let funs = if null funs then unit_ else bindall_ funs in
    -- let additions = bind_ env.lib funs in
    -- let expr = bindWithEnd_ expr additions in
    -- let acc = mapMap (lam v.
    --     match v with (TmLet t1, TmLet t2) then (t1.ident,t2.ident)
    --     else error "Impossible"
    --   ) acc in
    (r.0, r.1)

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
    let s = { serializer = nvar_ env.sSeq, deserializer = nvar_ env.dSeq } in
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
    let deserializer = appf1_ (nvar_ env.dTensor) si.deserializer in
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
    let inner = urecord_ (map (lam t. (sidToString t.0, (nvar_ (t.1).1))) (mapToSeq iss)) in
    let none = nconapp_ env.none unit_ in
    let deserializer =
      nulam_ darg (
          match_
            (nvar_ darg)
            (npcon_ env.jsonObject (npvar_ m))
            (mapFoldWithKey  (lam acc. lam k. lam v.
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
            error "TODO"
            -- SERIALIZER
            -- lam p1. lam p2. lam v.
            --   match v with Con1 d1 then
            --     JsonObject m{ "__constructor__": "Con1", "__data__": srlsfun1 d1 }
            --   else match v with Con2 d2 then
            --     JsonObject m{ "__constructor__": "Con2", "__data__": srlsfun2 d2 }
            --   else match v with Con3 d3 then
            --     JsonObject m{ "__constructor__": "Con3", "__data__": srlsfun3 d3 }
            --   else never
            --
            --
            -- DESERIALIZER
          else error (join ["Empty variant type: ", nameGetStr t.ident])

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

  -- | TyApp _ ->
    -- TODO
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

let parseTest = parseMExprString {
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
  match generateJsonSerializers tys expr with (acc,res) in
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
  [tyseq_ tyint_, tytensor_ tyint_]
  "()"
  []
  [
    (tyseq_ tyint_,
       "jsonSerializeSeq jsonSerializeInt",
       "jsonDeserializeSeq jsonDeserializeInt"),
    (tytensor_ tyint_,
       "jsonSerializeTensor jsonSerializeInt",
       "jsonDeserializeTensor jsonDeserializeInt")
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
                         { a = rv2, b = rv1, c = rv }
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
utest test true
  [tycon_ "Seq", tycon_ "Integer"]
  "
    type Seq a = [a] in
    type Integer = Int in
    ()
  "
  []
  [
    -- (ty,
    --    "
    --      def
    --    ",
    --    "
    --      def
    --    ")
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

