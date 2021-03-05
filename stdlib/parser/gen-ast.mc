include "mexpr/eq.mc"

type SynType = String
let stringToSynType = identity
let _eqSynType = eqString
let _cmpSynType = cmpString
let _synTypeToString = identity

type CarriedType =
  { repr : Type
  , smapAccumL
    : (Expr -> Expr -> Expr) -- Staged function to apply
    -> Type -- Target type
    -> Option (Name -> Name -> Expr) -- acc name -> val name -> result expression
  }

type Constructor =
  { name : Name
  , synType : SynType
  , carried : CarriedType
  }

type SemanticFunction =
  { name : String
  , preCaseArgs : [(Name, Type)]
  , cases : [(Pat, Expr)]
  }

type LanguageFragment =
  { name : String
  , extends : [String]
  , synTypes : Map SynType [Constructor]
  , semanticFunctions : [SemanticFunction]
  }

type GenInput =
  { namePrefix : String
  , constructors : [Constructor]
  , requestedSFunctions : [(SynType, Type)]
  }

lang CarriedTypeBase
  syn CarriedType =

  sem carriedRepr /- : CarriedType -> Type -/ =
  sem carriedSMapAccumL (f : Expr -> Expr -> Expr) (targetTy : Type) /- : CarriedType -> Option (Name -> Name -> Expr) -/ =
end

let _equalTypes = use MExprEq in eqType assocEmpty
let _typeToString = use MExprPrettyPrint in lam ty. (getTypeStringCode 0 pprintEnvEmpty ty).1
let _nulet_ = lam n. lam body. lam inexpr. use LetAst in TmLet
  { ident = n
  , body = body
  , tyBody = tyunknown_
  , inexpr = inexpr
  , info = NoInfo ()
  , ty = tyunknown_
  }

let _pprintSemanticFunction
  : SemanticFunction
  -> String
  = lam func. use MExprPrettyPrint in
    match func with {name = name, preCaseArgs = preCaseArgs, cases = cases} then
      let pprintArg = lam env. lam arg.
        match arg with (name, ty) then
          match pprintVarName env name with (env, str) then
            match getTypeStringCode 2 env ty with (env, ty) then
              (env, join [" (", str, " : ", ty, ")"])
            else never
          else never
        else never in
      let pprintCase = lam env. lam case.
        match case with (pat, expr) then
          match getPatStringCode 4 env pat with (env, pat) then
            match pprintCode 4 env expr with (env, expr) then
              (env, join ["  | ", pat, " ->\n    ", expr, "\n"])
            else never
          else never
        else never in
      let env = pprintEnvEmpty in
      match mapAccumL pprintArg env preCaseArgs with (env, args) then
        match mapAccumL pprintCase env cases with (env, cases) then
          join
            [ "  sem ", name
            , join args
            , " =\n"
            , join cases
            ]
        else never
      else never
    else never

lang CarriedTypeHelpers = CarriedTypeBase
  sem _pprintLanguageFragment =
  | {name = name, extends = extends, synTypes = synTypes, semanticFunctions = semanticFunctions} ->
    let extends = match extends
      with [] then ""
      else concat " = " (strJoin " + " extends) in
    let pprintConstructor = lam constructor.
      match constructor with {name = name, carried = carried} then
        join ["\n  | ", nameGetStr name, " ", _typeToString (carriedRepr carried)]
      else never in
    let synDefns = map
      (lam binding.
        match binding with (synType, constructors) then
          join
            [ "  syn ", _synTypeToString synType, " ="
            , join (map pprintConstructor constructors)
            , "\n"
            ]
        else never)
      (mapBindings synTypes) in
    join
      [ "lang ", name, extends , "\n"
      , join synDefns
      , "\n"
      , strJoin "\n" (map _pprintSemanticFunction semanticFunctions)
      , "\nend"
      ]

  sem _mkSmapAccumL (synType : SynType) (targetTy : Type) =
  | constructor ->
    if _eqSynType synType constructor.synType then
      let fName = nameSym "f" in
      match carriedSMapAccumL (appf2_ (nvar_ fName)) targetTy constructor.carried with Some mkNew then
        let accName = nameSym "acc" in
        let valName = nameSym "x" in
        Some
          { name = join ["smapAccumL_", _synTypeToString synType, "_", _typeToString targetTy]
          , preCaseArgs =
            [ (fName, tyarrows_ [tyvar_ "a", targetTy, tytuple_ [tyvar_ "a", targetTy]])
            , (accName, tyvar_ "a")
            ]
          , cases =
            [ ( npcon_ constructor.name (npvar_ valName)
              , match_
                (mkNew accName valName)
                (ptuple_ [npvar_ accName, npvar_ valName])
                (tuple_ [nvar_ accName, nconapp_ constructor.name (nvar_ valName)])
                never_
              )
            ]
          }
      else None ()
    else None ()
end

let _mkSFuncStubs
  : SynType
  -> Type
  -> [SemanticFunction]
  = lam synType. lam targetTy.
    let suffix = join ["_", _synTypeToString synType, "_", _typeToString targetTy] in
    let fName = nameSym "f" in
    let accName = nameSym "acc" in
    let valName = nameSym "x" in
    let smapAccumL_ = appf3_ (var_ (concat "smapAccumL" suffix)) in
    let smapAccumL =
      { name = concat "smapAccumL" suffix
      , preCaseArgs =
        [ (fName, tyarrows_ [tyvar_ "a", targetTy, tytuple_ [tyvar_ "a", targetTy]])
        , (accName, tyvar_ "a")
        ]
      , cases =
        [ (npvar_ valName, tuple_ [nvar_ accName, nvar_ valName])
        ]
      } in
    let smap =
      { name = concat "smap" suffix
      , preCaseArgs =
        [ (fName, tyarrow_ targetTy targetTy)
        ]
      , cases =
        [ ( npvar_ valName
          , tupleproj_ 1
            (smapAccumL_
              (ulam_ "" (nulam_ valName (tuple_ [unit_, appf1_ (nvar_ fName) (nvar_ valName)])))
              unit_
              (nvar_ valName))
          )
        ]
      } in
    let sfold =
      { name = concat "sfold" suffix
      , preCaseArgs =
        [ (fName, tyarrows_ [tyvar_ "a", targetTy, tyvar_ "a"])
        , (accName, tyvar_ "a")
        ]
      , cases =
        [ ( npvar_ valName
          , tupleproj_ 0
            (smapAccumL_
              (nulam_ accName (nulam_ valName (tuple_ [appf2_ (nvar_ fName) (nvar_ accName) (nvar_ valName), nvar_ valName])))
              (nvar_ accName)
              (nvar_ valName))
          )
        ]
      } in
    [smapAccumL, smap, sfold]

lang CarriedTarget = CarriedTypeBase
  syn CarriedType =
  | TargetType {targetable : Bool, ty : Type}

  sem carriedRepr =
  | TargetType {ty = ty} -> ty

  sem carriedSMapAccumL (f : Expr -> Expr -> Expr) (targetTy : Type) =
  | TargetType {targetable = false} -> None ()
  | TargetType {targetable = true, ty = ty} ->
    if _equalTypes ty targetTy
    then Some (lam accName. lam valName. f (nvar_ accName) (nvar_ valName))
    else None ()
end

lang CarriedSeq = CarriedTypeBase
  syn CarriedType =
  | SeqType CarriedType

  sem carriedRepr =
  | SeqType ty -> tyseq_ (carriedRepr ty)

  sem carriedSMapAccumL (f : Expr -> Expr -> Expr) (targetTy : Type) =
  | SeqType ty ->
    match carriedSMapAccumL f targetTy ty with Some mkNew then Some
      (lam accName. lam valName.
        let innerAcc = nameSym "acc" in
        let innerVal = nameSym "x" in
        appf3_
          (var_ "mapAccumL")
          (nulam_ innerAcc
            (nulam_ innerVal
              (mkNew innerAcc innerVal)))
          (nvar_ accName)
          (nvar_ valName)
      )
    else None ()
end

lang CarriedRecord = CarriedTypeBase
  syn CarriedType =
  | RecordType [(String, CarriedType)]

  sem carriedRepr =
  | RecordType tys -> tyrecord_
    (map
      (lam x. {x with #label"1" = carriedRepr x.1})
      tys)

  sem carriedSMapAccumL (f : Expr -> Expr -> Expr) (targetTy : Type) =
  | RecordType fields ->
    let mappingFields = mapOption
      (lam x. optionMap (lam y. (x.0, y)) (carriedSMapAccumL f targetTy x.1))
      fields in
    match mappingFields with [] then None ()
    else Some
      (lam accName. lam valName.
        -- NOTE(vipa, 2021-03-03): This constructs an AST with
        -- shadowing of symbolized names, which may or may not be what
        -- we want
        let mappedFields = mapAccumR
          (lam constr. lam x. match x with (field, mkNew) then
             let fieldName = nameSym field in
             let constr = lam innerMost.
               match_
                 (_nulet_
                   fieldName
                   (recordproj_ field (nvar_ valName))
                   (mkNew accName fieldName))
                 (ptuple_ [npvar_ accName, npvar_ fieldName])
                 (constr innerMost)
                 never_
             in (constr, (field, fieldName))
           else never)
          identity
          mappingFields
        in match mappedFields with (constr, mappedFields) then
          constr
            (tuple_
              [ nvar_ accName
              , (foldl
                  (lam acc. lam update.
                    recordupdate_ acc update.0 (nvar_ update.1))
                  (nvar_ valName)
                  mappedFields)
              ])
        else never
      )
end

let targetableType
  : Type
  -> CarriedType
  = lam ty. use CarriedTarget in TargetType {targetable = true, ty = ty}

let untargetableType
  : Type
  -> CarriedType
  = lam ty. use CarriedTarget in TargetType {targetable = false, ty = ty}

let seqType
  : CarriedType
  -> CarriedType
  = lam ty. use CarriedSeq in SeqType ty

let recordType
  : [(String, CarriedType)]
  -> CarriedType
  = lam fields. use CarriedRecord in RecordType fields

let tupleType
  : [CarriedType]
  -> CarriedType
  = lam fields. recordType (mapi (lam i. lam field. (int2string i, field)) fields)

lang CarriedTypeGenerate = CarriedTypeHelpers
  sem mkLanguages = /- GenInput -> String -/
  | input ->
    match input with {namePrefix = namePrefix, constructors = constructors, requestedSFunctions = requestedSFunctions} then
      let synTypes = foldl
        (lam acc. lam c. mapInsert c.synType [] acc)
        (mapEmpty _cmpSynType)
        constructors in
      let baseLangName = concat namePrefix "Base" in
      let baseLang =
        { name = baseLangName
        , extends = []
        , synTypes = synTypes
        , semanticFunctions = join
          (map (lam request. _mkSFuncStubs request.0 request.1) requestedSFunctions)
        } in
      let mkConstructorLang = lam constructor.
        match constructor with {name = name, synType = synType, carried = carried} then
          { name = concat namePrefix (nameGetStr name)
          , extends = [baseLangName]
          , synTypes = mapInsert synType [constructor] (mapEmpty _cmpSynType)
          , semanticFunctions = mapOption
            (lam request. _mkSmapAccumL request.0 request.1 constructor)
            requestedSFunctions
          }
        else never in
      let constructorLangs = map mkConstructorLang constructors in
      strJoin "\n\n" (map _pprintLanguageFragment (cons baseLang constructorLangs))
    else never
end

lang CarriedBasic = CarriedTypeGenerate + CarriedTarget + CarriedSeq + CarriedRecord

mexpr

use CarriedBasic in

let tyInfo = targetableType (tyvar_ "Info") in
let tyName = targetableType (tyvar_ "Name") in
let tyString = targetableType tystr_ in
let tyExpr = targetableType (tyvar_ "Expr") in
let tyType = targetableType (tyvar_ "Type") in
let tyField = tupleType [tyString, tyExpr] in
let tyFields = seqType tyField in
let tyRecord = recordType
  [ ("info", tyInfo)
  , ("ty", tyType)
  , ("fields", tyFields)
  ] in

let recordConstructor =
  { name = nameSym "TmRecord"
  , synType = stringToSynType "Expr"
  , carried = tyRecord
  } in

let varConstructor =
  { name = nameSym "TmVar"
  , synType = stringToSynType "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("ident", tyName)
    ]
  } in

let seqConstructor =
  { name = nameSym "TmSeq"
  , synType = stringToSynType "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("tms", seqType tyExpr)
    ]
  } in

let input =
  { namePrefix = "MExpr"
  , constructors = [recordConstructor, varConstructor, seqConstructor]
  , requestedSFunctions =
    [ (stringToSynType "Expr", tyvar_ "Info")
    , (stringToSynType "Expr", tyvar_ "Expr")
    , (stringToSynType "Expr", tyvar_ "Type")
    ]
  } in

-- printLn (mkLanguages input);

-- TODO(vipa, 2021-03-05): The tests here need to parse and evaluate
-- MLang, so I'm holding off on doing it in an automated fashion until
-- `boot-parser.mc` handles that

()
