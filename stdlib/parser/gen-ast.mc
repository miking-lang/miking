include "mexpr/eq.mc"
include "common.mc"


/-

This library assists in automatically generating MLang fragments for
arbitrary AST nodes, while also generating shallow mapping functions
(see the [recursion
cookbook](https://github.com/miking-lang/miking/wiki/Recursion-Cookbook)).

Input is a list of constructors and a list of shallow mappings to
generate. Each constructor gets a name, a syn type, and a carried
type. The carried type, represented by `CarriedType`, is the type of
the value the constructor is applied to. A `CarriedType` knows what
type it is representing (in the form of a `Type` value) and how to
build `smapAccumL` given a targeted type. It's built using a few
helper functions: `targetableType`, `untargetableType`, `seqType`,
`recordType`, and `tupleType`. `targetableType` and `untargetableType`
are intended to be atomic from the generator's point of view, the
former can be targeted by a shallow mapping while the latter
cannot. The others represent composite types that know how to traverse
themselves.

`untargetableType` is intended to be used for things that the AST node
doesn't "contain", but are rather information about it, e.g., info
fields and type annotations, as opposed to sub-expressions or the type
of the lambda parameter.

-- NOTE(vipa, 2021-03-05): It is my hypothesis that we don't want a
`smap_Expr_Type` to map over the `ty` field, hence this library
supports untargetable types, but it remains to be seen if this is the
case. Default to `targetableType`, use `untargetableType` if you have
a good reason to suspect that most traversals won't want to include
the given field.

For example, we can declare something like `TmRecord` like this:

```
let recordConstructor =
  { name = nameSym "TmRecord"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", targetableType (tycon_ "Info"))
    , ("ty", untargetableType (tycon_ "Type"))
    , ( "bindings"
      , seqType
        (tupleType
          [ targetableType tystr_
          , targetableType (tycon_ "Expr")])
      )
    ]
  }
```

We can then generate some language fragments:

```
use CarriedBasic in mkLanguages
  { namePrefix = "MExpr"
  , constructors = [recordConstructor]
  , requestedSFunctions =
    [ (nameNoSym "Expr", tycon_ "Expr")
    ]
  , composedName = Some "Composed"
  }

-- This is what's generated:

lang MExprBase
  syn Expr =

  sem smapAccumL_Expr_Expr (f : (a) -> ((Expr) -> ((a, Expr)))) (acc : a) =
  | x ->
    (acc, x)

  sem smap_Expr_Expr (f : (Expr) -> (Expr)) =
  | x ->
    (smapAccumL_Expr_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Expr (f : (a) -> ((Expr) -> (a))) (acc : a) =
  | x ->
    (smapAccumL_Expr_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

end

lang MExprTmRecord = MExprBase
  syn Expr =
  | TmRecord {info: Info, ty: Type, bindings: [([Char], Expr)]}

  sem smapAccumL_Expr_Expr (f : (a) -> ((Expr) -> ((a, Expr)))) (acc : a) =
  | TmRecord x ->
    match
      match
        let bindings =
          x.bindings
        in
        mapAccumL
          (lam acc1.
             lam x1.
               match
                 let #var"1" =
                   x1.#label"1"
                 in
                 f
                   acc1
                   #var"1"
               with
                 (acc1, #var"1")
               then
                 (acc1, { x1
                   with
                   #label"1" =
                     #var"1" })
               else
                 never)
          acc
          bindings
      with
        (acc, bindings)
      then
        (acc, { x
          with
          bindings =
            bindings })
      else
        never
    with
      (acc, x)
    then
      (acc, TmRecord
        x)
    else
      never

end

lang Composed = MExprTmRecord


end
```

-- NOTE(vipa, 2021-03-05): Since we do not yet self-host MLang this
file uses local and temporary definitions of language fragments. These
are not intended to be public, and should be replaced once we do
bootstrap MLang.

-/

type Constructor =
  { name : Name
  , synType : Name
  , carried : CarriedType
  }

type SemanticFunction =
  { name : String
  , ty : Option Type
  , preCaseArgs : [(Name, Option Type)]
  , cases : [(Pat, Expr)]
  }

type LanguageFragment =
  { name : String
  , extends : [String]
  , aliases : [(Name, Type)]
  , synTypes : Map Name ([Name], [Constructor])
  , semanticFunctions : [SemanticFunction]
  }

type GenInput =
  { baseName : String
  , composedName : Option String
  , fragmentName : Name -> String
  , constructors : [Constructor]
  , requestedSFunctions : [(Name, Type)]
  , fieldAccessors : [(Name, String, Type)]
  }

lang CarriedTypeBase
  syn CarriedType =

  sem carriedRepr /- : CarriedType -> Type -/ =
  sem carriedSMapAccumL (f : Expr -> Expr -> Expr) (targetTy : Type) /- : CarriedType -> Option (Name -> Name -> Expr) -/ =
end

let _equalTypes = use MExprEq in eqType
let _typeToString = use MExprPrettyPrint in lam ty. (getTypeStringCode 0 pprintEnvEmpty ty).1
let _nulet_ = lam n. lam body. lam inexpr. use LetAst in TmLet
  { ident = n
  , body = body
  , tyAnnot = tyunknown_
  , tyBody = tyunknown_
  , inexpr = inexpr
  , info = NoInfo ()
  , ty = tyunknown_
  }

let _pprintSemanticFunction
  : SemanticFunction
  -> String
  = lam func. use MExprPrettyPrint in
    match func with {name = name, preCaseArgs = preCaseArgs, cases = cases, ty = ty} then
      let pprintArg = lam env. lam arg.
        match arg with (name, ty) then
          match pprintVarName env name with (env, str) then
            match ty with Some ty then
              match getTypeStringCode 2 env ty with (env, ty) in
              (env, join [" (", str, " : ", ty, ")"])
            else (env, cons ' ' str)
          else never
        else never in
      let pprintCase = lam env. lam aCase.
        match aCase with (pat, expr) then
          match getPatStringCode 4 env pat with (env, pat) then
            match pprintCode 4 env expr with (env, expr) then
              (env, join ["  | ", pat, " ->\n    ", expr, "\n"])
            else never
          else never
        else never in
      let env = pprintEnvEmpty in
      let temp =
        match ty with Some ty then
          match getTypeStringCode 2 env ty with (env, ty) in
          (env, join ["  sem ", name, " : ", ty, "\n"])
        else (env, "") in
      match temp with (env, sig) in
      let temp =
        match cases with ![] then
          match mapAccumL pprintArg env preCaseArgs with (env, args) in
          match mapAccumL pprintCase env cases with (env, cases) in
          let str = join
            [ "  sem ", name
            , join args
            , " =\n"
            , join cases
            ] in
          (env, str)
        else (env, "") in
      match temp with (env, impl) in
      -- NOTE(vipa, 2022-03-31): In an actual later implementation
      -- we'd presumably pass on the environment here as well, but for
      -- now we just return the string
      concat sig impl
    else never

lang CarriedTypeHelpers = CarriedTypeBase
  sem _pprintLanguageFragment =
  | x ->
    match let x: LanguageFragment = x in x with
      { name = name
      , extends = extends
      , aliases = aliases
      , synTypes = synTypes
      , semanticFunctions = semanticFunctions
      }
    then
      let extends = match extends
        with [] then ""
        else concat " = " (strJoin " + " extends) in
      let pprintConstructor = lam constructor: Constructor.
        match constructor with {name = name, carried = carried} then
          join ["\n  | ", nameGetStr name, " ", _typeToString (carriedRepr carried)]
        else never in
      let aliases = map
        (lam binding. match binding with (name, ty) in
          join [ "  type ", nameGetStr name, " = ", _typeToString ty, "\n"])
        aliases in
      let synDefns = map
        (lam binding.
          match binding with (synType, (params, constructors)) then
            join
              [ "  syn ", nameGetStr synType, join (map (lam x. cons ' ' (nameGetStr x)) params), " ="
              , join (map pprintConstructor constructors)
              , "\n"
              ]
          else never)
        (mapBindings synTypes) in
      join
        [ "lang ", name, extends , "\n"
        , join aliases
        , "\n"
        , join synDefns
        , "\n"
        , strJoin "\n" (map _pprintSemanticFunction semanticFunctions)
        , "\nend"
        ]
    else never

  sem _mkSmapAccumL (synType : Name) (targetTy : Type) =
  | constructor ->
    let constructor: Constructor = constructor in
    if nameEq synType constructor.synType then
      let fName = nameSym "f" in
      match carriedSMapAccumL (appf2_ (nvar_ fName)) targetTy constructor.carried with Some mkNew then
        let accName = nameSym "acc" in
        let valName = nameSym "x" in
        Some
          { name = join ["smapAccumL_", nameGetStr synType, "_", _typeToString targetTy]
          , ty = None ()
          , preCaseArgs =
            [ (fName, None ())
            , (accName, None ())
            ]
          , cases =
            [ ( npcon_ constructor.name (npvar_ valName)
              , match_
                (mkNew accName valName)
                (ptuple_ [npvar_ accName, npvar_ valName])
                (utuple_ [nvar_ accName, nconapp_ constructor.name (nvar_ valName)])
                never_
              )
            ]
          }
      else None ()
    else None ()

  sem _mkAccess : Name -> String -> Constructor -> [SemanticFunction]
  sem _mkAccess synType field =
  | constructor ->
    if nameEq constructor.synType synType then
      let targetName = nameSym "target" in
      let valName = nameSym "val" in
      let getf =
        { name = join ["get_", nameGetStr synType, "_", field]
        , ty = None ()
        , preCaseArgs = []
        , cases =
          [ ( npcon_ constructor.name (npvar_ targetName)
            , recordproj_ field (nvar_ targetName)
            )
          ]
        } in
      let setf =
        { name = join ["set_", nameGetStr synType, "_", field]
        , ty = None ()
        , preCaseArgs = [(valName, None ())]
        , cases =
          [ ( npcon_ constructor.name (npvar_ targetName)
            , nconapp_ constructor.name (recordupdate_ (nvar_ targetName) field (nvar_ valName))
            )
          ]
        } in
      [getf, setf]
    else []
end

let _mkSFuncStubs
  : Name
  -> Type
  -> [SemanticFunction]
  = lam synType. lam targetTy.
    let synTy = ntycon_ synType in
    let suffix = join ["_", nameGetStr synType, "_", _typeToString targetTy] in
    let fName = nameSym "f" in
    let accName = nameSym "acc" in
    let valName = nameSym "x" in
    let smapAccumL_ = appf3_ (var_ (concat "smapAccumL" suffix)) in
    let smapAccumL =
      { name = concat "smapAccumL" suffix
      , ty = Some (tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", targetTy, tytuple_ [tyvar_ "a", targetTy]]
        , tyvar_ "a"
        , synTy
        , tytuple_ [tyvar_ "a", synTy]
        ]))
      , preCaseArgs =
        [ (fName, None ())
        , (accName, None ())
        ]
      , cases =
        [ (npvar_ valName, utuple_ [nvar_ accName, nvar_ valName])
        ]
      } in
    let smap =
      { name = concat "smap" suffix
      , ty = Some (tyarrows_
        [ tyarrow_ targetTy targetTy
        , synTy
        , synTy
        ])
      , preCaseArgs =
        [ (fName, None ())
        ]
      , cases =
        [ ( npvar_ valName
          , tupleproj_ 1
            (smapAccumL_
              (ulam_ "" (nulam_ valName (utuple_ [uunit_, appf1_ (nvar_ fName) (nvar_ valName)])))
              uunit_
              (nvar_ valName))
          )
        ]
      } in
    let sfold =
      { name = concat "sfold" suffix
      , ty = Some (tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", targetTy, tyvar_ "a"]
        , tyvar_ "a"
        , synTy
        , tyvar_ "a"
        ]))
      , preCaseArgs =
        [ (fName, None ())
        , (accName, None ())
        ]
      , cases =
        [ ( npvar_ valName
          , tupleproj_ 0
            (smapAccumL_
              (nulam_ accName (nulam_ valName (utuple_ [appf2_ (nvar_ fName) (nvar_ accName) (nvar_ valName), nvar_ valName])))
              (nvar_ accName)
              (nvar_ valName))
          )
        ]
      } in
    [smapAccumL, smap, sfold]

let _mkFieldStubs
  : Name
  -> String
  -> Type
  -> [SemanticFunction]
  = lam synType. lam field. lam ty.
    let synTy = ntycon_ synType in
    let suffix = join ["_", nameGetStr synType, "_", field] in
    let fName = nameSym "f" in
    let accName = nameSym "acc" in
    let valName = nameSym "val" in
    let targetName = nameSym "target" in
    let getf =
      { name = concat "get" suffix
      , ty = Some (tyarrow_ synTy ty)
      , preCaseArgs = []
      , cases = []
      } in
    let getf_ = appf1_ (var_ (concat "get" suffix)) in
    let setf =
      { name = concat "set" suffix
      , ty = Some (tyarrows_ [ty, synTy, synTy])
      , preCaseArgs = [(valName, None ())]
      , cases = []
      } in
    let setf_ = appf2_ (var_ (concat "set" suffix)) in
    let mapAccumf =
      { name = concat "mapAccum" suffix
      , ty = Some (tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", ty, tytuple_ [tyvar_ "a", ty]]
        , tyvar_ "a"
        , synTy
        , tytuple_ [tyvar_ "a", synTy]
        ]))
      , preCaseArgs = [(fName, None ()), (accName, None ())]
      , cases =
        [ ( npvar_ targetName
          , match_
            (appf2_ (nvar_ fName) (nvar_ accName) (getf_ (nvar_ targetName)))
            (ptuple_ [npvar_ accName, npvar_ valName])
            (utuple_ [nvar_ accName, setf_ (nvar_ valName) (nvar_ targetName)])
            never_
          )
        ]
      } in
    let mapf =
      { name = concat "map" suffix
      , ty = Some (tyarrows_
        [ tyarrow_ ty ty
        , synTy
        , synTy
        ])
      , preCaseArgs = [(fName, None ())]
      , cases =
        [ ( npvar_ targetName
          , setf_ (appf1_ (nvar_ fName) (getf_ (nvar_ targetName))) (nvar_ targetName)
          )
        ]
      } in
    [getf, setf, mapAccumf, mapf]

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
            (nlam_ innerVal (carriedRepr ty)
              (mkNew innerAcc innerVal)))
          (nvar_ accName)
          (nvar_ valName)
      )
    else None ()
end

lang CarriedOption = CarriedTypeBase
  syn CarriedType =
  | OptionType CarriedType

  sem carriedRepr =
  | OptionType ty -> tyapp_ (tycon_ "Option") (carriedRepr ty)

  sem carriedSMapAccumL f targetTy =
  | OptionType ty ->
    match carriedSMapAccumL f targetTy ty with Some mkNew then Some
      (lam accName. lam valName.
        let innerAcc = nameSym "acc" in
        let innerVal = nameSym "x" in
        appf3_
          (var_ "optionMapAccum")
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
      (lam x. (x.0, carriedRepr x.1))
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
            (utuple_
              [ nvar_ accName
              , (foldl
                  (lam acc. lam update: (Unknown, Unknown).
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

let optionType
  : CarriedType
  -> CarriedType
  = lam ty. use CarriedOption in OptionType ty

let recordType
  : [(String, CarriedType)]
  -> CarriedType
  = lam fields. use CarriedRecord in RecordType fields

let tupleType
  : [CarriedType]
  -> CarriedType
  = lam fields. recordType (mapi (lam i. lam field. (int2string i, field)) fields)

lang CarriedTypeGenerate = CarriedTypeHelpers
  sem mkLanguages : GenInput -> String
  sem mkLanguages =
  | input ->
    let synTypes = foldl
      (lam acc. lam c: Constructor. mapInsert c.synType ([], []) acc)
      (mapEmpty nameCmp)
      input.constructors in
    let baseLang =
      let sfunctions = join
        (map (lam request: (Unknown, Unknown). _mkSFuncStubs request.0 request.1) input.requestedSFunctions) in
      let accessors = join
        (map (lam x. match x with (synty, field, ty) in _mkFieldStubs synty field ty) input.fieldAccessors) in
      { name = input.baseName
      , extends = []
      , aliases = []
      , synTypes = synTypes
      , semanticFunctions = concat sfunctions accessors
      } in
    let mkConstructorLang = lam constructor: Constructor.
      match constructor with {name = name, synType = synType, carried = carried} then
        let recordTyName = nameNoSym (concat (nameGetStr name) "Record") in
        let sfunctions = mapOption
          (lam request: (Unknown, Unknown). _mkSmapAccumL request.0 request.1 constructor)
          input.requestedSFunctions in
        let accessors = map
          (lam request. match request with (name, field, _) in _mkAccess name field constructor)
          input.fieldAccessors in
        { name = input.fragmentName name
        , extends = [input.baseName]
        , aliases = [(recordTyName, carriedRepr carried)]
        , synTypes = mapInsert synType ([], [{constructor with carried = untargetableType (ntycon_ recordTyName)}]) (mapEmpty nameCmp)
        , semanticFunctions = concat sfunctions (join accessors)
        }
      else never in
    let constructorLangs = map mkConstructorLang input.constructors in
    let constructorLangs =
      match input.composedName with Some name then
        snoc
          constructorLangs
          { name = name
          , extends = map (lam x: LanguageFragment. x.name) constructorLangs
          , aliases = []
          , synTypes = mapEmpty nameCmp
          , semanticFunctions = []
          }
      else constructorLangs in
    strJoin "\n\n" (map _pprintLanguageFragment (cons baseLang constructorLangs))
end

lang CarriedBasic = CarriedTypeGenerate + CarriedTarget + CarriedSeq + CarriedRecord + CarriedOption
end

mexpr

use CarriedBasic in

let tyInfo = targetableType (tycon_ "Info") in
let tyName = targetableType (tycon_ "Name") in
let tyString = targetableType tystr_ in
let tyExpr = targetableType (tycon_ "Expr") in
let tyType = targetableType (tycon_ "Type") in
let tyField = tupleType [tyString, tyExpr] in
let tyFields = seqType tyField in
let tyRecord = recordType
  [ ("info", tyInfo)
  , ("ty", tyType)
  , ("fields", tyFields)
  ] in

let recordConstructor =
  { name = nameSym "TmRecord"
  , synType = nameNoSym "Expr"
  , carried = tyRecord
  } in

let varConstructor =
  { name = nameSym "TmVar"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("ident", tyName)
    ]
  } in

let seqConstructor =
  { name = nameSym "TmSeq"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("tms", seqType tyExpr)
    ]
  } in

let input =
  { baseName = "MExprBase"
  , fragmentName = lam s. concat (nameGetStr s) "Ast"
  , constructors = [recordConstructor, varConstructor, seqConstructor]
  , requestedSFunctions =
    [ (nameNoSym "Expr", tycon_ "Info")
    , (nameNoSym "Expr", tycon_ "Expr")
    , (nameNoSym "Expr", tycon_ "Type")
    ]
  , composedName = Some "Composed"
  , fieldAccessors = []
  } in

let res = mkLanguages input in
-- printLn res;

let recordConstructor =
  { name = nameSym "TmRecord"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", untargetableType (tycon_ "Info"))
    , ("ty", untargetableType (tycon_ "Type"))
    , ( "bindings"
      , seqType
        (tupleType
          [ targetableType tystr_
          , targetableType (tycon_ "Expr")])
      )
    ]
  } in
let res = mkLanguages
  { baseName = "MExprBase"
  , fragmentName = lam s. concat (nameGetStr s) "Ast"
  , constructors = [recordConstructor]
  , requestedSFunctions =
    [ (nameNoSym "Expr", tycon_ "Expr")
    ]
  , composedName = Some "Composed"
  , fieldAccessors = []
  } in
-- printLn res;

-- TODO(vipa, 2021-03-05): The tests here need to parse and evaluate
-- MLang, so I'm holding off on doing it in an automated fashion until
-- `boot-parser.mc` handles that

()
