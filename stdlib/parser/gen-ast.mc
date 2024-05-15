include "mlang/ast.mc"
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

-- TODO(vipa, 2023-03-09): The previous note is mostly handled at this
point, but I'm leaving it in place since there are some open questions
on Info fields and similar things. Search for "NoInfo ()" or
"nameNoSym" for a large number of places that should probably be
changed.

-/

lang CarriedTypeBase = Ast
  syn CarriedType =

  sem carriedRepr : CarriedType -> Type
  sem carriedSMapAccumL : (Expr -> Expr -> Expr) -> Type -> CarriedType -> Option (Name -> Name -> Expr)
end

type Constructor = use CarriedTypeBase in
  { name : Name
  , fragment : Name
  , synType : Name
  , carried : CarriedType
  }

type SFuncRequest = use Ast in
  { synName : Name
  , target : Type
  , names :
    { smapAccumL : Name
    , smap : Name
    , sfold : Name
    }
  }

type FieldAccessorRequest = use Ast in
  { synName : Name
  , field : String
  , resTy : Type
  , names :
    { get : Name
    , set : Name
    , mapAccum : Name
    , map : Name
    }
  }

type GenInput =
  { baseName : Name
  , composedName : Option Name
  , constructors : [Constructor]
  , sfunctions : [SFuncRequest]
  , fieldAccessors : [FieldAccessorRequest]
  }

let _nulet_ = lam n. lam body. lam inexpr. use LetAst in TmLet
  { ident = n
  , body = body
  , tyAnnot = tyunknown_
  , tyBody = tyunknown_
  , inexpr = inexpr
  , info = NoInfo ()
  , ty = tyunknown_
  }

lang CarriedTypeHelpers = CarriedTypeBase + SemDeclAst + PrettyPrint
  sem _mkSmapAccumL : SFuncRequest -> Constructor -> Option Decl
  sem _mkSmapAccumL request =
  | constructor ->
    if nameEq request.synName constructor.synType then
      let fName = nameNoSym "f" in
      match carriedSMapAccumL (appf2_ (nvar_ fName)) request.target constructor.carried with Some mkNew then
        let accName = nameNoSym "acc" in
        let valName = nameNoSym "x" in
        let decl = DeclSem
          { ident = request.names.smapAccumL
          , tyAnnot = tyunknown_
          , tyBody = tyunknown_  -- TODO(vipa, 2023-03-09): Provide a proper type here
          , args = Some [{ident = fName, tyAnnot = tyunknown_}, {ident = accName, tyAnnot = tyunknown_}]
          , includes = []
          , cases =
            [ { pat = npcon_ constructor.name (npvar_ valName)
              , thn = match_
                (mkNew accName valName)
                (ptuple_ [npvar_ accName, npvar_ valName])
                (utuple_ [nvar_ accName, nconapp_ constructor.name (nvar_ valName)])
                never_
              }
            ]
          , info = NoInfo ()  -- TODO(vipa, 2023-03-09): Info
          } in
        Some decl
      else None ()
    else None ()

  sem _mkAccess : FieldAccessorRequest -> Constructor -> [Decl]
  -- sem _mkAccess synType field =
  sem _mkAccess request =
  | constructor ->
    if nameEq constructor.synType request.synName then
      let targetName = nameSym "target" in
      let valName = nameNoSym "val" in
      let getf = DeclSem
        { ident = request.names.get
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_  -- TODO(vipa, 2023-03-09): provide a proper type here
        , args = Some []
        , includes = []
        , cases =
          [ { pat = npcon_ constructor.name (npvar_ targetName)
            , thn = recordproj_ request.field (nvar_ targetName)
            }
          ]
        , info = NoInfo () -- TODO(vipa, 2023-03-09): Info
        } in
      let setf = DeclSem
        { ident = request.names.set
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_  -- TODO(vipa, 2023-03-09): provide a proper type here
        , args = Some [{ident = valName, tyAnnot = tyunknown_}]
        , includes = []
        , cases =
          [ { pat = npcon_ constructor.name (npvar_ targetName)
            , thn = nconapp_ constructor.name (recordupdate_ (nvar_ targetName) request.field (nvar_ valName))
            }
          ]
        , info = NoInfo () -- TODO(vipa, 2023-03-09): Info
        } in
      [getf, setf]
    else []

  sem _mkSFuncStubs : SFuncRequest -> [Decl]
  sem _mkSFuncStubs = | request ->
    let synTy = ntycon_ request.synName in
    let fName = nameNoSym "f" in
    let accName = nameNoSym "acc" in
    let valName = nameSym "x" in
    let smapAccumL_ = appf3_ (nvar_ request.names.smapAccumL) in
    let smapAccumL =
      let ty = tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", request.target, tytuple_ [tyvar_ "a", request.target]]
        , tyvar_ "a"
        , synTy
        , tytuple_ [tyvar_ "a", synTy]
        ])
      in DeclSem
      { ident = request.names.smapAccumL
      , tyAnnot = ty
      , tyBody = ty
      , includes = []
      , args = Some
        [ {ident = fName, tyAnnot = tyunknown_}
        , {ident = accName, tyAnnot = tyunknown_}
        ]
      , cases =
        [ {pat = npvar_ valName, thn = utuple_ [nvar_ accName, nvar_ valName]}
        ]
      , info = NoInfo ()
      } in
    let smap =
      let ty = tyarrows_
        [ tyarrow_ request.target request.target
        , synTy
        , synTy
        ]
      in DeclSem
      { ident = request.names.smap
      , tyAnnot = ty
      , tyBody = ty
      , includes = []
      , args = Some
        [ {ident = fName, tyAnnot = tyunknown_}
        ]
      , cases =
        [ { pat = npvar_ valName
          , thn = tupleproj_ 1
            (smapAccumL_
              (ulam_ "" (nulam_ valName (utuple_ [uunit_, appf1_ (nvar_ fName) (nvar_ valName)])))
              uunit_
              (nvar_ valName))
          }
        ]
      , info = NoInfo ()
      } in
    let sfold =
      let ty = tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", request.target, tyvar_ "a"]
        , tyvar_ "a"
        , synTy
        , tyvar_ "a"
        ])
      in DeclSem
      { ident = request.names.sfold
      , tyAnnot = ty
      , tyBody = ty
      , includes = []
      , args = Some
        [ {ident = fName, tyAnnot = tyunknown_}
        , {ident = accName, tyAnnot = tyunknown_}
        ]
      , cases =
        [ { pat = npvar_ valName
          , thn = tupleproj_ 0
            (smapAccumL_
              (nulam_ accName (nulam_ valName (utuple_ [appf2_ (nvar_ fName) (nvar_ accName) (nvar_ valName), nvar_ valName])))
              (nvar_ accName)
              (nvar_ valName))
          }
        ]
      , info = NoInfo ()
      } in
    [smapAccumL, smap, sfold]
end

let _mkFieldStubs
  : use DeclAst in FieldAccessorRequest -> [Decl]
  = lam request.
    use SemDeclAst in
    let synTy = ntycon_ request.synName in
    let ty = request.resTy in
    let fName = nameNoSym "f" in
    let accName = nameNoSym "acc" in
    let valName = nameNoSym "val" in
    let targetName = nameSym "target" in
    let getf =
      let ty = tyarrow_ synTy ty
      in DeclSem
      { ident = request.names.get
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , cases = []
      , includes = []
      , info = NoInfo ()
      } in
    let getf_ = appf1_ (nvar_ request.names.get) in
    let setf =
      let ty = tyarrows_ [ty, synTy, synTy]
      in DeclSem
      { ident = request.names.set
      , tyAnnot = ty
      , tyBody = ty
      , args = Some [{ident = valName, tyAnnot = tyunknown_}]
      , cases = []
      , includes = []
      , info = NoInfo ()
      } in
    let setf_ = appf2_ (nvar_ request.names.set) in
    let mapAccumf =
      let ty = tyall_ "a" (tyarrows_
        [ tyarrows_ [tyvar_ "a", ty, tytuple_ [tyvar_ "a", ty]]
        , tyvar_ "a"
        , synTy
        , tytuple_ [tyvar_ "a", synTy]
        ])
      in DeclSem
      { ident = request.names.mapAccum
      , tyAnnot = ty
      , includes = []
      , tyBody = ty
      , args = Some [{ident = fName, tyAnnot = tyunknown_}, {ident = accName, tyAnnot = tyunknown_}]
      , cases =
        [ { pat = npvar_ targetName
          , thn = match_
            (appf2_ (nvar_ fName) (nvar_ accName) (getf_ (nvar_ targetName)))
            (ptuple_ [npvar_ accName, npvar_ valName])
            (utuple_ [nvar_ accName, setf_ (nvar_ valName) (nvar_ targetName)])
            never_
          }
        ]
      , info = NoInfo ()
      } in
    let mapf =
      let ty = tyarrows_
        [ tyarrow_ ty ty
        , synTy
        , synTy
        ]
      in DeclSem
      { ident = request.names.map
      , tyAnnot = ty
      , includes = []
      , tyBody = ty
      , args = Some [{ident = fName, tyAnnot = tyunknown_}]
      , cases =
        [ { pat = npvar_ targetName
          , thn = setf_ (appf1_ (nvar_ fName) (getf_ (nvar_ targetName))) (nvar_ targetName)
          }
        ]
      , info = NoInfo ()
      } in
    [getf, setf, mapAccumf, mapf]

lang CarriedTarget = CarriedTypeBase + Eq + Ast
  syn CarriedType =
  | TargetType {targetable : Bool, ty : Type}

  sem carriedRepr =
  | TargetType {ty = ty} -> ty

  sem carriedSMapAccumL f targetTy =
  | TargetType {targetable = false} -> None ()
  | TargetType {targetable = true, ty = ty} ->
    if eqType ty targetTy
    then Some (lam accName. lam valName. f (nvar_ accName) (nvar_ valName))
    else None ()
end

lang CarriedSeq = CarriedTypeBase
  syn CarriedType =
  | SeqType CarriedType

  sem carriedRepr =
  | SeqType ty -> tyseq_ (carriedRepr ty)

  sem carriedSMapAccumL f targetTy =
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

  sem carriedSMapAccumL f targetTy =
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
  : use Ast in Type
  -> use CarriedTypeBase in CarriedType
  = lam ty. use CarriedTarget in TargetType {targetable = true, ty = ty}

let untargetableType
  : use Ast in Type
  -> use CarriedTypeBase in CarriedType
  = lam ty. use CarriedTarget in TargetType {targetable = false, ty = ty}

let seqType
  : use CarriedTypeBase in CarriedType
  -> CarriedType
  = lam ty. use CarriedSeq in SeqType ty

let optionType
  : use CarriedTypeBase in CarriedType
  -> CarriedType
  = lam ty. use CarriedOption in OptionType ty

let recordType
  : use CarriedTypeBase in [(String, CarriedType)]
  -> CarriedType
  = lam fields. use CarriedRecord in RecordType fields

let tupleType
  : use CarriedTypeBase in  [CarriedType]
  -> CarriedType
  = lam fields. recordType (mapi (lam i. lam field. (int2string i, field)) fields)

lang CarriedTypeGenerate = CarriedTypeHelpers + LangDeclAst + TypeDeclAst + SynDeclAst
  sem mkLanguages : GenInput -> [Decl]
  sem mkLanguages =
  | input ->
    let synTypes = foldl
      (lam acc. lam c: Constructor. setInsert c.synType acc)
      (setEmpty nameCmp)
      input.constructors in
    let synTypes = setFold
      (lam acc. lam synType. cons (DeclSyn {ident = synType, includes = [], params = [], defs = [], info = NoInfo ()}) acc)
      []
      synTypes in
    type DeclLangRec =
      { ident : Name
      , includes : [Name]
      , decls : [Decl]
      , info : Info
      } in
    let baseLang: DeclLangRec =
      let sfunctions = join
        (map _mkSFuncStubs input.sfunctions) in
      let accessors = join
        (map _mkFieldStubs input.fieldAccessors) in
      { ident = input.baseName
      , includes = []
      , decls = join [synTypes, sfunctions, accessors]
      , info = NoInfo () -- TODO(vipa, 2023-03-09): info?
      } in
    let mkConstructorLang : Constructor -> DeclLangRec = lam constructor.
      match constructor with {name = name, synType = synType, carried = carried} then
        let recordTyName = nameNoSym (concat (nameGetStr name) "Record") in
        let sfunctions = mapOption
          (lam request. _mkSmapAccumL request constructor)
          input.sfunctions in
        let accessors = map
          (lam request. _mkAccess request constructor)
          input.fieldAccessors in
        { ident = constructor.fragment
        , includes = [input.baseName]
        , decls =
          join
            [ [ DeclType {ident = recordTyName, params = [], tyIdent = carriedRepr carried, info = NoInfo ()}
              , DeclSyn {ident = synType, includes = [], params = [], defs = [{ident = name, tyIdent = ntycon_ recordTyName}], info = NoInfo ()}
              ]
            , sfunctions
            , join accessors
            ]
        , info = NoInfo ()
        }
      else never in
    let constructorLangs = map mkConstructorLang input.constructors in
    let constructorLangs =
      match input.composedName with Some name then
        snoc
          constructorLangs
          { ident = name
          , includes = map (lam x. x.ident) constructorLangs
          , decls = []
          , info = NoInfo ()
          }
      else constructorLangs in
  map (lam x. DeclLang x) (cons baseLang constructorLangs)
end

lang CarriedBasic = CarriedTypeGenerate + CarriedTarget + CarriedSeq + CarriedRecord + CarriedOption
end

lang TestLang = CarriedBasic + MExprEq + MExprPrettyPrint
end

mexpr

use TestLang in

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
  , fragment = nameSym "TmRecordAst"
  , synType = nameNoSym "Expr"
  , carried = tyRecord
  } in

let varConstructor =
  { name = nameSym "TmVar"
  , fragment = nameSym "TmVarAst"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("ident", tyName)
    ]
  } in

let seqConstructor =
  { name = nameSym "TmSeq"
  , fragment = nameSym "TmSeqAst"
  , synType = nameNoSym "Expr"
  , carried = recordType
    [ ("info", tyInfo)
    , ("ty", tyType)
    , ("tms", seqType tyExpr)
    ]
  } in

let input =
  { baseName = nameNoSym "MExprBase"
  , constructors = [recordConstructor, varConstructor, seqConstructor]
  , sfunctions =
    [ {synName = nameNoSym "Expr", target = tycon_ "Info", names = {smapAccumL = nameNoSym "smapAccumL_EI", smap = nameNoSym "smap_EI", sfold = nameNoSym "sfold_EI"}}
    , {synName = nameNoSym "Expr", target = tycon_ "Expr", names = {smapAccumL = nameNoSym "smapAccumL_EI", smap = nameNoSym "smap_EI", sfold = nameNoSym "sfold_EI"}}
    , {synName = nameNoSym "Expr", target = tycon_ "Type", names = {smapAccumL = nameNoSym "smapAccumL_EI", smap = nameNoSym "smap_EI", sfold = nameNoSym "sfold_EI"}}
    ]
  , composedName = Some (nameNoSym "Composed")
  , fieldAccessors = []
  } in

let res = mkLanguages input in
-- printLn res;

let recordConstructor =
  { name = nameSym "TmRecord"
  , fragment = nameSym "TmRecordAst"
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
  { baseName = nameNoSym "MExprBase"
  , constructors = [recordConstructor]
  , sfunctions =
    [ {synName = nameNoSym "Expr", target = tycon_ "Expr", names = {smapAccumL = nameNoSym "smapAccumL_EE", smap = nameNoSym "smap_EE", sfold = nameNoSym "sfold_EE"}}
    ]
  , composedName = Some (nameNoSym "Composed")
  , fieldAccessors = []
  } in
-- printLn res;

-- TODO(vipa, 2021-03-05): The tests here need to parse and evaluate
-- MLang, so I'm holding off on doing it in an automated fashion until
-- `boot-parser.mc` handles that

()
