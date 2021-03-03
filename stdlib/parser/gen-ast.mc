include "mexpr/eq.mc"

type SynType = String
let _eqSynType = eqString
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

let _equalTypes = use MExprEq in eqType assocEmpty
let _typeToString = use MExprPrettyPrint in lam ty. (getTypeStringCode 0 pprintEnvEmpty ty).1
let _patToString = use MExprPrettyPrint in lam pat. (getPatStringCode 0 pprintEnvEmpty pat).1
let _exprToString = use MExprPrettyPrint in expr2str
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
  = lam func.
    match func with {name = name, preCaseArgs = preCaseArgs, cases = cases} then
      let pprintArg = lam arg.
        match arg with (name, ty) then
          join [" (", nameGetStr name, " : ", _typeToString ty, ")"]
        else never in
      let pprintCase = lam case.
        match case with (pat, expr) then
          join ["| ", _patToString pat, " -> ", _exprToString expr, "\n"]
        else never in
      join
        [ "sem ", name
        , join (map pprintArg preCaseArgs)
        , " =\n"
        , join (map pprintCase cases)
        ]
    else never

let _mkSmapAccumL
  : SynType -- "Container" type
  -> Type -- Target type
  -> Constructor
  -> Option SemanticFunction
  = lam synType. lam targetTy. lam constructor.
    if _eqSynType synType constructor.synType then
      let fName = nameSym "f" in
      match constructor.carried.smapAccumL (appf2_ (nvar_ fName)) targetTy with Some mkNew then
        let accName = nameSym "acc" in
        let valName = nameSym "x" in
        Some
          { name = join ["smapAccumL_", _synTypeToString synType, "_", _typeToString targetTy]
          , preCaseArgs =
            [ (fName, tyarrows_ [tyvar_ "a", targetTy, tytuple_ [tyvar_ "a", targetTy]])
            , (accName, tyvar_ "a")
            ]
          , cases =
            [ (npcon_ constructor.name (npvar_ valName), mkNew accName valName)
            ]
          }
      else None ()
    else None ()

let _mkSfuncStubs
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

let bareType
  : Type
  -> CarriedType
  = lam ty.
    { repr = ty
    , smapAccumL = lam func_. lam targetTy.
      if _equalTypes ty targetTy
      then Some (lam accName. lam valName. func_ (nvar_ accName) (nvar_ valName))
      else None ()
    }

let seqType
  : CarriedType
  -> CarriedType
  = lam inner.
    { repr = tyseq_ inner.repr
    , smapAccumL = lam func_. lam targetTy.
      match inner.smapAccumL func_ targetTy with Some mkNew then Some
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
    }

let recordType
  : [(String, CarriedType)]
  -> CarriedType
  = lam fields.
    { repr = tyrecord_
      (map (lam x. (x.0, (x.1).repr)) fields)
    , smapAccumL = lam func_. lam targetTy.
      let mappingFields = mapOption
        (lam x. optionMap (lam y. (x.0, y)) ((x.1).smapAccumL func_ targetTy))
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
              (foldl
                (lam acc. lam update.
                  recordupdate_ acc update.0 (nvar_ update.1))
                (nvar_ valName)
                mappedFields)
          else never
        )
    }

let tupleType
  : [CarriedType]
  -> CarriedType
  = lam fields. recordType (mapi (lam i. lam field. (int2string i, field)) fields)

mexpr

let tyInfo = bareType (tyvar_ "Info") in
let tyString = bareType tystr_ in
let tyExpr = bareType (tyvar_ "Expr") in
let tyField = tupleType [tyString, tyExpr] in
let tyFields = seqType tyField in
let tyRecord = recordType
  [ ("info", tyInfo)
  , ("fields", tyFields)
  ] in
let recordConstructor =
  { name = nameSym "TmRecord"
  , synType = "Expr"
  , carried = tyRecord
  } in

for_ (_mkSfuncStubs "Expr" (tyvar_ "Info"))
  (lam semFunc. printLn (_pprintSemanticFunction semFunc));

(match _mkSmapAccumL "Expr" (tyvar_ "Info") recordConstructor with Some semFunc then
  printLn (_pprintSemanticFunction semFunc)
else never);

()

-- match
--   let fields = x.fields in
--   mapAccumL
--     (lam acc. lam x2.
--          match
--            let #var"1" = x2.1 in
--            f acc1 #var"1"
--          with
--            {#label"1" = #var"1", #label"0" = acc1}
--          then
--            { x2
--              with
--              #label"1" =
--                #var"1" }
--          else
--            never)
--     acc
--     fields
-- with {#label"1" = fields, #label"0" = acc} then
--   { x
--     with
--     fields =
--       fields }
-- else
--   never
