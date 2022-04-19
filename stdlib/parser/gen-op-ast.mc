include "gen-ast.mc"

type OperatorUnsplitter
con AtomUnsplit :
  ({record : Expr, info : Expr} -> Expr) -> OperatorUnsplitter
con PrefixUnsplit :
  ({record : Expr, info : Expr, right : Expr} -> Expr) -> OperatorUnsplitter
con PostfixUnsplit :
  ({record : Expr, info : Expr, left : Expr} -> Expr) -> OperatorUnsplitter
con InfixUnsplit :
  ({record : Expr, info : Expr, left : Expr, right : Expr} -> Expr) -> OperatorUnsplitter

type GenOperator =
  { baseConstructorName : Name
  , opConstructorName : Name
  , baseTypeName : Name
  , carried : Type
  , mkUnsplit : OperatorUnsplitter
  }
type GenOpInput =
  { infoFieldLabel : String
  , termsFieldLabel : String
  , syns : Map Name {bad : Name}
  , mkSynName : Name -> String
  , mkSynAstBaseName : Name -> String
  , mkConAstName : Name -> String
  , mkBaseName : String -> String
  , composedName : String
  , operators : [GenOperator]
  }

let _allowedDirectionTy = ntycon_ (nameSym "AllowedDirection")
let _gneither = nconapp_ (nameSym "GNeither") unit_
let _gleft = nconapp_ (nameSym "GLeft") unit_
let _gright = nconapp_ (nameSym "GRight") unit_
let _geither = nconapp_ (nameSym "GEither") unit_
let _infoTy = ntycon_ (nameSym "Info")
let _permanentNodeName = nameSym "PermanentNode"
let _permanentNode_ = lam ty. tyapp_ (ntycon_ _permanentNodeName) ty

let _mergeInfos_ : [Expr] -> Expr = lam exprs. switch exprs
  case [] then conapp_ "NoInfo" unit_
  case [x] then x
  case [a, b] then appf2_ (var_ "mergeInfo") a b
  case [first] ++ exprs then appf3_ (var_ "foldl") (var_ "mergeInfo") first (seq_ exprs)
  end

let _nletin_ : Name -> Type -> Expr -> Expr -> Expr
  = lam name. lam ty. lam val. lam body.
    use MExprAst in
    TmLet {ident = name, tyBody = ty, body = val, inexpr = body, ty = tyunknown_, info = NoInfo ()}

let _letin_ : String -> Type -> Expr -> Expr -> Expr
  = lam name. lam ty. lam val. lam body.
    _nletin_ (nameNoSym name) ty val body

let _nuletin_ : Name -> Expr -> Expr -> Expr
  = lam name. lam val. lam body.
    _nletin_ name tyunknown_ val body

let _uletin_ : String -> Expr -> Expr -> Expr
  = lam name. lam val. lam body.
    _nletin_ (nameNoSym name) tyunknown_ val body

let _mkBaseFragment
  : GenOpInput -> (Name, {bad : Name, op : name}) -> LanguageFragment
  = lam config. lam names.
    let originalName = names.0 in
    let synName = names.1 .op in
    let suffix = concat "_" (nameGetStr synName) in

    let topAllowed =
      { name = concat "topAllowed" suffix
      , ty = Some (tyarrow_ (ntycon_ synName) tybool_)
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let leftAllowed =
      { name = concat "leftAllowed" suffix
      , ty = Some (tyarrow_
        (tyrecord_ [("parent", ntycon_ synName), ("child", ntycon_ synName)])
        tybool_)
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let rightAllowed =
      { name = concat "rightAllowed" suffix
      , ty = Some (tyarrow_
        (tyrecord_ [("parent", ntycon_ synName), ("child", ntycon_ synName)])
        tybool_)
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let groupingsAllowed =
      { name = concat "groupingsAllowed" suffix
      , ty = Some (tyarrow_ (ntycon_ synName) _allowedDirectionTy)
      , preCaseArgs = []
      , cases = [(pvarw_, _geither)]
      }
    in
    let parenAllowed =
      { name = concat "parenAllowed" suffix
      , ty = Some (tyarrow_ (ntycon_ synName) _allowedDirectionTy)
      , preCaseArgs = []
      , cases = [(pvarw_, _geither)]
      }
    in
    let getInfo =
      { name = join ["get", suffix, "_info"]
      , ty = Some (tyarrow_ (ntycon_ synName) _infoTy)
      , preCaseArgs = []
      , cases = []
      }
    in
    let getTerms =
      { name = join ["get", suffix, "_terms"]
      , ty = Some (tyarrow_ (ntycon_ synName) (tyseq_ _infoTy))
      , preCaseArgs = []
      , cases = []
      }
    in
    let unsplit =
      { name = concat "unsplit" suffix
      , ty = Some (tyarrow_ (_permanentNode_ (ntycon_ synName)) (tytuple_ [_infoTy, ntycon_ originalName]))
      , preCaseArgs = []
      , cases = []
      }
    in

    { name = config.mkBaseName (nameGetStr synName)
    , extends = [config.mkSynAstBaseName originalName]
    , aliases = []
    , synTypes = mapInsert synName [] (mapEmpty nameCmp)
    , semanticFunctions =
      [ topAllowed, leftAllowed, rightAllowed, groupingsAllowed
      , parenAllowed, getInfo, getTerms, unsplit
      ]
    }

let _mkConstructorFragment
  : GenOpInput -> Map Name {bad : Name, op : Name} -> GenOperator -> LanguageFragment
  = lam config. lam synNames. lam op.
    let synName = (mapFindExn op.baseTypeName synNames).op in
    let conName = op.opConstructorName in
    let suffix = concat "_" (nameGetStr synName) in

    let getInfo =
      let x = nameSym "x" in
      { name = join ["get", suffix, "_info"]
      , ty = None ()
      , preCaseArgs = []
      , cases = [(npcon_ conName (npvar_ x), recordproj_ config.infoFieldLabel (nvar_ x))]
      } in
    let getTerms =
      let x = nameSym "x" in
      { name = join ["get", suffix, "_terms"]
      , ty = None ()
      , preCaseArgs = []
      , cases = [(npcon_ conName (npvar_ x), recordproj_ config.termsFieldLabel (nvar_ x))]
      } in
    let unsplit =
      let unsplitStr = concat "unsplit" suffix in
      let unsplit_ = lam r. app_ (var_ unsplitStr) r in
      let x = nameSym "x" in
      let arm = switch op.mkUnsplit
        case AtomUnsplit f then
          ( pcon_ "AtomP" (prec_ [("self", npcon_ conName (npvar_ x))])
          , utuple_
            [ recordproj_ config.infoFieldLabel (nvar_ x)
            , f {record = nvar_ x, info = recordproj_ config.infoFieldLabel (nvar_ x)}
            ]
          )
        case PrefixUnsplit f then
          let info = nameSym "info" in
          let r = nameSym "r" in
          let rinfo = nameSym "rinfo" in
          ( pcon_ "PrefixP"
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("rightChildAlts", pseqedgew_ [npvar_ r] [])
              ]
            )
          , match_
            (unsplit_ (nvar_ r))
            (ptuple_ [npvar_ rinfo, npvar_ r])
            (_nuletin_ info (_mergeInfos_ [recordproj_ config.infoFieldLabel (nvar_ x), nvar_ rinfo])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , right = nvar_ r , info = nvar_ info}
                ]))
            never_
          )
        case PostfixUnsplit f then
          let info = nameSym "info" in
          let l = nameSym "l" in
          let linfo = nameSym "linfo" in
          ( pcon_ "PostfixP"
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("leftChildAlts", pseqedgew_ [npvar_ l] [])
              ]
            )
          , match_
            (unsplit_ (nvar_ l))
            (ptuple_ [npvar_ linfo, npvar_ l])
            (_nuletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ config.infoFieldLabel (nvar_ x)])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , left = nvar_ l , info = nvar_ info}
                ]))
            never_
          )
        case InfixUnsplit f then
          let info = nameSym "info" in
          let l = nameSym "l" in
          let linfo = nameSym "linfo" in
          let r = nameSym "r" in
          let rinfo = nameSym "rinfo" in
          ( pcon_ "InfixP"
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("leftChildAlts", pseqedgew_ [npvar_ l] [])
              , ("rightChildAlts", pseqedgew_ [npvar_ r] [])
              ]
            )
          , match_
            (utuple_ [unsplit_ (nvar_ l), unsplit_ (nvar_ r)])
            (ptuple_
              [ ptuple_ [npvar_ linfo, npvar_ l]
              , ptuple_ [npvar_ rinfo, npvar_ r]
              ])
            (_nuletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ config.infoFieldLabel (nvar_ x), nvar_ rinfo])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , left = nvar_ l, right = nvar_ r , info = nvar_ info}
                ]))
            never_
          )
        end
      in
      { name = concat "unsplit" suffix
      , ty = None ()
      , preCaseArgs = []
      , cases = [arm]
      } in

    { name = nameGetStr conName
    , extends =
      [ config.mkBaseName (nameGetStr synName)
      , config.mkConAstName op.baseConstructorName
      ]
    , aliases = []
    , synTypes = mapInsert synName [{name = conName, synType = synName, carried = untargetableType op.carried}] (mapEmpty nameCmp)
    , semanticFunctions = [getInfo, getTerms, unsplit]
    }

type WrapperInfo =
  { addAtom_ : Expr -> Expr -> Expr -> Expr
  , addInfix_ : Expr -> Expr -> Expr -> Expr
  , addPrefix_ : Expr -> Expr -> Expr -> Expr
  , addPostfix_ : Expr -> Expr -> Expr -> Expr
  , finalize_ : Expr -> Expr -> Expr
  , definitions : [Expr]
  }

let _mkBrWrappersFor
  : GenOpInput -> {original: Name, op: Name, bad: Name} -> WrapperInfo
  = lam config. lam name.
    let stateTy = tyrecord_
      [ ("errors", tyapp_ (tycon_ "Ref") (tyseq_ (tytuple_ [tycon_ "Info", tystr_])))
      , ("content", tycon_ "String")
      ] in
    let suffix = concat "_" (nameGetStr name.op) in
    let configName = nameSym "config" in
    let reportConfigName = nameSym "reportConfig" in
    let addAtomName = nameSym (join ["add", nameGetStr name.op, "Atom"]) in
    let addInfixName = nameSym (join ["add", nameGetStr name.op, "Infix"]) in
    let addPrefixName = nameSym (join ["add", nameGetStr name.op, "Prefix"]) in
    let addPostfixName = nameSym (join ["add", nameGetStr name.op, "Postfix"]) in
    let finalizeName = nameSym (concat "finalize" (nameGetStr name.op)) in
    let mkTotalFunc = lam callee: Name.
      (ulam_ "" (ulam_ "x" (ulam_ "st"
        (appf2_ (var_ "optionMap")
          (appf2_ (nvar_ callee) (nvar_ configName) (var_ "x"))
          (var_ "st"))))) in
    let mkPartialFunc = lam callee: Name.
      (lam_ "p" stateTy (ulam_ "x" (ulam_ "st"
        (match_ (var_ "st") (pcon_ "Some" (pvar_ "st"))
          (_uletin_ "st"
            (appf3_ (var_ "breakableAddInfix") (nvar_ configName) (var_ "x") (var_ "st"))
            (semi_
              (match_ (var_ "st") (pcon_ "None" pvarw_)
                (modref_ (recordproj_ "errors" (var_ "p"))
                  (snoc_ (deref_ (recordproj_ "errors" (var_ "p")))
                    (utuple_
                      [ app_ (var_ (join ["get", suffix, "_info"])) (var_ "x")
                      , str_ "Invalid input"
                      ])))
                (unit_))
              (var_ "st")))
          (var_ "st"))))) in
    let definitions =
      [ nulet_ configName
        (urecord_
          [ ("topAllowed", var_ (concat "topAllowed" suffix))
          , ("leftAllowed", var_ (concat "leftAllowed" suffix))
          , ("rightAllowed", var_ (concat "rightAllowed" suffix))
          , ("parenAllowed", var_ (concat "parenAllowed" suffix))
          , ("groupingsAllowed", var_ (concat "groupingsAllowed" suffix))
          ])
      , nulet_ reportConfigName
        (urecord_
          [ ("parenAllowed", var_ (concat "parenAllowed" suffix))
          , ("topAllowed", var_ (concat "topAllowed" suffix))
          , ("terminalInfos", var_ (join ["get", suffix, "_terms"]))
          , ("getInfo", var_ (join ["get", suffix, "_info"]))
          , ("lpar", str_ "(")
          , ("rpar", str_ ")")
          ])
      , nulet_ addAtomName (mkTotalFunc (nameNoSym "breakableAddAtom"))
      , nulet_ addInfixName (mkPartialFunc (nameNoSym "breakableAddInfix"))
      , nulet_ addPrefixName (mkTotalFunc (nameNoSym "breakableAddPrefix"))
      , nulet_ addPostfixName (mkPartialFunc (nameNoSym "breakableAddPostfix"))
      , nulet_ finalizeName
        (lam_ "p" stateTy (ulam_ "st"
          (_uletin_ "res"
            (appf2_ (var_ "optionBind") (var_ "st")
              (ulam_ "st"
                (match_
                  (appf2_ (var_ "breakableFinalizeParse") (nvar_ configName) (var_ "st"))
                  (pcon_ "Some" (pand_ (pvar_ "tops") (pseqedgew_ [pvar_ "top"] [])))
                  (_uletin_ "errs"
                    (appf3_ (var_ "breakableDefaultHighlight") (nvar_ reportConfigName) (recordproj_ "content" (var_ "p")) (var_ "tops"))
                    (_letin_ "res" (tytuple_ [tycon_ "Info", ntycon_ name.original])
                      (app_ (var_ (concat "unsplit" suffix)) (var_ "top"))
                      (if_ (null_ (var_ "errs"))
                        (conapp_ "Some" (var_ "res"))
                        (semi_
                          (modref_ (recordproj_ "errors" (var_ "p"))
                            (concat_ (deref_ (recordproj_ "errors" (var_ "p"))) (var_ "errs")))
                            (conapp_ "Some"
                              (utuple_
                                [ tupleproj_ 0 (var_ "res")
                                , nconapp_ name.bad (urecord_ [("info", tupleproj_ 0 (var_ "res"))])
                                ]))))))
                  (semi_
                    (modref_ (recordproj_ "errors" (var_ "p"))
                      (snoc_
                        (deref_ (recordproj_ "errors" (var_ "p")))
                        (utuple_ [conapp_ "NoInfo" unit_, str_ (concat "Unfinished " (nameGetStr name.original))])))
                    (conapp_ "None" unit_)))))
            (appf2_ (var_ "optionGetOr")
              (utuple_
                [ conapp_ "NoInfo" unit_
                , nconapp_ name.bad (urecord_ [("info", conapp_ "NoInfo" unit_)])
                ])
              (var_ "res")))
        ))
      ] in
    { definitions = definitions
    , addAtom_ = appf3_ (nvar_ addAtomName)
    , addInfix_ = appf3_ (nvar_ addInfixName)
    , addPrefix_ = appf3_ (nvar_ addPrefixName)
    , addPostfix_ = appf3_ (nvar_ addPostfixName)
    , finalize_ = appf2_ (nvar_ finalizeName)
    }

let _mkBrWrappers
  : GenOpInput -> Map Name Name -> GenOpResult
  = lam config. lam synNames.
    let wrappers = mapMapWithKey
      (lam original. lam names : {bad : Name, op : Name}.
        _mkBrWrappersFor config {original = original, op = names.op, bad = names.bad})
      synNames in
    let getWrapper : Name -> WrapperInfo = lam name.
      mapFindExn name wrappers in
    { fragments = ""
    , addAtomFor = lam name. (getWrapper name).addAtom_
    , addInfixFor = lam name. (getWrapper name).addInfix_
    , addPrefixFor = lam name. (getWrapper name).addPrefix_
    , addPostfixFor = lam name. (getWrapper name).addPostfix_
    , finalizeFor = lam name. (getWrapper name).finalize_
    , wrapProductions = lam expr.
      let definitions = mapFoldWithKey
        (lam acc. lam. lam wrapper: WrapperInfo. concat acc wrapper.definitions)
        []
        wrappers in
      bindall_ (snoc definitions expr)
    }

type GenOpResult =
  { fragments : String
  -- NOTE(vipa, 2022-04-12): This function wraps an expression such
  -- that the remaining functions (`addAtomFor`, etc.) can be used.
  , wrapProductions : Expr -> Expr
  -- NOTE(vipa, 2022-04-12): The arguments here are:
  -- Name (the syn name for the operator sequence we want to work on)
  -- Expr (parsing state, to report errors and the like)
  -- Expr (the operator to be added, i.e., `self lstyle rstyle`)
  -- Expr (the operator sequence already encountered)
  , addAtomFor : Name -> Expr -> Expr -> Expr -> Expr
  , addPrefixFor : Name -> Expr -> Expr -> Expr -> Expr
  , addInfixFor : Name -> Expr -> Expr -> Expr -> Expr
  , addPostfixFor : Name -> Expr -> Expr -> Expr -> Expr
  -- NOTE(vipa, 2022-04-12): The arguments here are:
  -- Name (the syn name for the operator sequence we want to work on)
  -- Expr (parsing state, to report errors and the like)
  -- Expr (the operator sequence already encountered)
  , finalizeFor : Name -> Expr -> Expr -> Expr
  }

let mkOpLanguages
  : GenOpInput -> GenOpResult
  = lam config.
    use CarriedBasic in
    let opTypeNames : Map Name {bad : Name, op : Name} = mapMapWithKey
      (lam original. lam names : {bad : Name}.
        {bad = names.bad, op = nameSym (config.mkSynName original)})
      config.syns in
    let baseFragments = map (_mkBaseFragment config) (mapBindings opTypeNames) in
    let constructorFragments = map (_mkConstructorFragment config opTypeNames) config.operators in
    let fragments = join
      [ baseFragments
      , constructorFragments
      ] in
    let res : GenOpResult = _mkBrWrappers config opTypeNames in
    {res with fragments = strJoin "\n\n" (snoc (map _pprintLanguageFragment fragments) res.fragments)}
