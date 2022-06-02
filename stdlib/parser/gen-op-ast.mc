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

type Ordering
con LT : () -> Ordering
con EQ : () -> Ordering
con GT : () -> Ordering

let flipOrdering : Ordering -> Ordering = lam x. switch x
  case LT _ then GT ()
  case GT _ then LT ()
  case EQ _ then EQ ()
  end

type Assoc
con NAssoc : () -> Assoc
con LAssoc : () -> Assoc
con RAssoc : () -> Assoc

type GenOperator =
  { baseConstructorName : Option Name
  , opConstructorName : Name
  , baseTypeName : Name
  , carried : Type
  , mkUnsplit : OperatorUnsplitter
  , assoc : Assoc
  }
type GenOpInput =
  { infoFieldLabel : String
  , termsFieldLabel : String
  , syns : Map Name {bad : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering}
  , mkSynName : Name -> String
  , mkSynAstBaseName : Name -> String
  , mkConAstName : Name -> String
  , mkBaseName : String -> String
  , composedName : String
  , operators : [GenOperator]
  , extraFragments : [String]
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
  : GenOpInput -> (Name, {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering}) -> LanguageFragment
  = lam config. lam names.
    let originalName = names.0 in
    let synName = names.1 .op in
    let synTy_ = lam l. lam r. tyapp_ (tyapp_ (ntycon_ synName) l) r in
    let synTy = synTy_ (tyvar_ "lstyle") (tyvar_ "rstyle") in
    let suffix = concat "_" (nameGetStr synName) in

    let topAllowed =
      { name = concat "topAllowed" suffix
      , ty = Some (tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy tybool_))
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let leftAllowed =
      { name = concat "leftAllowed" suffix
      , ty = Some (tyalls_ ["lstyle", "style", "rstyle"] (tyarrow_
        (tyrecord_ [("parent", synTy_ (tycon_ "LOpen") (tyvar_ "style")), ("child", synTy)])
        tybool_))
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let rightAllowed =
      { name = concat "rightAllowed" suffix
      , ty = Some (tyalls_ ["style", "lstyle", "rstyle"] (tyarrow_
        (tyrecord_ [("parent", synTy_ (tyvar_ "style") (tycon_ "ROpen")), ("child", synTy)])
        tybool_))
      , preCaseArgs = []
      , cases = [(pvarw_, true_)]
      }
    in
    let groupingsAllowed =
      { name = concat "groupingsAllowed" suffix
      , ty = Some (tyalls_ ["lstyle", "rstyle"] (tyarrow_ (tytuple_ [synTy_ (tyvar_ "lstyle") (tycon_ "ROpen"), synTy_ (tycon_ "LOpen") (tyvar_ "rstyle")]) _allowedDirectionTy))
      , preCaseArgs = []
      , cases = [(pvarw_, _geither)]
      }
    in
    let parenAllowed =
      { name = concat "parenAllowed" suffix
      , ty = Some (tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy _allowedDirectionTy))
      , preCaseArgs = []
      , cases = [(pvarw_, _geither)]
      }
    in
    let getInfo =
      { name = join ["get", suffix, "_info"]
      , ty = Some (tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy _infoTy))
      , preCaseArgs = []
      , cases = []
      }
    in
    let getTerms =
      { name = join ["get", suffix, "_terms"]
      , ty = Some (tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy (tyseq_ _infoTy)))
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
    , synTypes = mapInsert synName ([nameNoSym "lstyle", nameNoSym "rstyle"], []) (mapEmpty nameCmp)
    , semanticFunctions =
      [ topAllowed, leftAllowed, rightAllowed, groupingsAllowed
      , parenAllowed, getInfo, getTerms, unsplit
      ]
    }

let _mkConstructorFragment
  : GenOpInput -> Map Name {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering} -> GenOperator -> LanguageFragment
  = lam config. lam synNames. lam op.
    let synName =
      let tmp : {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering} = mapFindExn op.baseTypeName synNames in
      tmp.op in
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
    let grouping = match (op.mkUnsplit, op.assoc) with (InfixUnsplit _, !NAssoc _)
      then [
        { name = concat "groupingsAllowed" suffix
        , ty = None ()
        , preCaseArgs = []
        , cases =
          [ ( ptuple_ [npcon_ op.opConstructorName pvarw_, npcon_ op.opConstructorName pvarw_]
            , match op.assoc with LAssoc _ then conapp_ "GLeft" unit_ else conapp_ "GRight" unit_
            )
          ]
        }]
      else [] in
    { name = nameGetStr conName
    , extends = cons
      (config.mkBaseName (nameGetStr synName))
      (match op.baseConstructorName with Some n then [config.mkConAstName n] else [])
    , aliases = []
    , synTypes = mapInsert synName ([nameNoSym "lstyle", nameNoSym "rstyle"], [{name = conName, synType = synName, carried = untargetableType op.carried}]) (mapEmpty nameCmp)
    , semanticFunctions = concat [getInfo, getTerms, unsplit] grouping
    }

let _mkGroupingSem
  : GenOpInput
  -> Map Name {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
  -> (Name, {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering})
  -> SemanticFunction
  = lam config. lam opMap. lam binding.
    let suffix = concat "_" (nameGetStr binding.1 .op) in
    let mkCase
      : Ordering
      -> {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
      -> {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
      -> Option (Pat, Expr)
      = lam ordering. lam l. lam r.
        if and l.canBeLeft r.canBeRight then
          let dir = switch ordering
            case LT _ then Some "GRight"
            case GT _ then Some "GLeft"
            case EQ _ then
              switch (l.assoc, r.assoc)
              case (LAssoc _, LAssoc _) then Some "GLeft"
              case (RAssoc _, RAssoc _) then Some "GRight"
              case _ then None ()
              end
            end
          in match dir with Some dir then
            Some (ptuple_ [npcon_ l.conName pvarw_, npcon_ r.conName pvarw_], conapp_ dir unit_)
          else None ()
        else None () in
    let mkCases : ((Name, Name), Ordering) -> [(Pat, Expr)] = lam pair.
      let linfo : {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
        = mapFindExn pair.0 .0 opMap in
      let rinfo : {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
        = mapFindExn pair.0 .1 opMap in
      mapOption identity
        [ mkCase pair.1 linfo rinfo, mkCase (flipOrdering pair.1) rinfo linfo ]
    in
    { name = concat "groupingsAllowed" suffix
    , ty = None ()
    , preCaseArgs = []
    , cases = join (map mkCases (mapBindings binding.1 .precedence))
    }

let _mkComposedFragment
  : GenOpInput -> Map Name {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering} -> [LanguageFragment] -> LanguageFragment
  = lam config. lam opTypeNames. lam fragments.
    let opFragments : [String] = map
      (lam frag: LanguageFragment. frag.name)
      fragments in
    let badFragments : [String] = map
      (lam name: {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering}. config.mkConAstName name.bad)
      (mapValues opTypeNames) in
    let opMap : Map Name {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name} = mapFromSeq nameCmp
      (mapOption
        (lam op: GenOperator. match op.baseConstructorName with Some name then
          switch op.mkUnsplit
          case AtomUnsplit _ then Some (name, {canBeLeft = false, canBeRight = false, assoc = op.assoc, conName = op.opConstructorName})
          case PrefixUnsplit _ then Some (name, {canBeLeft = true, canBeRight = false, assoc = op.assoc, conName = op.opConstructorName})
          case InfixUnsplit _ then Some (name, {canBeLeft = true, canBeRight = true, assoc = op.assoc, conName = op.opConstructorName})
          case PostfixUnsplit _ then Some (name, {canBeLeft = false, canBeRight = true, assoc = op.assoc, conName = op.opConstructorName})
          end else None ())
        config.operators) in
    let groupingSems = map (_mkGroupingSem config opMap) (mapBindings opTypeNames) in
    { name = config.composedName
    , extends = join
      [ opFragments
      , badFragments
      , ["LL1Parser"]
      , config.extraFragments
      ]
    , aliases = []
    , synTypes = mapEmpty nameCmp
    , semanticFunctions = groupingSems
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
  : GenOpInput -> {original: Name, op: Name, bad: Name, grouping: Option (String, String), precedence : Map (Name, Name) Ordering} -> WrapperInfo
  = lam config. lam name.
    let stateTy = tyrecord_
      [ ("errors", tyapp_ (tycon_ "Ref") (tyseq_ (tytuple_ [tycon_ "Info", tystr_])))
      , ("content", tycon_ "String")
      ] in
    match match name.grouping with Some x then x else ("(", ")") with (lparStr, rparStr) in
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
            (appf3_ (nvar_ callee) (nvar_ configName) (var_ "x") (var_ "st"))
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
          (conapp_ "None" unit_))))) in
    let definitions =
      [ nulet_ configName
        (urecord_
          [ ("topAllowed", freeze_ (var_ (concat "topAllowed" suffix)))
          , ("leftAllowed", freeze_ (var_ (concat "leftAllowed" suffix)))
          , ("rightAllowed", freeze_ (var_ (concat "rightAllowed" suffix)))
          , ("parenAllowed", freeze_ (var_ (concat "parenAllowed" suffix)))
          , ("groupingsAllowed", freeze_ (var_ (concat "groupingsAllowed" suffix)))
          ])
      , nulet_ reportConfigName
        (urecord_
          [ ("parenAllowed", freeze_ (var_ (concat "parenAllowed" suffix)))
          , ("topAllowed", freeze_ (var_ (concat "topAllowed" suffix)))
          , ("terminalInfos", freeze_ (var_ (join ["get", suffix, "_terms"])))
          , ("getInfo", freeze_ (var_ (join ["get", suffix, "_info"])))
          , ("lpar", str_ lparStr)
          , ("rpar", str_ rparStr)
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

let _mkBrWrappers
  : GenOpInput -> Map Name {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering} -> GenOpResult
  = lam config. lam synNames.
    let wrappers = mapMapWithKey
      (lam original. lam names : {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering}.
        _mkBrWrappersFor config {original = original, op = names.op, bad = names.bad, grouping = names.grouping, precedence = names.precedence})
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

let mkOpLanguages
  : GenOpInput -> GenOpResult
  = lam config.
    use CarriedBasic in
    let opTypeNames : Map Name {bad : Name, op : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering} = mapMapWithKey
      (lam original. lam names : {bad : Name, grouping : Option (String, String), precedence : Map (Name, Name) Ordering}.
        {bad = names.bad, op = nameSym (config.mkSynName original), grouping = names.grouping, precedence = names.precedence})
      config.syns in
    let baseFragments = map (_mkBaseFragment config) (mapBindings opTypeNames) in
    let constructorFragments = map (_mkConstructorFragment config opTypeNames) config.operators in
    let composedFragment = _mkComposedFragment config opTypeNames constructorFragments in
    let fragments = join
      [ baseFragments
      , constructorFragments
      , [composedFragment]
      ] in
    let res : GenOpResult = _mkBrWrappers config opTypeNames in
    {res with fragments = strJoin "\n\n" (snoc (map _pprintLanguageFragment fragments) res.fragments)}
