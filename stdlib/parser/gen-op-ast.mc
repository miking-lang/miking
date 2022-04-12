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

let _nletin_ : Name -> Expr -> Expr -> Expr
  = lam name. lam val. lam body.
    use MExprAst in
    TmLet {ident = name, tyBody = tyunknown_, body = val, inexpr = body, ty = tyunknown_, info = NoInfo ()}

let _mkBaseFragment
  : GenOpInput -> (Name, Name) -> LanguageFragment
  = lam config. lam names.
    let originalName = names.0 in
    let synName = names.1 in
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
  : GenOpInput -> Map Name Name -> GenOperator -> LanguageFragment
  = lam config. lam synNames. lam op.
    let synName = mapFindExn op.baseTypeName synNames in
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
            (_nletin_ info (_mergeInfos_ [recordproj_ config.infoFieldLabel (nvar_ x), nvar_ rinfo])
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
            (_nletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ config.infoFieldLabel (nvar_ x)])
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
            (_nletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ config.infoFieldLabel (nvar_ x), nvar_ rinfo])
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

let mkOpLanguages
  : GenOpInput -> String
  = lam config.
    use CarriedBasic in
    let opTypeNames : Map Name Name =
      let res = map (lam x : GenOperator. x.baseTypeName) config.operators in
      let res = setOfSeq nameCmp res in
      mapMapWithKey (lam key. lam. nameSym (config.mkSynName key)) res in
    let baseFragments = map (_mkBaseFragment config) (mapBindings opTypeNames) in
    let constructorFragments = map (_mkConstructorFragment config opTypeNames) config.operators in
    strJoin "\n\n" (concat (map _pprintLanguageFragment baseFragments) (map _pprintLanguageFragment constructorFragments))
