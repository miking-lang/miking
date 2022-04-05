include "gen-ast.mc"

type OperatorUnsplitter
con AtomUnsplit :
  ({record : Expr, info : Expr} -> Expr) -> OperatorUnsplitter
con PrefixUnsplit :
  ({record : Expr, info : Expr, left : Expr} -> Expr) -> OperatorUnsplitter
con PostfixUnsplit :
  ({record : Expr, info : Expr, right : Expr} -> Expr) -> OperatorUnsplitter
con InfixUnsplit :
  ({record : Expr, info : Expr, left : Expr, right : Expr} -> Expr) -> OperatorUnsplitter

type GenOperator =
  { baseConstructorName : Name
  , baseTypeName : Name
  , carried : Type
  , mkUnsplit : OperatorUnsplitter
  }
type GenOpInput =
  { infoFieldLabel : String
  , termsFieldLabel : String
  , mkSynName : Name -> String
  , mkSynAstBaseName : Name -> String
  , mkConName : Name -> String
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

let mkOpLanguages
  : GenOpInput -> String
  = lam config.
    use CarriedBasic in
    let opTypeNames : Map Name Name =
      let res = map (lam x : GenOperator. x.baseTypeName) config.operators in
      let res = setOfSeq nameCmp res in
      mapMapWithKey (lam key. lam. nameSym (config.mkSynName key)) res in

    let mkBaseFragment
      : (Name, Name) -> LanguageFragment
      = lam names.
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
    in
    let baseFragments = map mkBaseFragment (mapBindings opTypeNames) in
    strJoin "\n\n" (map _pprintLanguageFragment baseFragments)
