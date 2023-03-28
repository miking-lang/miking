include "gen-ast.mc"

type OperatorUnsplitter
con AtomUnsplit : use Ast in
  ({record : Expr, info : Expr} -> Expr) -> OperatorUnsplitter
con PrefixUnsplit : use Ast in
  ({record : Expr, info : Expr, right : Expr} -> Expr) -> OperatorUnsplitter
con PostfixUnsplit : use Ast in
  ({record : Expr, info : Expr, left : Expr} -> Expr) -> OperatorUnsplitter
con InfixUnsplit : use Ast in
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

type GenOperator = use Ast in
  { requiredFragments : [Name]
  , opConstructorName : Name
  , precedenceKey : Option Name
  , baseTypeName : Name
  , carried : Type
  , mkUnsplit : OperatorUnsplitter
  , assoc : Assoc
  }
/-
NOTE(vipa, 2023-05-08): There are a bunch of names in
`GenOpInput.syns`, so for ease of understanding here are some
examples, using the current naming scheme for `Expr` in a language
`Lang` and a key-value pair `(k, v)`:

- `k = Expr`
- `v.baseFragmentName = LangBaseAst`
- `v.bad.conName = BadExpr`, which is defined in `v.bad.langName = BadExprAst`
-/
type SynDesc =
  { bad : {conName : Name, langName : Name} -- The constructor created upon parse failure in this syn
  , grouping : Option (String, String)
  , precedence : Map (Name, Name) Ordering
  , baseFragmentName : Name -- The fragment declaring the normal `syn`
  }
type FieldLabels =
  { info : String, terms : String }
type GenOpInput =
  { fieldLabels : FieldLabels
  , syns : Map Name SynDesc
  , namingScheme :
    { synName : String -> String -- e.g., `Expr` -> `ExprOp`
    , opBaseLangName : String -> String -- e.g., `ExprOp` -> `ExprOpBase`
    }
  -- , mkSynName : String -> String -- namingScheme.synName
  -- , mkSynAstBaseName : String -> String -- This should be provided as a `Name` directly instead
  -- , mkConAstName : String -> String -- This should be provided as a `Name` directly instead
  -- , mkBaseName : String -> String -- namingScheme.opBaseLangName
  , composedName : Name
  , operators : [GenOperator]
  , extraFragments : [Name]
  }
type InternalSynDesc =
  { bad : {conName : Name, langName : Name} -- The constructor created upon parse failure in this syn
  , grouping : Option (String, String)
  , precedence : Map (Name, Name) Ordering
  , baseFragmentName : Name -- The fragment declaring the normal `syn`
  -- The names below are newly generated and not used outside of gen-op-ast (except indirectly).
  , synName : Name -- The `Name` of the type that contains all operators for this syn
  , baseOpFragmentName : Name -- The base fragment declaring the `syn` for the operators
  , functions :
    { topAllowed : Name
    , leftAllowed : Name
    , rightAllowed : Name
    , groupingsAllowed : Name
    , parenAllowed : Name
    , getInfo : Name
    , getTerms : Name
    , unsplit : Name
    }
  }

let _incNames =
  { v =
    { allowedDirectionTy = nameNoSym "AllowedDirection"
    , mergeInfo = nameNoSym "mergeInfo"
    , foldl = nameNoSym "foldl"
    , optionMap = nameNoSym "optionMap"
    , optionBind = nameNoSym "optionBind"
    , breakableFinalizeParse = nameNoSym "breakableFinalizeParse"
    , breakableDefaultHighlight = nameNoSym "breakableDefaultHighlight"
    , optionGetOr = nameNoSym "optionGetOr"
    , breakableAddAtom = nameNoSym "breakableAddAtom"
    , breakableAddInfix = nameNoSym "breakableAddInfix"
    , breakableAddPrefix = nameNoSym "breakableAddPrefix"
    , breakableAddPostfix = nameNoSym "breakableAddPostfix"
    }
  , c =
    { gneither = nameNoSym "GNeither"
    , gleft = nameNoSym "GLeft"
    , gright = nameNoSym "GRight"
    , geither = nameNoSym "GEither"
    , noInfo = nameNoSym "NoInfo"
    , info = nameNoSym "Info"
    , none = nameNoSym "None"
    , some = nameNoSym "Some"
    , atomP = nameNoSym "AtomP"
    , prefixP = nameNoSym "PrefixP"
    , postfixP = nameNoSym "PostfixP"
    , infixP = nameNoSym "InfixP"
    }
  , t =
    { infoTy = nameNoSym "Info"
    , permanentNode = nameNoSym "PermanentNode"
    }
  }

let _allowedDirectionTy = ntycon_ _incNames.v.allowedDirectionTy
let _gneither = nconapp_ _incNames.c.gneither unit_
let _gleft = nconapp_ _incNames.c.gleft unit_
let _gright = nconapp_ _incNames.c.gright unit_
let _geither = nconapp_ _incNames.c.geither unit_
let _infoTy = ntycon_ _incNames.t.infoTy
let _permanentNode_ = lam ty. tyapp_ (ntycon_ _incNames.t.permanentNode) ty

let _mergeInfos_ : use Ast in [Expr] -> Expr = lam exprs. switch exprs
  case [] then nconapp_ _incNames.c.noInfo unit_
  case [x] then x
  case [a, b] then appf2_ (nvar_ _incNames.v.mergeInfo) a b
  case [first] ++ exprs then appf3_ (nvar_ _incNames.v.foldl) (nvar_ _incNames.v.mergeInfo) first (seq_ exprs)
  end

let _nletin_ : use Ast in Name -> Type -> Expr -> Expr -> Expr
  = lam name. lam ty. lam val. lam body.
    use MExprAst in
    TmLet {ident = name, tyAnnot = ty, tyBody = tyunknown_, body = val, inexpr = body, ty = tyunknown_, info = NoInfo ()}

let _nuletin_ : use Ast in Name -> Expr -> Expr -> Expr
  = lam name. lam val. lam body.
    _nletin_ name tyunknown_ val body

let _uletin_ : use Ast in String -> Expr -> Expr -> Expr
  = lam name. lam val. lam body.
    _nletin_ (nameNoSym name) tyunknown_ val body

let _mkBaseFragment
  : use LangDeclAst in (Name, InternalSynDesc) -> Decl
  = lam names.
    use SemDeclAst in
    use SynDeclAst in
    use LangDeclAst in
    match names with (originalName, desc) in
    let synName = desc.synName in
    let synTy_ = lam l. lam r. tyapp_ (tyapp_ (ntycon_ synName) l) r in
    let synTy = synTy_ (tyvar_ "lstyle") (tyvar_ "rstyle") in

    let topAllowed =
      let ty = tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy tybool_)
      in DeclSem
      { ident = desc.functions.topAllowed
      , tyBody = ty
      , tyAnnot = ty
      , args = Some []
      , includes = []
      , cases = [{pat = pvarw_, thn = true_}]
      , info = NoInfo ()
      }
    in
    let leftAllowed =
      let ty = tyalls_ ["lstyle", "style", "rstyle"] (tyarrow_
        (tyrecord_ [("parent", synTy_ (tycon_ "LOpen") (tyvar_ "style")), ("child", synTy)])
        tybool_)
      in DeclSem
      { ident = desc.functions.leftAllowed
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , includes = []
      , cases = [{pat = pvarw_, thn = true_}]
      , info = NoInfo ()
      }
    in
    let rightAllowed =
      let ty = tyalls_ ["style", "lstyle", "rstyle"] (tyarrow_
        (tyrecord_ [("parent", synTy_ (tyvar_ "style") (tycon_ "ROpen")), ("child", synTy)])
        tybool_)
      in DeclSem
      { ident = desc.functions.rightAllowed
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , includes = []
      , cases = [{pat = pvarw_, thn = true_}]
      , info = NoInfo ()
      }
    in
    let groupingsAllowed =
      let ty = tyalls_ ["lstyle", "rstyle"] (tyarrow_ (tytuple_ [synTy_ (tyvar_ "lstyle") (tycon_ "ROpen"), synTy_ (tycon_ "LOpen") (tyvar_ "rstyle")]) _allowedDirectionTy)
      in DeclSem
      { ident = desc.functions.groupingsAllowed
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , includes = []
      , cases = [{pat = pvarw_, thn = _geither}]
      , info = NoInfo ()
      }
    in
    let parenAllowed =
      let ty = tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy _allowedDirectionTy)
      in DeclSem
      { ident = desc.functions.parenAllowed
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , includes = []
      , cases = [{pat = pvarw_, thn = _geither}]
      , info = NoInfo ()
      }
    in
    let getInfo =
      let ty = tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy _infoTy)
      in DeclSem
      { ident = desc.functions.getInfo
      , tyAnnot = ty
      , tyBody = ty
      , cases = []
      , args = Some []
      , includes = []
      , info = NoInfo ()
      }
    in
    let getTerms =
      let ty = tyalls_ ["lstyle", "rstyle"] (tyarrow_ synTy (tyseq_ _infoTy))
      in DeclSem
      { ident = desc.functions.getTerms
      , tyAnnot = ty
      , tyBody = ty
      , cases = []
      , args = Some []
      , includes = []
      , info = NoInfo ()
      }
    in
    let unsplit =
      let ty = tyarrow_ (_permanentNode_ (ntycon_ synName)) (tytuple_ [_infoTy, ntycon_ originalName])
      in DeclSem
      { ident = desc.functions.unsplit
      , tyAnnot = ty
      , tyBody = ty
      , args = Some []
      , cases = []
      , includes = []
      , info = NoInfo ()
      }
    in
    DeclLang
    { ident = desc.baseOpFragmentName
    , includes = [desc.baseFragmentName]
    , decls =
      [ DeclSyn {ident = synName, params = [nameNoSym "lstyle", nameNoSym "rstyle"], defs = [], includes = [], info = NoInfo ()}
      , topAllowed, leftAllowed, rightAllowed, groupingsAllowed
      , parenAllowed, getInfo, getTerms, unsplit
      ]
    , info = NoInfo ()
    }

lang GenOpAstLang = SynDeclAst + SemDeclAst + LangDeclAst
  sem _mkConstructorFragment
  : FieldLabels
  -> Map Name InternalSynDesc
  -> GenOperator
  -> Decl
  sem _mkConstructorFragment labels synNames = | op ->
    let desc = mapFindExn op.baseTypeName synNames in
    let synName = desc.synName in
    let conName = op.opConstructorName in

    let getInfo =
      let x = nameSym "x" in
      DeclSem
      { ident = desc.functions.getInfo
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , args = Some []
      , includes = []
      , cases = [{pat = npcon_ conName (npvar_ x), thn = recordproj_ labels.info (nvar_ x)}]
      , info = NoInfo ()
      } in
    let getTerms =
      let x = nameSym "x" in
      DeclSem
      { ident = desc.functions.getTerms
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , args = Some []
      , includes = []
      , cases = [{pat = npcon_ conName (npvar_ x), thn = recordproj_ labels.terms (nvar_ x)}]
      , info = NoInfo ()
      } in
    let unsplit =
      let unsplit_ = lam r. app_ (nvar_ desc.functions.unsplit) r in
      let x = nameSym "x" in
      let arm = switch op.mkUnsplit
        case AtomUnsplit f then
          { pat = npcon_ _incNames.c.atomP (prec_ [("self", npcon_ conName (npvar_ x))])
          , thn = utuple_
            [ recordproj_ labels.info (nvar_ x)
            , f {record = nvar_ x, info = recordproj_ labels.info (nvar_ x)}
            ]
          }
        case PrefixUnsplit f then
          let info = nameSym "info" in
          let r = nameSym "r" in
          let rinfo = nameSym "rinfo" in
          { pat = npcon_ _incNames.c.prefixP
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("rightChildAlts", pseqedgew_ [npvar_ r] [])
              ]
            )
          , thn = match_
            (unsplit_ (nvar_ r))
            (ptuple_ [npvar_ rinfo, npvar_ r])
            (_nuletin_ info (_mergeInfos_ [recordproj_ labels.info (nvar_ x), nvar_ rinfo])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , right = nvar_ r , info = nvar_ info}
                ]))
            never_
          }
        case PostfixUnsplit f then
          let info = nameSym "info" in
          let l = nameSym "l" in
          let linfo = nameSym "linfo" in
          { pat = npcon_ _incNames.c.postfixP
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("leftChildAlts", pseqedgew_ [npvar_ l] [])
              ]
            )
          , thn = match_
            (unsplit_ (nvar_ l))
            (ptuple_ [npvar_ linfo, npvar_ l])
            (_nuletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ labels.info (nvar_ x)])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , left = nvar_ l , info = nvar_ info}
                ]))
            never_
          }
        case InfixUnsplit f then
          let info = nameSym "info" in
          let l = nameSym "l" in
          let linfo = nameSym "linfo" in
          let r = nameSym "r" in
          let rinfo = nameSym "rinfo" in
          { pat = npcon_ _incNames.c.infixP
            (prec_
              [ ("self", npcon_ conName (npvar_ x))
              , ("leftChildAlts", pseqedgew_ [npvar_ l] [])
              , ("rightChildAlts", pseqedgew_ [npvar_ r] [])
              ]
            )
          , thn = match_
            (utuple_ [unsplit_ (nvar_ l), unsplit_ (nvar_ r)])
            (ptuple_
              [ ptuple_ [npvar_ linfo, npvar_ l]
              , ptuple_ [npvar_ rinfo, npvar_ r]
              ])
            (_nuletin_ info (_mergeInfos_ [nvar_ linfo, recordproj_ labels.info (nvar_ x), nvar_ rinfo])
              (utuple_
                [ nvar_ info
                , f { record = nvar_ x , left = nvar_ l, right = nvar_ r , info = nvar_ info}
                ]))
            never_
          }
        end
      in DeclSem
      { ident = desc.functions.unsplit
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , args = Some []
      , includes = []
      , cases = [arm]
      , info = NoInfo ()
      } in
    let grouping = match (op.mkUnsplit, op.assoc) with (InfixUnsplit _, !NAssoc _)
      then [ DeclSem
        { ident = desc.functions.groupingsAllowed
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_
        , args = Some []
        , includes = []
        , cases =
          [ { pat = ptuple_ [npcon_ op.opConstructorName pvarw_, npcon_ op.opConstructorName pvarw_]
            , thn = match op.assoc with LAssoc _ then nconapp_ _incNames.c.gleft unit_ else nconapp_ _incNames.c.gright unit_
            }
          ]
        , info = NoInfo ()
        }]
      else [] in
    DeclLang
    { ident = conName  -- TODO(vipa, 2023-05-08): This reuses a `Name`, though in a different kind of scope. Might be worth creating a new name and syncing, but it's too much work right now
    , includes = cons desc.baseOpFragmentName op.requiredFragments
    , decls = concat
      grouping
      [ DeclSyn
        { ident = synName
        , params = [nameNoSym "lstyle", nameNoSym "rstyle"]
        , includes = []
        , defs = [{ident = conName, tyIdent = op.carried}]
        , info = NoInfo ()
        }
      , getInfo
      , getTerms
      , unsplit
      ]
    , info = NoInfo ()
    }
end

let _mkGroupingSem
  : use SemDeclAst in Map Name {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
  -> InternalSynDesc
  -> Decl
  = lam opMap. lam desc.
    use SemDeclAst in
    let mkCase
      : Ordering
      -> {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
      -> {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
      -> Option {pat : Pat, thn : Expr}
      = lam ordering. lam l. lam r.
        if and l.canBeLeft r.canBeRight then
          let dir = switch ordering
            case LT _ then Some _incNames.c.gright
            case GT _ then Some _incNames.c.gleft
            case EQ _ then
              switch (l.assoc, r.assoc)
              case (LAssoc _, LAssoc _) then Some _incNames.c.gleft
              case (RAssoc _, RAssoc _) then Some _incNames.c.gright
              case _ then None ()
              end
            end
          in match dir with Some dir then
            Some {pat = ptuple_ [npcon_ l.conName pvarw_, npcon_ r.conName pvarw_], thn = nconapp_ dir unit_}
          else None ()
        else None () in
    let mkCases : ((Name, Name), Ordering) -> [{pat : Pat, thn : Expr}] = lam pair.
      let linfo : {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
        = mapFindExn pair.0 .0 opMap in
      let rinfo : {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name}
        = mapFindExn pair.0 .1 opMap in
      mapOption identity
        [ mkCase pair.1 linfo rinfo, mkCase (flipOrdering pair.1) rinfo linfo ]
    in DeclSem
    { ident = desc.functions.groupingsAllowed
    , tyAnnot = tyunknown_
    , tyBody = tyunknown_
    , args = Some []
    , includes = []
    , cases = join (map mkCases (mapBindings desc.precedence))
    , info = NoInfo ()
    }

let _mkComposedFragment
  : use LangDeclAst in GenOpInput -> Map Name InternalSynDesc -> [Decl] -> Decl
  = lam config. lam synDescs. lam fragments.
    use LangDeclAst in
    let opFragments : [Name] = mapOption
      (lam decl. match decl with DeclLang x then Some x.ident else None ())
      fragments in
    let badFragments : [Name] = map
      (lam desc. desc.bad.langName)
      (mapValues synDescs) in
    let opMap : Map Name {canBeLeft : Bool, canBeRight : Bool, assoc : Assoc, conName : Name} = mapFromSeq nameCmp
      (mapOption
        (lam op: GenOperator. match op.precedenceKey with Some key then
          switch op.mkUnsplit
          case AtomUnsplit _ then Some (key, {canBeLeft = false, canBeRight = false, assoc = op.assoc, conName = op.opConstructorName})
          case PrefixUnsplit _ then Some (key, {canBeLeft = true, canBeRight = false, assoc = op.assoc, conName = op.opConstructorName})
          case InfixUnsplit _ then Some (key, {canBeLeft = true, canBeRight = true, assoc = op.assoc, conName = op.opConstructorName})
          case PostfixUnsplit _ then Some (key, {canBeLeft = false, canBeRight = true, assoc = op.assoc, conName = op.opConstructorName})
          end else None ())
        config.operators) in
    let groupingSems = map (_mkGroupingSem opMap) (mapValues synDescs) in
    DeclLang
    { ident = config.composedName
    , includes = join
      [ opFragments
      , badFragments
      , config.extraFragments
      ]
    , decls = groupingSems
    , info = NoInfo ()
    }

type WrapperInfo = use Ast in
  { addAtom_ : Expr -> Expr -> Expr -> Expr
  , addInfix_ : Expr -> Expr -> Expr -> Expr
  , addPrefix_ : Expr -> Expr -> Expr -> Expr
  , addPostfix_ : Expr -> Expr -> Expr -> Expr
  , finalize_ : Expr -> Expr -> Expr
  , definitions : [Expr]
  }

let _mkBrWrappersFor
  : Name -> InternalSynDesc -> WrapperInfo
  = lam original. lam desc.
    let stateTy = tyrecord_
      [ ("errors", tyapp_ (tycon_ "Ref") (tyseq_ (tytuple_ [tycon_ "Info", tystr_])))
      , ("content", tycon_ "String")
      ] in
    match match desc.grouping with Some x then x else ("(", ")") with (lparStr, rparStr) in
    let configName = nameSym "config" in
    let reportConfigName = nameSym "reportConfig" in
    let addAtomName = nameSym (join ["add", nameGetStr desc.synName, "Atom"]) in
    let addInfixName = nameSym (join ["add", nameGetStr desc.synName, "Infix"]) in
    let addPrefixName = nameSym (join ["add", nameGetStr desc.synName, "Prefix"]) in
    let addPostfixName = nameSym (join ["add", nameGetStr desc.synName, "Postfix"]) in
    let finalizeName = nameSym (concat "finalize" (nameGetStr desc.synName)) in
    let mkTotalFunc = lam callee: Name.
      (ulam_ "" (ulam_ "x" (ulam_ "st"
        (appf2_ (nvar_ _incNames.v.optionMap)
          (appf2_ (nvar_ callee) (nvar_ configName) (var_ "x"))
          (var_ "st"))))) in
    let mkPartialFunc = lam callee: Name.
      (lam_ "p" stateTy (ulam_ "x" (ulam_ "st"
        (match_ (var_ "st") (npcon_ _incNames.c.some (pvar_ "st"))
          (_uletin_ "st"
            (appf3_ (nvar_ callee) (nvar_ configName) (var_ "x") (var_ "st"))
            (semi_
              (match_ (var_ "st") (npcon_ _incNames.c.none pvarw_)
                (modref_ (recordproj_ "errors" (var_ "p"))
                  (snoc_ (deref_ (recordproj_ "errors" (var_ "p")))
                    (utuple_
                      [ app_ (nvar_ desc.functions.getInfo) (var_ "x")
                      , str_ "Invalid input"
                      ])))
                (unit_))
              (var_ "st")))
          (nconapp_ _incNames.c.none unit_))))) in
    let definitions =
      [ nulet_ configName
        (urecord_
          [ ("topAllowed", freeze_ (nvar_ desc.functions.topAllowed))
          , ("leftAllowed", freeze_ (nvar_ desc.functions.leftAllowed))
          , ("rightAllowed", freeze_ (nvar_ desc.functions.rightAllowed))
          , ("parenAllowed", freeze_ (nvar_ desc.functions.parenAllowed))
          , ("groupingsAllowed", freeze_ (nvar_ desc.functions.groupingsAllowed))
          ])
      , nulet_ reportConfigName
        (urecord_
          [ ("parenAllowed", freeze_ (nvar_ desc.functions.parenAllowed))
          , ("topAllowed", freeze_ (nvar_ desc.functions.topAllowed))
          , ("terminalInfos", freeze_ (nvar_ desc.functions.getTerms))
          , ("getInfo", freeze_ (nvar_ desc.functions.getInfo))
          , ("lpar", str_ lparStr)
          , ("rpar", str_ rparStr)
          ])
      , nulet_ addAtomName (mkTotalFunc (_incNames.v.breakableAddAtom))
      , nulet_ addInfixName (mkPartialFunc (_incNames.v.breakableAddInfix))
      , nulet_ addPrefixName (mkTotalFunc (_incNames.v.breakableAddPrefix))
      , nulet_ addPostfixName (mkPartialFunc (_incNames.v.breakableAddPostfix))
      , nulet_ finalizeName
        (lam_ "p" stateTy (ulam_ "st"
          (_uletin_ "res"
            (appf2_ (nvar_ _incNames.v.optionBind) (var_ "st")
              (ulam_ "st"
                (match_
                  (appf2_ (nvar_ _incNames.v.breakableFinalizeParse) (nvar_ configName) (var_ "st"))
                  (npcon_ _incNames.c.some (pand_ (pvar_ "tops") (pseqedgew_ [pvar_ "top"] [])))
                  (_uletin_ "errs"
                    (appf3_ (nvar_ _incNames.v.breakableDefaultHighlight) (nvar_ reportConfigName) (recordproj_ "content" (var_ "p")) (var_ "tops"))
                    (_uletin_ "res"
                      (app_ (nvar_ desc.functions.unsplit) (var_ "top"))
                      (if_ (null_ (var_ "errs"))
                        (nconapp_ _incNames.c.some (var_ "res"))
                        (semi_
                          (modref_ (recordproj_ "errors" (var_ "p"))
                            (concat_ (deref_ (recordproj_ "errors" (var_ "p"))) (var_ "errs")))
                            (nconapp_ _incNames.c.some
                              (utuple_
                                [ tupleproj_ 0 (var_ "res")
                                , nconapp_ desc.bad.conName (urecord_ [("info", tupleproj_ 0 (var_ "res"))])
                                ]))))))
                  (semi_
                    (modref_ (recordproj_ "errors" (var_ "p"))
                      (snoc_
                        (deref_ (recordproj_ "errors" (var_ "p")))
                        (utuple_ [nconapp_ _incNames.c.noInfo unit_, str_ (concat "Unfinished " (nameGetStr original))])))
                    (nconapp_ _incNames.c.none unit_)))))
            (appf2_ (nvar_ _incNames.v.optionGetOr)
              (utuple_
                [ nconapp_ _incNames.c.noInfo unit_
                , nconapp_ desc.bad.conName (urecord_ [("info", nconapp_ _incNames.c.noInfo unit_)])
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

type GenOpResult = use LangDeclAst in use Ast in
  { fragments : [Decl]
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
  : Map Name InternalSynDesc -> GenOpResult
  = lam synDescs.
    let wrappers = mapMapWithKey _mkBrWrappersFor synDescs in
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


lang MkOpLanguages = GenOpAstLang
  sem mkOpLanguages
  : GenOpInput -> GenOpResult
  sem mkOpLanguages = | config ->
    let synDescs : Map Name InternalSynDesc = mapMapWithKey
      (lam original. lam desc.
        let synStr = config.namingScheme.synName (nameGetStr original) in
        { bad = desc.bad
        , grouping = desc.grouping
        , precedence = desc.precedence
        , baseFragmentName = desc.baseFragmentName
        , synName = nameSym synStr
        , baseOpFragmentName = nameSym (config.namingScheme.opBaseLangName (nameGetStr original))
        , functions =
          { topAllowed = nameSym (concat "topAllowed_" synStr)
          , leftAllowed = nameSym (concat "leftAllowed_" synStr)
          , rightAllowed = nameSym (concat "rightAllowed_" synStr)
          , groupingsAllowed = nameSym (concat "groupingsAllowed_" synStr)
          , parenAllowed = nameSym (concat "parenAllowed_" synStr)
          , getInfo = nameSym (concat "getInfo_" synStr)
          , getTerms = nameSym (concat "getTerms_" synStr)
          , unsplit = nameSym (concat "unsplit_" synStr)
          }
        })
      config.syns in
    let baseFragments = map _mkBaseFragment (mapBindings synDescs) in
    let constructorFragments = map (_mkConstructorFragment config.fieldLabels synDescs) config.operators in
    let composedFragment = _mkComposedFragment config synDescs constructorFragments in
    let fragments = join
      [ baseFragments
      , constructorFragments
      , [composedFragment]
      ] in
    let res : GenOpResult = _mkBrWrappers synDescs in
    {res with fragments = concat fragments res.fragments}
end
