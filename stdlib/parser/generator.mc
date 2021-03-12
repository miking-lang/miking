include "mexpr/ast-builder.mc"
include "semantic.mc"
include "gen-ast.mc"

type GeneratorSymbol-- TODO(vipa, 2021-03-08): Create remaining cases
-- TODO(vipa, 2021-03-12): We want to support alternatives as well, or
-- at least optional elements, but to make that easy we probably want
-- to add support for that in `semantic.mc`
con GeneratorLit : {lit : String} -> GeneratorSymbol
con GeneratorLIdent : {field : Option String} -> GeneratorSymbol
con GeneratorUIdent : {field : Option String} -> GeneratorSymbol
con GeneratorNonSyntax : {field : String, fieldType : Type, fieldValue : Expr} -> GeneratorSymbol
con GeneratorNt : {field : Option String, nt : NonTerminal} -> GeneratorSymbol

type GeneratorProdType
con GeneratorAtom :
  { self : DefaultInclude
  } -> GeneratorProdType
con GeneratorPrefix :
  { self : DefaultInclude
  , right : DefaultInclude
  , rightField : Option String
  } -> GeneratorProdType
con GeneratorInfix :
  { self : DefaultInclude
  , left : DefaultInclude
  , leftField : Option String
  , right : DefaultInclude
  , rightField : Option String
  } -> GeneratorProdType
con GeneratorPostfix :
  { self : DefaultInclude
  , left : DefaultInclude
  , leftField : Option String
  } -> GeneratorProdType

type GeneratorOverride
con GeneratorLeftChild : { child : GeneratorProduction, parent : GeneratorProduction } -> GeneratorOverride
con GeneratorRightChild : { child : GeneratorProduction, parent : GeneratorProduction } -> GeneratorOverride

let generatorLit_ : String -> GeneratorSymbol = lam lit. GeneratorLit {lit = lit}

-- A `GeneratorStaged t` is an expression of type `t`.
type GeneratorStaged t = Expr

type GeneratorProduction =
  { stagedSpec : GeneratorStaged ProductionSpec
  , constructor : Option Constructor
  , sym : Symbol
  , nonTerminal : String
  }

let _semanticProductionName = nameSym "semanticProduction"
let _semanticGrammarName = nameSym "semanticGrammar"
let _semanticNonTerminalName = nameSym "semanticNonTerminal"
let _semanticParseFileName = nameSym "semanticParseFile"
let _semanticLeftChildName = nameSym "LeftChild"
let _semanticRightChildName = nameSym "RightChild"
let _semanticAtomName = nameSym "Atom"
let _semanticPrefixName = nameSym "Prefix"
let _semanticInfixName = nameSym "Infix"
let _semanticPostfixName = nameSym "Postfix"
let _semanticDefaultInName = nameSym "DefaultIn"
let _semanticDefaultNotInName = nameSym "DefaultNotIn"
let _semanticLitName = nameSym "semanticLit"
let _semanticLIdentName = nameSym "semanticLIdent"
let _semanticShortenErrorsName = nameSym "semanticShortenErrors"
let _rightConName = nameSym "Right"
let _leftConName = nameSym "Left"
let _eitherMapRightName = nameSym "eitherMapRight"
let _infoTypeName = nameSym "Info"
let _symSeqInfoName = nameSym "_symSeqInfo"
let _headName = nameSym "head"
let _lastName = nameSym "last"
let _ll1TokName = nameSym "Tok"
let _ll1UserSymName = nameSym "UserSym"
let _lexerLIdentName = nameSym "LIdentTok"
let _lexerUIdentName = nameSym "UIdentTok"
let _dprintLnName = nameSym "dprintLn"

let _env =
  match optionFoldlM pprintAddStr pprintEnvEmpty
    [ _semanticProductionName
    , _semanticGrammarName
    , _semanticNonTerminalName
    , _semanticParseFileName
    , _semanticLeftChildName
    , _semanticRightChildName
    , _semanticAtomName
    , _semanticPrefixName
    , _semanticInfixName
    , _semanticPostfixName
    , _semanticDefaultInName
    , _semanticDefaultNotInName
    , _semanticLitName
    , _semanticLIdentName
    , _semanticShortenErrorsName
    , _rightConName
    , _leftConName
    , _eitherMapRightName
    , _infoTypeName
    , _symSeqInfoName
    , _headName
    , _lastName
    , _ll1TokName
    , _ll1UserSymName
    , _lexerLIdentName
    , _lexerUIdentName
    , _dprintLnName
    ]
  with Some env then env
  else never

let _semanticProduction_ = app_ (nvar_ _semanticProductionName)
let _semanticGrammar_ = app_ (nvar_ _semanticGrammarName)
let _semanticNonTerminal_ = app_ (nvar_ _semanticNonTerminalName)
let _semanticParseFile_ = appf3_ (nvar_ _semanticParseFileName)
let _semanticLeftChild_ = nconapp_ _semanticLeftChildName
let _semanticRightChild_ = nconapp_ _semanticRightChildName
let _semanticAtom_ = nconapp_ _semanticAtomName
let _semanticPrefix_ = nconapp_ _semanticPrefixName
let _semanticInfix_ = nconapp_ _semanticInfixName
let _semanticPostfix_ = nconapp_ _semanticPostfixName
let _semanticDefaultIn_ = nconapp_ _semanticDefaultInName unit_
let _semanticDefaultNotIn_ = nconapp_ _semanticDefaultNotInName unit_
let _semanticLit_ = app_ _semanticLitName
let _semanticLIdent_ = nvar_ _semanticLIdentName
let _semanticShortenErrors_ = app_ (nvar_ _semanticShortenErrorsName)
let _symSeqInfo_ = app_ (nvar_ _symSeqInfoName)
let _head_ = app_ (nvar_ _headName)
let _last_ = app_ (nvar_ _lastName)
let _dprintLn_ = app_ (nvar_ _dprintLnName)
let _eitherMapRight_ = appf2_ (nvar_ _eitherMapRightName)

let _sequentialComposition_ = lam a. lam b. use LetAst in TmLet
  { ident = nameSym ""
  , body = a
  , tyBody = tyunknown_
  , inexpr = b
  , info = NoInfo ()
  , ty = tyunknown_
  }

let generatorProd
  : { constructorName : String
    , nonTerminal : NonTerminal
    , prodType : GeneratorProdType
    , syntax : [GeneratorSymbol]
    }
  -> GeneratorProduction
  = lam spec.
    match spec with
      { constructorName = constructorStr
      , nonTerminal = nonTerminal
      , prodType = prodType
      , syntax = syntax
      }
    then
      let sym = gensym () in

      -- Constructor, i.e., input for ast-gen.mc
      recursive let symbolToConstructorField
        : GeneratorSymbol
        -> Option (String, CarriedType)
        = lam sym.
          match sym with GeneratorLit _ then None () else-- TODO(vipa, 2021-03-10): Fill in remaining cases
          match sym with GeneratorLIdent {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorUIdent {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorNonSyntax {field = name, fieldType = ty} then
            Some (name, untargetableType ty) else
          match sym with GeneratorNt {field = Some name, nt = nt} then
            Some (name, targetableType (tyvar_ nt))
          else None ()
      in
      let stageSymbol = lam sym.
        match sym with GeneratorLit {lit = lit} then
          _semanticLit_ (str_ lit)
        else match sym with GeneratorLIdent _ then
          _semanticLIdent_
        else never in-- TODO(vipa, 2021-03-12): Implement
      let constructorName = nameSym constructorStr in
      let wrappedSyntax =
        match prodType with GeneratorAtom _ then syntax
        else match prodType with GeneratorPrefix {rightField = rName} then
          snoc
            syntax
            (GeneratorNt {field = rName, nt = nonTerminal})
        else match prodType with GeneratorInfix {leftField = lName, rightField = rName} then
          cons
            (GeneratorNt {field = lName, nt = nonTerminal})
            (snoc
              syntax
              (GeneratorNt {field = rName, nt = nonTerminal}))
        else match prodType with GeneratorPostfix {leftFiled = lName} then
          cons
            (GeneratorNt {field = lName, nt = nonTerminal})
            syntax
        else never in
      let constructor =
        { name = constructorName
        , synType = stringToSynType nonTerminal
        , carried = recordType
          (cons ("info", untargetableType (ntyvar_ _infoTypeName))
            (mapOption symbolToConstructorField wrappedSyntax))
        } in

      -- Staged production spec, i.e., input for semantic.mc
      let stagedSpec =
        let stageInclude = lam inc.
          match inc with DefaultIn _ then _semanticDefaultIn_ else
          match inc with DefaultNotIn _ then _semanticDefaultNotIn_ else
          never in
        let stagedProdType =
          match prodType with GeneratorAtom {self = self} then
            _semanticAtom_ (record_ [("self", stageInclude self)])
          else match prodType with GeneratorPrefix {self = self, right = right} then
            _semanticPrefix_ (record_ [("self", stageInclude self), ("right", stageInclude right)])
          else match prodType with GeneratorInfix {self = self, left = left, right = right} then
            _semanticInfix_ (record_ [("self", stageInclude self), ("left", stageInclude left), ("right", stageInclude right)])
          else match prodType with GeneratorPostfix {self = self, left = left} then
            _semanticPostfix_ (record_ [("self", stageInclude self), ("left", stageInclude left)])
          else never in
        let stageField = lam sym.
          match sym with GeneratorLIdent {field = Some field} then
            let valName = nameSym "ident" in
            ( Some (npcon_ _ll1TokName (npcon_ _lexerLIdentName (prec_ [("val", npvar_ valName)])))
            , Some (field, nvar_ valName)
            )
          else match sym with GeneratorUIdent {field = Some field} then
            let valName = nameSym "ident" in
            ( Some (npcon_ _ll1TokName (npcon_ _lexerUIdentName (prec_ [("val", npvar_ valName)])))
            , Some (field, nvar_ valName)
            )
          else match sym with GeneratorNonSyntax {field = field, fieldValue = val} then
            ( None ()
            , Some (field, val)
            )
          else match sym with GeneratorNt {field = Some field} then
            let valName = nameSym "val" in
            ( Some (npcon_ _ll1UserSymName (ptuple_ [pvarw_, npvar_ valName]))
            , Some (field, nvar_ valName)
            )
          else (pvarw_, None ()) in-- TODO(vipa, 2021-03-12): fill in all constructors
        let stagedAction =
          let infoName = nameSym "info" in
          let paramName = nameSym "syms" in
          nulam_ paramName
            (_nulet_ infoName (_symSeqInfo_ (nvar_ paramName))
              (tuple_
                [ nvar_ infoName
                , match unzip (map stageField wrappedSyntax) with (pats, fields) then
                    match_ (nvar_ paramName) (pseqtot_ (mapOption identity pats))
                      (nconapp_ constructorName
                        (record_
                          (cons ("info", nvar_ infoName)
                            (mapOption identity fields))))
                      never_
                  else never
                ]))
        in
        record_
          [ ("name", str_ constructorStr)
          , ("nt", var_ nonTerminal)
          , ("ptype", stagedProdType)
          , ("rhs" , seq_ (map stageSymbol syntax))
          , ("action", stagedAction)
          ]
      in

      -- Putting it together
      { constructor = Some constructor
      , sym = sym
      , stagedSpec = stagedSpec
      , nonTerminal = nonTerminal
      }
    else never

let generatorBracket
  : { nonTerminal : NonTerminal
    , leftBracket : [GeneratorSymbol]
    , rightBracket : [GeneratorSymbol]
    }
  -> GeneratorProduction
  = lam spec. never

-- TODO(vipa, 2021-03-10): We should run `semanticGrammar` once before
-- we generate the code and report errors there, then we know that the
-- grammar we generate won't produce any errors, so we don't have to
-- deal with it at that point.
let generatorGrammar
  : { langName : String
    , start : NonTerminal
    , productions : [GeneratorProduction]
    , overrideAllow : [GeneratorOverride]
    , overrideDisallow : [GeneratorOverride]
    , precedences : [((GeneratorProduction, GeneratorProduction), Precedence)]
    , sfunctions : [(NonTerminal, NonTerminal)]
    }
  -> String
  = lam grammar.
    match grammar with
      { langName = langName
      , start = start
      , productions = productions
      , overrideAllow = overrideAllow
      , overrideDisallow = overrideDisallow
      , precedences = precedences
      , sfunctions = sfunctions
      }
    then
      let composedName = concat langName "Composed" in
      let astGenInput =
        { namePrefix = langName
        , constructors = mapOption (lam x. x.constructor) productions
        , requestedSFunctions = map
          (lam x. (stringToSynType x.0, tyvar_ x.1))
          sfunctions
        , composedName = Some composedName
        } in
      let prodSymToName = lam sym. nameSetSym (nameNoSym "prod") sym in
      let stageOverride = lam o.
        match o
        with GeneratorLeftChild {child = child, parent = parent}
           | GeneratorRightChild {child = child, parent = parent}
        then
          let construct =
            match o with GeneratorLeftChild _ then _semanticLeftChild_ else _semanticRightChild_ in
          construct
            (record_
              [ ("child", nvar_ (prodSymToName child.sym))
              , ("parent", nvar_ (prodSymToName parent.sym))
              ])
        else never in
      let stagePrecedence = lam prec.
        match prec with ((l, r), {mayGroupLeft = mayGroupLeft, mayGroupRight = mayGroupRight}) then
          tuple_
            [ tuple_
              [ nvar_ (prodSymToName l.sym)
              , nvar_ (prodSymToName r.sym)
              ]
            , record_
              [ ("mayGroupLeft", bool_ mayGroupLeft)
              , ("mayGroupRight", bool_ mayGroupRight)
              ]
            ]
        else never in
      let nts = foldl
        (lam acc. lam prod. mapInsert prod.nonTerminal () acc)
        (mapEmpty cmpString)
        productions in
      let ntLets = map
        (lam pair.
          let nt = pair.0 in
          ulet_ nt (_semanticNonTerminal_ (str_ nt)))
        (mapBindings nts) in
      let productions = map
        (lam prod.
          let name = prodSymToName prod.sym in
          (name, nulet_ name (_semanticProduction_ prod.stagedSpec)))
        productions in
      match unzip productions with (prodNames, prodLets) then
        let semanticGrammar = record_
          [ ("start", var_ start)
          , ("productions", seq_ (map nvar_ prodNames))
          , ("overrideAllow", seq_ (map stageOverride overrideAllow))
          , ("overrideDisallow", seq_ (map stageOverride overrideDisallow))
          , ("precedences", seq_ (map stagePrecedence precedences))
          ] in
        let grammarName = nameSym "grammar" in
        use MExprPrettyPrint in
        let resName = nameSym "res" in
        let errsName = nameSym "errs" in
        let fileNameName = nameSym "filename" in
        let sourceName = nameSym "source" in
        let parseFuncStr = join
          [ "let parse", langName, "File = use ", composedName, " in use ParserConcrete in \n  "
          , (pprintCode 2 _env
              (_nulet_ resName
                (_semanticGrammar_ (bindall_ (snoc (concat ntLets prodLets) semanticGrammar)))
                (match_ (nvar_ resName)
                  (npcon_ _rightConName (npvar_ grammarName))
                  (nulam_ fileNameName
                    (nulam_ sourceName
                      (_eitherMapRight_ (ulam_ "x" (tupleproj_ 1 (var_ "x")))
                        (_semanticParseFile_ (nvar_ grammarName) (nvar_ fileNameName) (nvar_ sourceName)))))
                  (match_ (nvar_ resName)
                    (npcon_ _leftConName (npvar_ errsName))
                    (_sequentialComposition_
                      (_dprintLn_ (_semanticShortenErrors_ (nvar_ errsName)))
                      (error_ (str_ "Invalid grammar")))
                    never_)))).1
          , "\n"
          ] in
        use CarriedBasic in
        join
          [ "include \"parser/generator.mc\"\n"
          , "include \"parser/semantic.mc\"\n"
          , "\n"
          , mkLanguages astGenInput, "\n\n"
          , parseFuncStr]
      else never
    else never

let _symSeqInfo
  : [Symbol]
  -> Info
  = lam syms.
    let getInfo = lam sym. use ParserConcrete in
      match sym with Tok tok then tokInfo tok else
      match sym with Lit {info = info} then info else
      match sym with UserSym (info, _) then info else
      never in
    match syms with [] then NoInfo () else
    match syms with [sym] then getInfo sym else
    match syms with [first] ++ _ ++ [last] then mergeInfo (getInfo first) (getInfo last) else
    never

mexpr

let lit_ = lam lit. GeneratorLit {lit = lit} in
let lident = lam field. GeneratorLIdent {field = Some field} in
let lident_ = GeneratorLIdent {field = None ()} in
let uident = lam field. GeneratorUIdent {field = Some field} in
let uident_ = GeneratorUIdent {field = None ()} in
let nonsyntax = lam field. lam fieldType. lam fieldValue. GeneratorNonSyntax {field = field, fieldType = fieldType, fieldValue = fieldValue} in
let nt = lam field. lam nt. GeneratorNt {field = Some field, nt = nt} in
let nt_ = lam nt. GeneratorNt {field = None (), nt = nt} in

let varP = generatorProd
  { constructorName = "TmVar"
  , nonTerminal = "Expr"
  , prodType = GeneratorAtom {self = DefaultIn ()}
  , syntax = [lident "ident"]
  } in

let appP = generatorProd
  { constructorName = "TmApp"
  , nonTerminal = "Expr"
  , prodType = GeneratorInfix {self = DefaultIn (), left = DefaultIn (), right = DefaultIn (), leftField = Some "f", rightField = Some "a"}
  , syntax = []
  } in

let res = generatorGrammar
  { langName = "MExpr"
  , start = "Expr"
  , productions = [varP, appP]
  , overrideAllow = []
  , overrideDisallow = []
  , precedences = join
    [ [semanticGroupLeft appP appP]
    ]
  , sfunctions = [("Expr", "Expr")]
  } in

printLn res;

()
