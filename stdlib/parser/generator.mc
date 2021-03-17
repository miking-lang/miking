include "mexpr/ast-builder.mc"
include "semantic.mc"
include "gen-ast.mc"

/-

This file implements a small DSL for writing grammars and then
auto-generating language fragments for the AST as well as a parser
using `semantic.mc`. The main interface consists of the record
`generatorNamespace` which contains a field for every exported
function.

The main working function is `grammar`, which takes a grammar and
produces a string containing the generated code.

-- TODO(vipa, 2021-03-16): Once we have proper AST types for language
fragments we should probably return those instead, maybe have a
convenience function that produces the string.

The generated AST types will be in broken form and will typically
require a post-processing step to unbreak. This post-processing can
typically be expressed fairly concisely with `smap`, for example:

```
let g = generatorNamespace in

-- Broken "if"
let ifP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmIfBroken"
  , prodType = g.defPrefix "thenExpr"
  , syntax = [g.lit_ "if", g.nt "condition" "Expr", g.lit_ "then", tyField]
  } in

let elseP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmElseBroken"
  , prodType = GeneratorInfix
    { self = DefaultIn ()
    , left = DefaultNotIn ()
    , right = DefaultIn ()
    , leftField = Some "ifExpr"
    , rightField = Some "elseExpr"
    }
  , syntax = [g.lit_ "else", tyField]
  } in

-- Broken "match"
let matchP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmMatch"
  , prodType = GeneratorAtom {self = DefaultNotIn ()}
  , syntax =
    [ g.lit_ "match", g.nt "target" "Expr", g.lit_ "with"
    , g.nonsyntax "arms"
      (seqType
        (tupleType
          [ targetableType (tyvar_ "Pat")
          , targetableType (tyvar_ "Expr")
          ]))
      (seq_ [])
    , tyField]
  } in

let matchArmP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmMatchArmBroken"
  , prodType = GeneratorInfix
    { self = DefaultIn ()
    , left = DefaultNotIn ()
    , right = DefaultIn ()
    , leftField = Some "prev"
    , rightField = Some "armExpr"
    }
  , syntax = [g.lit_ "|", g.nt "pat" "Pat", g.lit_ "->", tyField]
  } in

-- After grammar generation we (manually) write the following language
fragments:
lang MExprpostProcess = MExprComposed
  sem postProcessExpr =
  | t -> postProcessExprUp (smap_Expr_Expr postProcessExpr (postProcessExprDown t))

  sem postProcessExprDown =
  | t -> t
  sem postProcessExprUp =
  | t -> t
end

lang MExprTmIf = MExprBase
  syn Expr =
  | TmIf {info : Info, condition : Expr, thenExpr : Expr, elseExpr : Option Expr, ty : Type}

  -- omitted smapAccumL_Expr_Expr
end

lang MExprUnbreakIf = MExprpostProcess + MExprTmIf
  sem postProcessExprDown =
  | TmElseBroken
    { info = info
    , ifExpr = TmIfBroken
      { condition = condition
      , thenExpr = thenExpr
      }
    , elseExpr = elseExpr
    } ->
    TmIf
      { info = info
      , condition = condition
      , thenExpr = thenExpr
      , elseExpr = Some elseExpr
      , ty = TyUnknown ()
      }
  | TmIfBroken
    { info = info
    , condition = condition
    , thenExpr = thenExpr
    } ->
    TmIf
      { info = info
      , condition = condition
      , thenExpr = thenExpr
      , elseExpr = None ()
      }
end

lang MExprUnbreakMatch = MExprpostProcess
  sem postProcessExprUp =
  | TmMatchArmBroken
    { info = info
    , prev = TmMatch r
    , pat = pat
    , armExpr = armExpr
    } ->
    TmMatch {{r with arms = snoc r.arms (pat, armExpr) } with info = info}
end

lang Unbreaking = MExprUnbreakIf + MExprUnbreakMatch

-- We can then "unbreak" a value "tm" of type "Expr" like so:

use Unbreaking in postprocessExpr tm

```

-/

type GeneratorSymbol
-- TODO(vipa, 2021-03-12): We want to support alternatives as well, or
-- at least optional elements, but to make that easy we probably want
-- to add support for that in `semantic.mc`
con GeneratorInt : {field : Option String} -> GeneratorSymbol
con GeneratorFloat : {field : Option String} -> GeneratorSymbol
con GeneratorOperator : {field : Option String} -> GeneratorSymbol
con GeneratorString : {field : Option String} -> GeneratorSymbol
con GeneratorChar : {field : Option String} -> GeneratorSymbol
con GeneratorHashString : {field : Option String, tag : String} -> GeneratorSymbol
con GeneratorLit : {lit : String} -> GeneratorSymbol
con GeneratorLIdent : {field : Option String} -> GeneratorSymbol
con GeneratorUIdent : {field : Option String} -> GeneratorSymbol
con GeneratorNonSyntax : {field : String, fieldType : CarriedType, fieldValue : Expr} -> GeneratorSymbol
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
let _semanticIntName = nameSym "semanticInt"
let _semanticFloatName = nameSym "semanticFloat"
let _semanticOperatorName = nameSym "semanticOperator"
let _semanticStringName = nameSym "semanticString"
let _semanticCharName = nameSym "semanticChar"
let _semanticHashStringName = nameSym "semanticHashString"
let _semanticLitName = nameSym "semanticLit"
let _semanticLIdentName = nameSym "semanticLIdent"
let _semanticUIdentName = nameSym "semanticUIdent"
let _semanticNtName = nameSym "semanticNt"
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
let _lexerIntName = nameSym "IntTok"
let _lexerFloatName = nameSym "FloatTok"
let _lexerOperatorName = nameSym "OperatorTok"
let _lexerStringName = nameSym "StringTok"
let _lexerCharName = nameSym "CharTok"
let _lexerHashStringName = nameSym "HashStringTok"
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
    , _semanticIntName
    , _semanticFloatName
    , _semanticOperatorName
    , _semanticStringName
    , _semanticCharName
    , _semanticHashStringName
    , _semanticLitName
    , _semanticLIdentName
    , _semanticUIdentName
    , _semanticNtName
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
    , _lexerIntName
    , _lexerFloatName
    , _lexerOperatorName
    , _lexerStringName
    , _lexerCharName
    , _lexerHashStringName
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
let _semanticInt_ = nvar_ _semanticIntName
let _semanticFloat_ = nvar_ _semanticFloatName
let _semanticOperator_ = nvar_ _semanticOperatorName
let _semanticString_ = nvar_ _semanticStringName
let _semanticChar_ = nvar_ _semanticCharName
let _semanticHashString_ = app_ (nvar_ _semanticHashStringName)
let _semanticLit_ = app_ (nvar_ _semanticLitName)
let _semanticLIdent_ = nvar_ _semanticLIdentName
let _semanticUIdent_ = nvar_ _semanticUIdentName
let _semanticNt_ = app_ (nvar_ _semanticNtName)
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

let _stageSymbol = lam sym.
  match sym with GeneratorInt _ then
    Some _semanticInt_
  else match sym with GeneratorFloat _ then
    Some _semanticFloat_
  else match sym with GeneratorOperator _ then
    Some _semanticOperator_
  else match sym with GeneratorString _ then
    Some _semanticString_
  else match sym with GeneratorChar _ then
    Some _semanticChar_
  else match sym with GeneratorHashString {tag = tag} then
    Some (_semanticHashString_ (str_ tag))
  else match sym with GeneratorLit {lit = lit} then
    Some (_semanticLit_ (str_ lit))
  else match sym with GeneratorLIdent _ then
    Some _semanticLIdent_
  else match sym with GeneratorUIdent _ then
    Some _semanticUIdent_
  else match sym with GeneratorNonSyntax _ then
    None ()
  else match sym with GeneratorNt {nt = nt} then
    Some (_semanticNt_ (var_ nt))
  else dprintLn sym; never

let _stageInclude = lam inc.
  match inc with DefaultIn _ then _semanticDefaultIn_ else
  match inc with DefaultNotIn _ then _semanticDefaultNotIn_ else
  never

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
          match sym with GeneratorInt {field = Some name} then
            Some (name, untargetableType tyint_) else
          match sym with GeneratorFloat {field = Some name} then
            Some (name, untargetableType tyfloat_) else
          match sym with GeneratorOperator {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorString {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorChar {field = Some name} then
            Some (name, untargetableType tychar_) else
          match sym with GeneratorHashString {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorLit _ then
            None () else
          match sym with GeneratorLIdent {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorUIdent {field = Some name} then
            Some (name, untargetableType tystr_) else
          match sym with GeneratorNonSyntax {field = name, fieldType = ty} then
            Some (name, ty) else
          match sym with GeneratorNt {field = Some name, nt = nt} then
            Some (name, targetableType (tyvar_ nt))
          else None ()
      in
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
        let stagedProdType =
          match prodType with GeneratorAtom {self = self} then
            _semanticAtom_ (record_ [("self", _stageInclude self)])
          else match prodType with GeneratorPrefix {self = self, right = right} then
            _semanticPrefix_ (record_ [("self", _stageInclude self), ("right", _stageInclude right)])
          else match prodType with GeneratorInfix {self = self, left = left, right = right} then
            _semanticInfix_ (record_ [("self", _stageInclude self), ("left", _stageInclude left), ("right", _stageInclude right)])
          else match prodType with GeneratorPostfix {self = self, left = left} then
            _semanticPostfix_ (record_ [("self", _stageInclude self), ("left", _stageInclude left)])
          else never in
        let stageField = lam sym.
          let simpleResult = lam field. lam conName.
            let valName = nameSym field in
            ( Some (npcon_ _ll1TokName (npcon_ conName (prec_ [("val", npvar_ valName)])))
            , Some (field, nvar_ valName)
            ) in
          match sym with GeneratorInt {field = Some field} then
            simpleResult field _lexerIntName
          else match sym with GeneratorFloat {field = Some field} then
            simpleResult field _lexerFloatName
          else match sym with GeneratorOperator {field = Some field} then
            simpleResult field _lexerOperatorName
          else match sym with GeneratorString {field = Some field} then
            simpleResult field _lexerStringName
          else match sym with GeneratorChar {field = Some field} then
            simpleResult field _lexerCharName
          else match sym with GeneratorHashString {field = Some field} then
            simpleResult field _lexerHashStringName
          else match sym with GeneratorLIdent {field = Some field} then
            simpleResult field _lexerLIdentName
          else match sym with GeneratorUIdent {field = Some field} then
            simpleResult field _lexerUIdentName
          else match sym with GeneratorNonSyntax {field = field, fieldValue = val} then
            ( None ()
            , Some (field, val)
            )
          else match sym with GeneratorNt {field = Some field} then
            let valName = nameSym field in
            ( Some (npcon_ _ll1UserSymName (ptuple_ [pvarw_, npvar_ valName]))
            , Some (field, nvar_ valName)
            )
          else (Some pvarw_, None ()) in
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
          , ("rhs" , seq_ (mapOption _stageSymbol syntax))
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
  = lam spec.
    match spec with
      { nonTerminal = nonTerminal
      , leftBracket = leftBracket
      , rightBracket = rightBracket
      }
    then
      let sym = gensym () in

      let stagedSpec =
        let allSymbols = join
          [ leftBracket
          , [GeneratorNt {field = None (), nt = nonTerminal}]
          , rightBracket
          ] in
        let stagedAction =
          let infoName = nameSym "info" in
          let paramName = nameSym "syms" in
          let valName = nameSym "val" in
          nulam_ paramName
            (_nulet_ infoName (_symSeqInfo_ (nvar_ paramName))
              (tuple_
                [ nvar_ infoName
                , match_ (get_ (nvar_ paramName) (int_ (length leftBracket)))
                  (npcon_ _ll1UserSymName (ptuple_ [pvarw_, npvar_ valName]))
                  (nvar_ valName)
                  never_
                ]))
        in
        record_
          [ ("name", str_ (concat "grouping " nonTerminal))
          , ("nt", var_ nonTerminal)
          , ("ptype", _semanticAtom_ (record_ [("self", _stageInclude (DefaultIn ()))]))
          , ("rhs", seq_ (mapOption _stageSymbol allSymbols))
          , ("action", stagedAction)
          ]
      in

      { constructor = None ()
      , sym = sym
      , stagedSpec = stagedSpec
      , nonTerminal = nonTerminal
      }
    else never

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
          , let res =
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
                    never_)))
            in (pprintCode 2 _env res).1
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

let generatorNamespace =
  -- Grammar construction and code generation
  let prod = generatorProd in
  let bracket = generatorBracket in
  let grammar = generatorGrammar in

  -- Production types
  let defAtom = GeneratorAtom
    { self = DefaultIn ()
    } in
  let defPrefix = lam rname. GeneratorPrefix
    { self = DefaultIn (), right = DefaultIn ()
    , rightField = Some rname
    } in
  let defInfix = lam lname. lam rname. GeneratorInfix
    { self = DefaultIn (), left = DefaultIn (), right = DefaultIn ()
    , leftField = Some lname, rightField = Some rname
    } in
  let defPostfix = lam lname. GeneratorPostfix
    { self = DefaultIn (), left = DefaultIn ()
    , leftField = Some lname
    } in

  -- Precedence helpers
  let groupLeft = semanticGroupLeft in
  let groupRight = semanticGroupRight in
  let groupEither = semanticGroupEither in
  let groupNeither = semanticGroupNeither in
  let highLowPrec = semanticHighLowPrec in
  let precTableNoEq = semanticPrecTableNoEq in
  let leftAssoc = semanticLeftAssoc in
  let rightAssoc = semanticRightAssoc in
  let nonAssoc = semanticNonAssoc in
  let ambAssoc = semanticAmbAssoc in
  let pairwiseGroup = semanticPairwiseGroup in

  -- Token symbols
  let int = lam field. GeneratorInt {field = Some field} in
  let int_ = GeneratorInt {field = None ()} in
  let float = lam field. GeneratorFloat {field = Some field} in
  let float_ = GeneratorFloat {field = None ()} in
  let operator = lam field. GeneratorOperator {field = Some field} in
  let operator_ = GeneratorOperator {field = None ()} in
  let string = lam field. GeneratorString {field = Some field} in
  let string_ = GeneratorString {field = None ()} in
  let char = lam field. GeneratorChar {field = Some field} in
  let char_ = GeneratorChar {field = None ()} in
  let hashString = lam field. lam tag. GeneratorHashString {field = Some field, tag = tag} in
  let hashString_ = lam tag. GeneratorHashString {field = None (), tag = tag} in
  let lit_ = lam lit. GeneratorLit {lit = lit} in
  let lident = lam field. GeneratorLIdent {field = Some field} in
  let lident_ = GeneratorLIdent {field = None ()} in
  let uident = lam field. GeneratorUIdent {field = Some field} in
  let uident_ = GeneratorUIdent {field = None ()} in
  let nonsyntax = lam field. lam fieldType. lam fieldValue. GeneratorNonSyntax {field = field, fieldType = fieldType, fieldValue = fieldValue} in
  let nt = lam field. lam nt. GeneratorNt {field = Some field, nt = nt} in
  let nt_ = lam nt. GeneratorNt {field = None (), nt = nt} in

  -- Namespace as a record
  { prod = prod, bracket = bracket, grammar = grammar
  , defAtom = defAtom, defPrefix = defPrefix, defInfix = defInfix, defPostfix = defPostfix
  , groupLeft = groupLeft, groupRight = groupRight, groupEither = groupEither
  , groupNeither = groupNeither, highLowPrec = highLowPrec, precTableNoEq = precTableNoEq
  , leftAssoc = leftAssoc, rightAssoc = rightAssoc, nonAssoc = nonAssoc, ambAssoc = ambAssoc
  , pairwiseGroup = pairwiseGroup
  , int = int, int_ = int_, float = float, float_ = float_
  , operator = operator , operator_ = operator_, string = string, string_ = string_
  , char = char, char_ = char_ , hashString = hashString, hashString_ = hashString_
  , lit_ = lit_, lident = lident , lident_ = lident_, uident = uident, uident_ = uident_
  , nonsyntax = nonsyntax , nt = nt, nt_ = nt_
  }

mexpr

let g = generatorNamespace in

let unknownTyP = g.prod
  { nonTerminal = "Type"
  , constructorName = "TyUnknown"
  , prodType = g.defAtom
  , syntax = [g.lit_ "Unknown"]
  } in

-- TODO(vipa, 2021-03-16): This is ugly, the result from g.prod should
-- be opaque, but we need the precise name the constructor will use to
-- get it to pretty print correctly. There should be a better way to
-- solve it later (more or less running symbolize before printing),
-- but not at present.
match unknownTyP with {constructor = Some {name = unknownTyConstructorName}} then
let tyField = g.nonsyntax "ty" (untargetableType (tyvar_ "Type")) (nconapp_ unknownTyConstructorName unit_) in

let varP = g.prod
  { constructorName = "TmVar"
  , nonTerminal = "Expr"
  , prodType = g.defAtom
  , syntax = [g.lident "ident", tyField]
  } in

let appP = g.prod
  { constructorName = "TmApp"
  , nonTerminal = "Expr"
  , prodType = g.defInfix "f" "a"
  , syntax = [tyField]
  } in

let groupingP = g.bracket
  { nonTerminal = "Expr"
  , leftBracket = [g.lit_ "("]
  , rightBracket = [g.lit_ ")"]
  } in

let ifP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmIfBroken"
  , prodType = g.defPrefix "thenExpr"
  , syntax = [g.lit_ "if", g.nt "condition" "Expr", g.lit_ "then", tyField]
  } in

let elseP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmElseBroken"
  , prodType = GeneratorInfix
    { self = DefaultIn ()
    , left = DefaultNotIn ()
    , right = DefaultIn ()
    , leftField = Some "ifExpr"
    , rightField = Some "elseExpr"
    }
  , syntax = [g.lit_ "else", tyField]
  } in

let matchP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmMatch"
  , prodType = GeneratorAtom {self = DefaultNotIn ()}
  , syntax =
    [ g.lit_ "match", g.nt "target" "Expr", g.lit_ "with"
    , g.nonsyntax "arms"
      (seqType
        (tupleType
          [ targetableType (tyvar_ "Pat")
          , targetableType (tyvar_ "Expr")
          ]))
      (seq_ [])
    , tyField]
  } in

let matchArmP = g.prod
  { nonTerminal = "Expr"
  , constructorName = "TmMatchArmBroken"
  , prodType = GeneratorInfix
    { self = DefaultIn ()
    , left = DefaultNotIn ()
    , right = DefaultIn ()
    , leftField = Some "prev"
    , rightField = Some "armExpr"
    }
  , syntax = [g.lit_ "|", g.nt "pat" "Pat", g.lit_ "->", tyField]
  } in

let intPatP = g.prod
  { nonTerminal = "Pat"
  , constructorName = "PatInt"
  , prodType = g.defAtom
  , syntax = [g.int "val", tyField]
  } in

let res = g.grammar
  { langName = "MExpr"
  , start = "Expr"
  , productions = [varP, appP, groupingP, ifP, elseP, matchP, matchArmP, intPatP, unknownTyP]
  , overrideAllow =
    [ GeneratorLeftChild {parent = elseP, child = ifP}
    , GeneratorLeftChild {parent = matchArmP, child = matchP}
    , GeneratorLeftChild {parent = matchArmP, child = matchArmP}
    ]
  , overrideDisallow = []
  , precedences = join
    [ map g.leftAssoc [appP]
    , g.precTableNoEq
      [ [appP]
      , [ifP]
      ]
    -- NOTE(vipa, 2021-03-16): These stem from if and match having
    -- lower precedence than the things to the right, but they can't
    -- be specified in the normal way because it should only apply to
    -- their right children
    , seqLiftA2 g.groupRight [elseP, matchArmP] [appP]
    -- NOTE(vipa, 2021-03-16): Precedence with things to the left have
    -- to be treated as ambiguous (groupEither) to allow them to float
    -- to the appropriate thing they must attach to (ifP, matchP,
    -- matchArmP)
    , seqLiftA2 g.groupEither [appP, ifP, elseP, matchArmP] [elseP, matchArmP]
    ]
  , sfunctions =
    [ ("Expr", "Expr")
    , ("Expr", "Type")
    , ("Expr", "Pat")
    , ("Pat", "Pat")
    , ("Pat", "Type")
    , ("Type", "Type")
    ]
  } in

-- printLn res;

()

else never
