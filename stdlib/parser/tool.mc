include "selfhost-gen.mc"
include "gen-ast.mc"
include "gen-op-ast.mc"
include "math.mc"
include "result.mc"
include "seq.mc"
include "mexpr/cmp.mc"
include "mexpr/boot-parser.mc"
include "mlang/pprint.mc"

type Res a = Result (Info, String) (Info, String) a

-- NOTE(vipa, 2022-04-05): A token type only ever intended for
-- analysis, thus only containing a TokenRepr, no Token. This is used
-- for all tokens declared with the `token` declaration.
lang PreToken = TokenParser
  syn Token =
  syn TokenRepr =
  | PreRepr {constructorName : Name}

  sem tokReprToStr =
  | PreRepr x -> join ["<", nameGetStr x.constructorName, ">"]

  sem tokReprCmp2 =
  | (PreRepr l, PreRepr r) -> nameCmp l.constructorName r.constructorName
end

-- NOTE(vipa, 2022-04-25): Similar to PreToken, these are only
-- intended for analysis. We cannot use normal LitSpec constructed
-- through `litSym` since it will check that the literal lexes as a
-- single token, which it only would if we have the appropriate
-- language fragments included, which we don't have in the
-- *generating* code, we only have that in the *generated* code.
lang PreLitToken = TokenParser
  syn TokenRepr =
  | PreLitRepr {lit : String}

  sem tokReprToStr =
  | PreLitRepr x -> snoc (cons '\'' x.lit) '\''

  sem tokReprCmp2 =
  | (PreLitRepr l, PreLitRepr r) -> cmpString l.lit r.lit
end

lang LL1Analysis = ParserGeneration + PreToken + PreLitToken
end

lang Fragments = LL1Analysis + MExprCmp + MExprPrettyPrint + CarriedBasic + MExprEq
end

let runParserGenerator : {synFile : String, outFile : String} -> () = lam args.
  use Fragments in
  use SelfhostAst in

  type MExpr = use Ast in Expr in
  type MType = use Ast in Type in
  type MDecl = use DeclAst in Decl in

  type TypeInfo =
    { ty : Type
    , ensureSuffix : Bool
    , commonFields : Map String (MType, MExpr)
    , grouping : Option ({v: Either Name String, i: Info}, {v: Either Name String, i: Info})
    } in
  type TokenInfo =
    { ty : MType
    , repr : MExpr
    , tokConstructor : Name
    , getInfo : MExpr -> MExpr
    , getValue : MExpr -> MExpr
    } in

  type Terminal in
  con NtTerm : {config : Res TypeInfo, name : Name} -> Terminal in
  con TokenTerm : Res TokenInfo -> Terminal in
  con LitTerm : String -> Terminal in
  type SRegex in
  con TerminalReg : {term: Terminal, info: Info, field: Option (Info, String)} -> SRegex in
  con RecordReg : {content: [SRegex], info: Info, field: Option (Info, String)} -> SRegex in
  con KleeneReg : {content: {v: [SRegex], i: Info}, info: Info} -> SRegex in
  con AltReg : {alts: [{v: [SRegex], i: Info}]} -> SRegex in
  type Operator =
    { lfield : Option String
    , rfield : Option String
    , mid : [SRegex]
    , nt : Name
    , definition : {v: Name, i: Info}
    , names :
      { prodCon : Name
      , prodLang : Name
      , opCon : Name
      }
    , assoc : Assoc
    } in

  type LabelRegexKind in
  con LRegAtom : () -> LabelRegexKind in
  con LRegInfix : () -> LabelRegexKind in
  con LRegPrefix : () -> LabelRegexKind in
  con LRegPostfix : () -> LabelRegexKind in
  con LRegEnd : () -> LabelRegexKind in
  type GenLabel in
  con TyTop : {v: Name, i: Info} -> GenLabel in
  con TyRegex : {nt: {v: Name, i: Info}, kind: LabelRegexKind} -> GenLabel in
  con TyGrouping : {left: Info, right: Info} -> GenLabel in
  con ProdTop : {v: Name, i: Info} -> GenLabel in
  con ProdInternal : {name: {v: Name, i: Info}, info: Info} -> GenLabel in

  let asDyn_ : use Ast in MExpr -> MExpr = app_ (var_ "asDyn") in
  let fromDyn_ : use Ast in MExpr -> MExpr = app_ (var_ "fromDyn") in

  let filename = args.synFile in
  let destinationFile = args.outFile in
  let content = readFile filename in
  match parseSelfhostExn filename content with LangFile {decls = decls, name = {v = langName}} in

  let simpleHighlight
    : Info -> String
    = lam info.
      formatHighlights terminalHighlightErrorConfig content [Relevant info]
  in
  let multiHighlight
    : Info -> [Info] -> String
    = lam surround. lam infos.
      let ranges = map (lam x. Relevant x) infos in
      let ranges =
        match surround with Info x then
          let first = infoVal x.filename x.row1 x.col1 x.row1 x.col1 in
          let last = infoVal x.filename x.row2 x.col2 x.row2 x.col2 in
          snoc (cons (Irrelevant first) ranges) (Irrelevant last)
        else ranges in
      formatHighlights terminalHighlightErrorConfig content ranges
  in
  let simpleMsg
    : Info -> String -> (Info, String)
    = lam info. lam msg.
      (info, join [msg, simpleHighlight info, "\n"])
  in
  let multiMsg
    : Info -> [Info] -> String -> (Info, String)
    = lam surround. lam infos. lam msg.
      (surround, join [msg, multiHighlight surround infos])
  in

  -- NOTE(vipa, 2022-04-21): The `Expr` type defined in the `.syn`
  -- format is similar to, but not precisely like, MExpr, and thus it
  -- needs a bit of conversion to create proper MExpr code (though most
  -- of it is just switching from XExpr to TmX).
  recursive let exprToMExpr
    : Expr -> Res MExpr
    = lam e. switch e
      case AppExpr (x & {left = ConExpr c}) then
        result.map
          (lam r. TmConApp
            { ident = c.name.v
            , body = r
            , ty = tyunknown_
            , info = x.info
            })
          (exprToMExpr x.right)
      case AppExpr x then
        result.map2
          (lam l. lam r. TmApp
            { lhs = l
            , rhs = r
            , ty = tyunknown_
            , info = x.info
            })
          (exprToMExpr x.left)
          (exprToMExpr x.right)
      case ConExpr x then
        result.err (simpleMsg x.info "A constructor must be applied to an argument.")
      case StringExpr x then
        result.ok (withInfo x.info (str_ x.val.v))
      case VariableExpr x then
        result.ok (TmVar
          { ident = x.name.v
          , ty = tyunknown_
          , info = x.info
          , frozen = false
          })
      case RecordExpr x then
        let f : {name : {v: String, i: Info}, val: Expr} -> Res (String, MExpr) = lam field.
          result.map (lam e. (field.name.v, e)) (exprToMExpr field.val) in
        result.map (lam pairs. withInfo x.info (urecord_ pairs)) (result.mapM f x.fields)
      end
  in

  -- NOTE(vipa, 2022-04-21): The `Expr` type is also designed to overlap
  -- syntactically as much as possible with `Type` in MExpr, so a
  -- similar approach to exprToMExpr is needed for conversion.
  recursive let exprToMExprTy
    : Expr -> Res MType
    = lam e. switch e
      case AppExpr x then
        result.map2
          (lam l. lam r. TyApp
            { lhs = l
            , rhs = r
            , info = x.info
            })
          (exprToMExprTy x.left)
          (exprToMExprTy x.right)
      case ConExpr x then
        result.ok (TyCon
          { ident = x.name.v
          , info = x.info
          , data = tyunknown_
          })
      case VariableExpr x then
        result.ok (TyVar
          { ident = x.name.v
          , info = x.info
          })
      case RecordExpr (x & {fields = []}) then
        result.ok (tyWithInfo x.info tyunit_)
      case RecordExpr x then
        result.err (simpleMsg x.info "Non-unit record types are not yet supported.")
      end
  in

  let decls : [Decl] =
    let makeNamedRegex : Info -> {v: Name, i: Info} -> String -> Regex = lam info. lam synName. lam field.
      NamedRegex
        { name = {v = field, i = info}
        , right = TokenRegex {name = synName, info = info, arg = None ()}
        , info = info
        } in
    let desugarProds = lam d.
      match d with ProductionDecl x then
        let regexInfo = get_Regex_info x.regex in
        let regex = x.regex in
        let regex = match (x.kinf, x.kpostf) with (Some info, _) | (_, Some info)
          then ConcatRegex {info = regexInfo, left = makeNamedRegex info x.nt "left", right = regex}
          else regex in
        let regex = match (x.kinf, x.kpref) with (Some info, _) | (_, Some info)
          then ConcatRegex {info = regexInfo, left = regex, right = makeNamedRegex info x.nt "right"}
          else regex in
        ProductionDecl {x with regex = regex}
      else d in
    map desugarProds decls
  in

  let includes : [IncludeDeclRecord] = mapOption
    (lam x. match x with IncludeDecl x then Some x else None ())
    decls
  in

  -- NOTE(vipa, 2022-03-18): Find all definitions in the file
  type PreNameEnv = {types : Map String [(Info, Name)], productions : Map String [(Info, Name)]} in
  let pullDefinition
    : PreNameEnv -> Decl -> PreNameEnv
    = lam env. lam decl.
      switch decl
      case TypeDecl x then
        {env with types = mapInsertWith concat (nameGetStr x.name.v) [(x.name.i, nameSetNewSym x.name.v)] env.types}
      case ProductionDecl x then
        {env with productions = mapInsertWith concat (nameGetStr x.name.v) [(x.name.i, nameSetNewSym x.name.v)] env.productions}
      case TokenDecl {name = Some n} then
        let n : {v : Name, i : Info} = n in
        {env with types = mapInsertWith concat (nameGetStr n.v) [(n.i, nameSetNewSym n.v)] env.types}
      case _ then
        env
      end
  in
  let nameEnv: PreNameEnv = foldl pullDefinition {types = mapEmpty cmpString, productions = mapEmpty cmpString} decls in

  -- NOTE(vipa, 2022-03-18): Create errors for things defined multiple times
  let mkMultiDefError
    : [(Info, Name)] -> Res Name
    = lam defs.
      switch defs
      case [(_, name)] then result.ok name
      case everything & ([(info, name)] ++ _) then
        let highlights = map
          (lam x. match x with (info, _) in join ["  ", info2str info, simpleHighlight info, "\n"])
          everything in
        let msg = join
          [ nameGetStr name, " has multiple definitions:\n"
          , join highlights
          ] in
        result.err (info, msg)
      end
  in
  type NameEnv = {types : Map String (Res Name), productions : Map String (Res Name)} in
  let nameEnv: NameEnv =
    { types = mapMap mkMultiDefError nameEnv.types
    , productions = mapMap mkMultiDefError nameEnv.productions
    } in
  let lookupName
    : {v: Name, i: Info} -> Map String (Res Name) -> Res {v: Name, i: Info}
    = lam name. lam map.
      let mkUnboundError = lam.
        result.err (simpleMsg name.i (concat (nameGetStr name.v) " is unbound.\n")) in
      let res = mapFindOrElse mkUnboundError (nameGetStr name.v) map in
      result.map (lam v. {name with v = v}) res
  in

  let typeMap : Ref (Map Name (Either (Res TypeInfo) (Res TokenInfo))) = ref (mapEmpty nameCmp) in
  let fragments : Ref [Res Name] = ref [] in

  -- NOTE(vipa, 2022-03-18): Do name resolution in all declarations
  -- NOTE(vipa, 2022-03-21): This does not do name resolution inside
  -- expressions in regexes. Presumably I should call out to
  -- symbolize.mc, but I'll postpone that until later
  recursive let resolveRegex
    : Regex -> Res Regex
    = lam reg.
      let smapM : (Regex -> Res Regex) -> Regex -> Res Regex = lam f. lam reg.
        let inner = lam annot. lam here.
          let res = f here in
          let here = match result.consume res with (_, Right x) then x else here in
          (result.withAnnotations res annot, here) in
        match smapAccumL_Regex_Regex inner (result.ok ()) reg with (annot, res) in
        result.withAnnotations annot (result.ok res)
      in
      switch reg
      case TokenRegex x then
        result.map
          (lam name. TokenRegex {x with name = name})
          (lookupName x.name nameEnv.types)
      case other then
        smapM resolveRegex other
      end
  in
  -- NOTE(vipa, 2022-04-21): Take a property in a property mass and
  -- extract the single definition, if possible.
  let getSingleDef : all a. Info -> String -> [(Info, Res a)] -> Res (Option (Info, a)) = lam surround. lam prop. lam defs.
    let multi =
      match defs with [_, _] ++ _ then
        let infos = (map (lam x. match x with (x, _) in x) defs) in
        let msg = join ["Multiple definitions of '", prop, "'"] in
        result.err (multiMsg surround infos msg)
      else result.ok () in
    let defs = result.mapM (lam x. match x with (info, x) in result.map (lam x. (info, x)) x) defs in
    let defs = result.map (lam x. match x with [x] ++ _ then Some x else None ()) defs in
    result.withAnnotations multi defs
  in
  type TokenDeclDesugaredRecord =
    { repr : Option (Info, MExpr)
    , constructor : Option (Info, {v: Name, i: Info})
    , fragment : Option (Info, {v: String, i: Info})
    , ty : Option (Info, MType)
    , base : Option (Info, {v: Name, i: Info})
    , wrap : Option (Info, MExpr)
    } in
  type TokenDeclPropertyMass =
    { repr : [(Info, Res MExpr)]
    , constructor : [(Info, Res {v: Name, i: Info})]
    , fragment : [(Info, Res {v: String, i: Info})]
    , ty : [(Info, Res MType)]
    , base : [(Info, Res {v: Name, i: Info})]
    , wrap : [(Info, Res MExpr)]
    , unknown : [Info]
    } in
  let emptyTokenDeclPropertyMass : TokenDeclPropertyMass =
    { repr = []
    , constructor = []
    , fragment = []
    , ty = []
    , base = []
    , wrap = []
    , unknown = []
    } in
  let mergeTokenDeclPropertyMass
    : TokenDeclPropertyMass -> TokenDeclPropertyMass -> TokenDeclPropertyMass
    = lam a. lam b.
      { repr = concat a.repr b.repr
      , constructor = concat a.constructor b.constructor
      , fragment = concat a.fragment b.fragment
      , ty = concat a.ty b.ty
      , base = concat a.base b.base
      , wrap = concat a.wrap b.wrap
      , unknown = concat a.unknown b.unknown
      } in
  let resolveTokenProperty
    : {name: {v: String, i: Info}, val: Expr} -> TokenDeclPropertyMass
    = lam prop.
      let field = prop.name in
      let value = prop.val in
      switch field.v
      case "repr" then {emptyTokenDeclPropertyMass with repr = [(field.i, exprToMExpr value)]}
      case "constructor" then
        let res = match value with ConExpr x
          then result.ok x.name
          else result.err (simpleMsg (get_Expr_info value) "The constructor must be a single constructor name.")
        in {emptyTokenDeclPropertyMass with constructor = [(field.i, res)]}
      case "fragment" then
        let res = match value with ConExpr x
          then result.ok {v = nameGetStr x.name.v, i = x.name.i}
          else result.err (simpleMsg (get_Expr_info value) "The language fragment must be a single fragment name.")
        in {emptyTokenDeclPropertyMass with fragment = [(field.i, res)]}
      case "ty" then {emptyTokenDeclPropertyMass with ty = [(field.i, exprToMExprTy value)]}
      case "base" then
        let res = match value with ConExpr x
          then result.ok x.name
          else result.err (simpleMsg (get_Expr_info value) "The base token must be a single token name.")
        in {emptyTokenDeclPropertyMass with base = [(field.i, res)]}
      case "wrap" then {emptyTokenDeclPropertyMass with wrap = [(field.i, exprToMExpr value)]}
      case _ then
        {emptyTokenDeclPropertyMass with unknown = [field.i]}
      end
  in
  let desugarAndResolveTokenDecl
    : TokenDeclRecord -> Res TokenDeclDesugaredRecord
    = lam x.
      let mass: TokenDeclPropertyMass = foldl mergeTokenDeclPropertyMass emptyTokenDeclPropertyMass
        (map resolveTokenProperty x.properties) in
      let unknownError = match mass.unknown with [] then result.ok () else
        let msg = match mass.unknown with [_] then "Unknown property:\n" else "Unknown properties:\n" in
        result.err (multiMsg x.info mass.unknown msg) in
      let repr = getSingleDef x.info "repr" mass.repr in
      let constructor = getSingleDef x.info "constructor" mass.constructor in
      let fragment = getSingleDef x.info "fragment" mass.fragment in
      let ty = getSingleDef x.info "ty" mass.ty in
      let base = getSingleDef x.info "base" mass.base in
      let wrap = getSingleDef x.info "wrap" mass.wrap in
      result.withAnnotations
        unknownError
        (result.apply
          (result.map5
            (lam repr. lam constructor. lam fragment. lam ty. lam base. lam wrap.
              { repr = repr
              , constructor = constructor
              , fragment = fragment
              , ty = ty
              , base = base
              , wrap = wrap
              })
            repr constructor fragment ty base)
            wrap)
  in
  let desugaredTokenToTokenInfo
    : Info -> Option {v: Name, i: Info} -> TokenDeclDesugaredRecord -> (Option (Res String), Option (Res TokenInfo))
    = lam surround. lam name. lam record.
      -- TODO(vipa, 2022-04-21): It would be nice to warn about unused
      -- properties, but it's annoying to implement atm
      let frag = match record.fragment with Some (_, str)
        then let str: {v: String, i: Info} = str in Some (result.ok str.v)
        else None () in
      match name with Some name then
        let name: {v: Name, i: Info} = name in
        let wrap: all a. (a -> MExpr) -> a -> MExpr = match record.wrap with Some (_, f)
          then lam inner. lam e. app_ f (inner e)
          else lam f. f in
        switch (record.repr, record.constructor, record.base)
        case (Some (_, repr), Some (_, constructor), None ()) then
          let constructor: {v: Name, i: Info} = constructor in
          let tinfo =
            { ty = match record.ty with Some (_, ty)
              then ty
              else tyWithInfo name.i (ntycon_ name.v)
            , repr = repr
            , tokConstructor = constructor.v
            , getInfo = recordproj_ "info"
            -- TODO(vipa, 2022-04-21): Provide a more principled way to extract `info` and `val`
            , getValue = wrap (recordproj_ "val")
            } in
          (frag, Some (result.ok tinfo))
        case (None (), None (), Some (_, base)) then
          let base: {v: Name, i: Info} = base in
          let base: Res {v: Name, i: Info} = lookupName base nameEnv.types in
          let f: {v: Name, i: Info} -> Res TokenInfo = lam name.
            match mapLookup name.v (deref typeMap) with Some tinfo then
              match tinfo with Right tinfo then
                result.map
                  (lam tinfo: TokenInfo.
                    {{tinfo
                       with ty = match record.ty with Some (_, ty) then ty else tinfo.ty}
                       with getValue = wrap tinfo.getValue})
                  tinfo
              else result.err (simpleMsg name.i "This name refers to a type; it must be a token.\n")
            else result.err (simpleMsg name.i "The base token must be defined earlier in the file.\n")
          in (frag, Some (result.bind base f))
        case _ then
          (frag, Some (result.err (simpleMsg surround "A named token declaration must have both 'repr' and 'constructor', or 'base'.\n")))
        end
      else match record.fragment with Some _ then
        (frag, None ())
      else
        let fragErr = (result.err (simpleMsg surround "A token declaration without a name must have a 'fragment' property.\n")) in
        (Some fragErr, None ())
  in
  type TypeDeclDesugaredRecord =
    { grouping : Option (Info, ({v: Either Name String, i: Info}, {v: Either Name String, i: Info}))
    } in
  type TypeDeclPropertyMass =
    { grouping : [(Info, Res ({v: Either Name String, i: Info}, {v: Either Name String, i: Info}))]
    , unknown : [Info]
    } in
  let emptyTypeDeclPropertyMass =
    { grouping = [], unknown = [] } in
  let mergeTypeDeclPropertyMass
    : TypeDeclPropertyMass -> TypeDeclPropertyMass -> TypeDeclPropertyMass
    = lam l. lam r.
      { grouping = concat l.grouping r.grouping
      , unknown = concat l.unknown r.unknown
      } in
  let resolveTypeProperty
    : {name: {v: String, i: Info}, val: Expr} -> TypeDeclPropertyMass
    = lam prop.
      let field = prop.name in
      let value = prop.val in
      switch field.v
      case "grouping" then
        let mkParen : Expr -> Res {v: Either Name String, i: Info} = lam e. switch e
          case ConExpr c then
            result.map
              (lam name. {v = Left name.v, i = c.name.i})
              (lookupName c.name nameEnv.types)
          case StringExpr s then
            result.ok {v = Right s.val.v, i = s.val.i}
          case e then
            result.err (simpleMsg (get_Expr_info e) "Expected a string literal or token name.")
          end in
        let res = match value with AppExpr x
          then result.map2 (lam a. lam b. (a, b)) (mkParen x.left) (mkParen x.right)
          else result.err (simpleMsg (get_Expr_info value) "Grouping must be two tokens (string literals or token names).")
        in {emptyTypeDeclPropertyMass with grouping = [(field.i, res)]}
      case _ then
        {emptyTypeDeclPropertyMass with unknown = [field.i]}
      end
  in
  let desugarAndResolveTypeDecl
    : TypeDeclRecord -> Res TypeDeclDesugaredRecord
    = lam x.
      let mass: TypeDeclPropertyMass = foldl mergeTypeDeclPropertyMass emptyTypeDeclPropertyMass
        (map resolveTypeProperty x.properties) in
      let unknownError = match mass.unknown with [] then result.ok () else
        let msg = match mass.unknown with [_] then "Unknown property:\n" else "Unknown properties:\n" in
        result.err (multiMsg x.info mass.unknown msg) in
      let grouping = getSingleDef x.info "grouping" mass.grouping in
      result.withAnnotations
        unknownError
        (result.map
          (lam grouping.
            { grouping = grouping
            })
          grouping)
  in
  let resolveDecl
    : Decl -> Res Decl
    = lam decl.
      switch decl
      case TypeDecl x then
        let name = lookupName x.name nameEnv.types in
        let record = desugarAndResolveTypeDecl x in
        let f = lam name: {v: Name, i: Info}. lam x: TypeDeclDesugaredRecord.
          { ty = ntycon_ name.v
          , ensureSuffix = true
          , commonFields = mapEmpty cmpString
          , grouping = optionMap (lam x. match x with (_, x) in x) x.grouping
          }
          in
        (match result.toOption name with Some name then
          let name: {v: Name, i: Info} = name in
          modref typeMap (mapInsert name.v (Left (result.map (f name) record)) (deref typeMap))
         else ()
        );
        result.withAnnotations
          record
          (result.map (lam name. TypeDecl {x with name = name}) name)
      case TokenDecl x then
        let name = match x.name with Some name
          then result.map (lam x. Some x) (lookupName name nameEnv.types)
          else result.ok (None ()) in
        let record = desugarAndResolveTokenDecl x in
        let tinfo = result.map2 (desugaredTokenToTokenInfo x.info) name record in
        (match result.toOption name with Some (Some name) then
          let name: {v: Name, i: Info} = name in
          let tinfo = result.bind tinfo (lam x. match x with (_, Some tinfo) in tinfo) in
          modref typeMap (mapInsert name.v (Right tinfo) (deref typeMap))
         else ());
        result.map
          (lam x. match x with (Some frag, _) then
              modref fragments (snoc (deref fragments) (result.map nameNoSym frag))
             else ())
          tinfo;
        result.map
          (lam name. TokenDecl {x with name = name})
          name
      case StartDecl x then
        result.map
          (lam name. StartDecl {x with name = name})
          (lookupName x.name nameEnv.types)
      case PrecedenceTableDecl x then
        let resolveLevel = lam level: {noeq : Option Info, operators : [{v: Name, i: Info}]}.
          result.map
            (lam operators. {level with operators = operators})
            (result.mapM (lam n. lookupName n nameEnv.productions) level.operators) in
        let resolveException = lam exception: {lefts : [{v: Name, i: Info}], rights : [{v: Name, i: Info}]}.
          result.map2
            (lam lefts. lam rights. {{exception with lefts = lefts} with rights = rights})
            (result.mapM (lam n. lookupName n nameEnv.productions) exception.lefts)
            (result.mapM (lam n. lookupName n nameEnv.productions) exception.rights) in
        result.map2
          (lam levels. lam exceptions. PrecedenceTableDecl {{x with levels = levels} with exceptions = exceptions})
          (result.mapM resolveLevel x.levels)
          (result.mapM resolveException x.exceptions)
      case ProductionDecl x then
        result.map3
          (lam name. lam nt. lam regex. ProductionDecl {{{x with name = name} with nt = nt} with regex = regex})
          (lookupName x.name nameEnv.productions)
          (lookupName x.nt nameEnv.types)
          (resolveRegex x.regex)
      case decl then result.ok decl
      end
  in
  -- NOTE(vipa, 2022-03-22): We want to do as much analysis as possible,
  -- thus at this point we split the list in two: one sentinel value of
  -- type `Res ()` that is ok iff all declarations name resolve
  -- properly, and one list of only the declarations without binding
  -- errors
  let decls: [Res Decl] = map resolveDecl decls in
  let allResolved: Res () = result.map (lam. ()) (result.mapM identity decls) in
  let decls: [Decl] = mapOption result.toOption decls in
  let typeMap: Map Name (Either (Res TypeInfo) (Res TokenInfo)) = deref typeMap in

  -- NOTE(vipa, 2022-03-21): Compute the required sfunctions
  let ntsWithInfo: [{v: Name, i: Info}] =
    let inner = lam x. match x with TypeDecl x then Some x.name else None () in
    mapOption inner decls in
  let nts: [Name] =
    map (lam name: {v: Name, i: Info}. name.v) ntsWithInfo in
  let requestedSFunctions: [SFuncRequest] =
    let mkRequest = lam a. lam b.
      let suffix = join [nameGetStr a, "_", nameGetStr b] in
      { synName = a
      , target = ntycon_ b
      , names =
        { smapAccumL = nameSym (concat "smapAccumL_" suffix)
        , smap = nameSym (concat "smap_" suffix)
        , sfold = nameSym (concat "sfold_" suffix)
        }
      } in
    seqLiftA2 mkRequest nts nts in

  -- NOTE(vipa, 2022-03-22): Find the starting non-terminal
  let start: Res Name =
    let inner = lam x. match x with StartDecl x then Some (x.info, x.name.v) else None () in
    let starts: [(Info, Name)] = mapOption inner decls in
    switch starts
    case [(_, start)] then result.ok start
    case [] then result.err (infoVal filename 0 0 0 0, "Missing start symbol")
    case starts & ([(info, _)] ++ _) then
      let highlights = map
        (lam x. match x with (info, _) in join ["  ", info2str info, simpleHighlight info, "\n"])
        starts in
      let msg = join
        [ "Multiple start symbol definitions:\n"
        , join highlights
        ] in
      result.err (info, msg)
    end
  in

  let requestedFieldAccessors : Res [FieldAccessorRequest] =
    let surfaceTypeInfo = lam x. match x with (n, Left config) then Some (n, config) else None () in
    let buryName = lam x. match x with (n, config) in result.map (lam x. (n, x)) config in
    let tripleToRequest = lam trip.
      { synName = trip.0
      , field = trip.1
      , resTy = trip.2
      , names =
        let suffix = join ["_", nameGetStr trip.0, "_", trip.1] in
        { get = nameSym (concat "get" suffix)
        , set = nameSym (concat "set" suffix)
        , mapAccum = nameSym (concat "mapAccum" suffix)
        , map = nameSym (concat "map" suffix)
        }
      } in
    let mkAccessors = lam x. match x with (name, config) in
      let common = map (lam x. match x with (field, (ty, _)) in tripleToRequest (name, field, ty)) (mapBindings config.commonFields) in
      cons (tripleToRequest (name, "info", tycon_ "Info")) common in
    let res = mapBindings typeMap in
    let res = mapOption surfaceTypeInfo res in
    let res = result.mapM buryName res in
    result.map (lam xs. join (map mkAccessors xs)) res
  in

  -- NOTE(vipa, 2022-03-28): Compute a canonicalized form of a regex, with embedded type information
  recursive
    let inner
    : Option (Info, String) -> Regex -> Res [SRegex]
    = lam field. lam reg.
      let suggestLabel: String -> Res () = lam msg.
        match field with Some _ then result.ok () else
        let info = get_Regex_info reg in
        result.withAnnotations (result.warn (simpleMsg info msg)) (result.ok ()) in
      let res = switch reg
        case RecordRegex x then
          let suggest = suggestLabel "You probably want to save this record to a field (otherwise you should use parentheses for grouping).\n" in
          let mkReg = lam. lam content. [RecordReg
            { content = content
            , field = field
            , info = x.info
            }] in
          result.map2 mkReg suggest (regexToSRegex x.regex)
        case LiteralRegex x then
          result.ok [TerminalReg {term = LitTerm x.val.v, info = x.info, field = field}]
        case TokenRegex x then
          switch mapFindExn x.name.v typeMap
          case Left config then
            let suggest = suggestLabel "You probably want to save this type to a field.\n" in
            let res = result.ok [TerminalReg {term = NtTerm {name = x.name.v, config = config}, field = field, info = x.info}] in
            result.withAnnotations suggest res
          case Right config then
            result.ok [TerminalReg {term = TokenTerm config, field = field, info = x.info}]
          end
        case ConcatRegex x then
          result.map2 concat (regexToSRegex x.left) (regexToSRegex x.right)
        case AlternativeRegex x then
          let sregAlts = lam info. lam regs. match regs with [AltReg x]
            then x.alts
            else [{v = regs, i = info}] in
          let combine = lam ls. lam rs.
            [ AltReg
              { alts = concat
                (sregAlts (get_Regex_info x.left) ls)
                (sregAlts (get_Regex_info x.right) rs)
              }
            ] in
          result.map2 combine (regexToSRegex x.left) (regexToSRegex x.right)
        case EmptyRegex _ then
          result.ok []
        case NamedRegex x then
          inner (Some (x.name.i, x.name.v)) x.right
        case RepeatPlusRegex x then
          let mkReg = lam regs. snoc regs (KleeneReg {content = {v = regs, i = get_Regex_info x.left}, info = x.info}) in
          result.map mkReg (regexToSRegex x.left)
        case RepeatStarRegex x then
          let mkReg = lam regs. [KleeneReg {content = {v = regs, i = get_Regex_info x.left}, info = x.info}] in
          result.map mkReg (regexToSRegex x.left)
        case RepeatQuestionRegex x then
          let mkReg = lam regs.
            [AltReg {alts = [{v = [], i = x.info}, {v = regs, i = get_Regex_info x.left}]}] in
          result.map mkReg (regexToSRegex x.left)
        end
      in
      match (field, reg) with (Some (info, _), !(RecordRegex _ | TokenRegex _ | LiteralRegex _)) then
        let err = result.err (simpleMsg info "Only tokens, types, literals, and records can be saved in a field.\n") in
        result.withAnnotations err res
      else res
    let regexToSRegex
    : Regex -> Res [SRegex]
    = lam reg. inner (None ()) reg
  in

  -- NOTE(vipa, 2022-03-28): `max` is `None` if there is no upper bound,
  -- i.e., if it's under a kleene star
  type FieldInfo = {min : Int, max : Option Int, ty : [(Info, Res CarriedType)]} in
  type RecordInfo = Map String FieldInfo in
  let emptyRecordInfo : RecordInfo = mapEmpty cmpString in
  let singleRecordInfo : String -> Info -> Res CarriedType -> RecordInfo = lam field. lam info. lam a.
    mapInsert field {min = 1, max = Some 1, ty = [(info, a)]} emptyRecordInfo in
  let concatRecordInfo
    : RecordInfo -> RecordInfo -> RecordInfo
    = lam l. lam r.
      let f : FieldInfo -> FieldInfo -> FieldInfo = lam l. lam r.
        { min = addi l.min r.min
        , max = match (l.max, r.max) with (Some l, Some r) then Some (addi l r) else None ()
        , ty = concat l.ty r.ty
        } in
      foldl (lam acc. lam x. match x with (k, v) in mapInsertWith f k v acc) l (mapBindings r)
  in
  let altRecordInfo
    : RecordInfo -> RecordInfo -> RecordInfo
    = lam l. lam r.
      let f : FieldInfo -> FieldInfo -> FieldInfo = lam l. lam r.
        { min = mini l.min r.min
        , max = match (l.max, r.max) with (Some l, Some r) then Some (maxi l r) else None ()
        , ty = concat l.ty r.ty
        } in
      let minToZero : FieldInfo -> FieldInfo = lam c. {c with min = 0} in
      -- OPT(vipa, 2022-03-28): Ideally this would use a generalized merging function, roughly:
      -- `merge : (k -> a -> c) -> (k -> a -> b -> c) -> (k -> b -> c) -> Map k a -> Map k b -> Map k c`
      let isIn : RecordInfo -> (String, FieldInfo) -> Bool = lam m. lam entry.
        match mapLookup entry.0 m with Some _ then true else false in
      match partition (isIn r) (mapBindings l) with (lInBoth, lOnly) in
      match partition (isIn l) (mapBindings r) with (rInBoth, rOnly) in
      let lOnly = map (lam pair. match pair with (k, v) in (k, minToZero v)) lOnly in
      let rOnly = map (lam pair. match pair with (k, v) in (k, minToZero v)) rOnly in
      let res = mapFromSeq (mapGetCmpFun l) lInBoth in
      let res = foldl (lam acc. lam pair. match pair with (k, v) in mapInsertWith f k v acc) res rInBoth in
      let res = foldl (lam acc. lam pair. match pair with (k, v) in mapInsert k v acc) res (concat lOnly rOnly) in
      res
  in
  let kleeneRecordInfo
    : RecordInfo -> RecordInfo
    = lam c.
      let f : FieldInfo -> FieldInfo = lam c. {{c with min = 0} with max = None ()} in
      mapMap f c
  in

  -- NOTE(vipa, 2022-04-04): Create the complete record type implied by
  -- the `RecordInfo` (located at `Info`), failing if there are
  -- inconsistent types for one or more fields. This is what gives each
  -- field an appropriate type depending on how many times it appears.
  let reifyRecord
    : Info -> RecordInfo -> Res CarriedType
    = lam info. lam content.
      let buryInfo : all a. (Info, Res a) -> Res (Info, a) = lam x. result.map (lam a. (x.0, a)) x.1 in
      let groupByTypeRepr : [(Info, CarriedType)] -> Map Type [(Info, CarriedType)] =
        foldl
          (lam m. lam pair : (Info, CarriedType). mapInsertWith concat (carriedRepr pair.1) [pair] m)
          (mapEmpty cmpType) in
      let extractUniqueType : String -> (Int, Option Int) -> Map Type [(Info, CarriedType)] -> Res (String, CarriedType) = lam field. lam counts. lam m.
        switch mapBindings m
        case [(_, [(_, ty)] ++ _)] then
          let ty = switch counts
            case (0, Some 1) then optionType ty
            case (1, Some 1) then ty
            case _ then seqType ty
            end in
          result.ok (field, ty)
        case bindings then
          let typeMsg : (Type, [(Info, CarriedType)]) -> String = lam pair.
            let places = setOfSeq infoCmp (map (lam x. match x with (info, _) in info) pair.1) in
            let places = snoc (multiHighlight info (setToSeq places)) '\n' in
            join ["\n  These fields imply ", type2str pair.0, "\n", places]
          in
          let types = join (map typeMsg bindings) in
          let msg = join ["The type of field '", field, "' is inconsistent:\n", types] in
          result.err (info, msg)
        end in
      let fixField : (String, FieldInfo) -> Res (String, CarriedType) = lam pair.
        match pair with (field, count) in
        let tys : Res [(Info, CarriedType)] = result.mapM buryInfo count.ty in
        let tys : Res (Map Type [(Info, CarriedType)]) = result.map groupByTypeRepr tys in
        result.bind tys (extractUniqueType field (count.min, count.max))
      in result.map recordType (result.mapM fixField (mapBindings content))
  in
  recursive
    let computeRecordType
      : SRegex -> RecordInfo
      = lam reg.
        switch reg
        case TerminalReg x then
          match x.field with Some (info, field) then
            switch x.term
            case NtTerm {config = config} then
              let ty = result.map (lam config: TypeInfo. targetableType config.ty) config in
              singleRecordInfo field info ty
            case TokenTerm config then
              let ty = result.map
                (lam config: TokenInfo. untargetableType (tyrecord_ [("v", config.ty), ("i", tycon_ "Info")]))
                config in
              singleRecordInfo field info ty
            case LitTerm _ then
              singleRecordInfo field info (result.ok (untargetableType (tycon_ "Info")))
            end
          else emptyRecordInfo
        case RecordReg x then
          -- NOTE(vipa, 2022-03-30): There's presently no way to pass on
          -- errors discovered in an unlabelled record, which is a bit
          -- annoying. It should be unlikely to matter in practice, but
          -- it's a thing
          match x.field with Some (info, field) then
            let ty = reifyRecord x.info (concatted x.content) in
            singleRecordInfo field info ty
          else emptyRecordInfo
        case KleeneReg x then
          kleeneRecordInfo (concatted x.content.v)
        case AltReg x then
          match map (lam x: {v: [SRegex], i: Info}. concatted x.v) x.alts with [first] ++ rest in
          foldl altRecordInfo first rest
        end
    let concatted
      : [SRegex] -> RecordInfo
      = lam regs. foldl concatRecordInfo emptyRecordInfo (map computeRecordType regs)
  in

  let infoFieldLabel : String = "__br_info" in
  let termsFieldLabel : String = "__br_terms" in
  let stateTy = tyrecord_
    [ ("errors", tyapp_ (tycon_ "Ref") (tyseq_ (tytuple_ [tycon_ "Info", tystr_])))
    , ("content", tycon_ "String")
    ] in

  let operatorNtNames : Map Name {prefix : Name, infix : Name, postfix : Name, atom : Name} =
    let f = lam nt.
      let ntStr = nameGetStr nt in
      { prefix = nameSym (concat ntStr "Prefix")
      , infix = nameSym (concat ntStr "Infix")
      , postfix = nameSym (concat ntStr "Postfix")
      , atom = nameSym (concat ntStr "Atom")
      } in
    mapFromSeq nameCmp
      (map (lam nt : Name. (nt, f nt)) nts)
  in
  let productions
    : Ref [Res (MExpr, Production GenLabel ())] -- Each `Expr` evaluates to a production for ll1.mc
    = ref []
  in

  type PartialSymbol =
    { repr : MExpr
    , pat : Pat
    , info : MExpr
    , sym : SpecSymbol Token TokenRepr () GenLabel
    } in
  type PartialProduction =
    { record : RecordInfo
    -- `repr` evaluates to a `SpecSymbol`, `pat` matches the
    -- corresponding `ParsedSymbol`, `info` evaluates to a single `Info`
    -- for the corresponding symbol
    , symbols : [Res PartialSymbol]
    , terms : [Res MExpr] -- Each `Expr` evaluates to a sequence of `Info`s
    , fields : Map String [Res MExpr] -- Each `Expr` evaluates to a sequence of the underlying type
    } in

  let concatSyntax
    : PartialProduction -> PartialProduction -> PartialProduction
    = lam l. lam r.
      { record = concatRecordInfo l.record r.record
      , symbols = concat l.symbols r.symbols
      , terms = concat l.terms r.terms
      , fields = mapUnionWith concat l.fields r.fields
      } in
  let concattedSyntax
    : [PartialProduction] -> PartialProduction
    = lam regs.
      foldl concatSyntax { record = emptyRecordInfo, symbols = [], terms = [], fields = mapEmpty cmpString } regs
  in
  let join_ : [MExpr] -> MExpr = lam exprs. switch exprs
    case [] then seq_ []
    case [x] then x
    case [a, b] then concat_ a b
    case exprs then app_ (var_ "join") (seq_ exprs)
    end in
  let mergeInfos_ : [MExpr] -> MExpr = lam exprs. switch exprs
    case [] then conapp_ "NoInfo" unit_
    case [x] then x
    case [a, b] then appf2_ (var_ "mergeInfo") a b
    case [first] ++ exprs then appf3_ (var_ "foldl") (var_ "mergeInfo") first (seq_ exprs)
    end in

  recursive let collectNamesWithTypes
    : Pat -> [(Name, MType)]
    = lam p. match p with PatNamed {ident = PName n, ty = ty & !(TyUnknown _)}
      then [(n, ty)]
      else sfold_Pat_Pat (lam acc. lam x. concat acc (collectNamesWithTypes x)) [] p
  in

  let prodToRecordExpr
    : Option [Res MExpr] -> RecordInfo -> Map String [Res MExpr] -> Res MExpr
    = lam infos. lam record. lam fields.
      let mkField = lam binding: (String, FieldInfo).
        match binding with (field, count) in
        let exprs = match mapLookup field fields with Some exprs
          then result.mapM identity exprs
          else result.ok [] in
        let f = switch (count.min, count.max)
          case (0, Some 1) then
            let x = nameSym "x" in
            lam exprs. match_ (join_ exprs) (pseqedgew_ [npvar_ x] [])
              (conapp_ "Some" (nvar_ x))
              (conapp_ "None" unit_)
          case (1, Some 1) then
            let x = nameSym "x" in
            lam exprs. match_ (join_ exprs) (pseqedgew_ [npvar_ x] [])
              (nvar_ x)
              never_
          case _ then
            lam exprs. join_ exprs
          end
        in result.map (lam expr. (field, expr)) (result.map f exprs)
      in
      let res = result.mapM mkField (mapBindings (mapRemove "info" record)) in
      let res =
        match infos with Some infos then
          let infos = result.mapM identity infos in
          let infos = result.map mergeInfos_ infos in
          let infos = result.map (lam x. ("info", x)) infos in
          result.map2 snoc res infos
        else res
      in result.map urecord_ res
  in
  let mkRecordOfSeqsTy
    : RecordInfo -> Res Type
    = lam record.
      let f : (String, FieldInfo) -> Res (String, Type) = lam pair.
        let tys = result.mapM (lam x. match x with (_, x) in x) (pair.1 .ty) in
        let ty = result.map (lam xs. match xs with [x] ++ _ in x) tys in
        let ty = result.map carriedRepr ty in
        result.map (lam ty. (pair.0, tyseq_ ty)) ty
      in
      let fields = result.mapM f (mapBindings record) in
      let fields = result.map
        (concat [(infoFieldLabel, tycon_ "Info"), (termsFieldLabel, tyseq_ (tycon_ "Info"))])
        fields in
      result.map tyrecord_ fields
  in
  -- NOTE(vipa, 2022-04-05): Make a partial production consisting of a
  -- single symbol that will parse to a record of sequences.
  let mkRecordOfSeqsSymbol
    : Name -> RecordInfo -> PartialProduction
    = lam nt. lam record.
      let infoName = nameSym "info" in
      let valName = nameSym "val" in
      let mkSymbol = lam ty.
        { repr = app_ (var_ "ntSym") (nvar_ nt)
        , pat = pcon_ "UserSym"
          (use MExprAst in PatNamed {ident = PName valName, info = NoInfo (), ty = ty})
        , info = recordproj_ infoFieldLabel (nvar_ valName)
        , sym = ntSym nt
        } in
      { record = record
      , symbols = [result.map mkSymbol (mkRecordOfSeqsTy record)]
      , terms = [result.ok (recordproj_ termsFieldLabel (nvar_ valName))]
      , fields = mapMapWithKey (lam k. lam. [result.ok (recordproj_ k (nvar_ valName))]) record
      }
  in
  -- NOTE(vipa, 2022-04-05): Make a production that parses something
  -- internal to a production, i.e., its action produces a record with
  -- fields that are all sequences.
  let completeSeqProduction
    : (MExpr -> MExpr) -> Name -> GenLabel -> PartialProduction -> Res (MExpr, Production GenLabel ())
    = lam wrap. lam nt. lam label. lam x.
      let symbols =
        result.mapM identity x.symbols in
      let terms = result.mapM identity x.terms in
      let fields = result.map (mapFromSeq cmpString)
        (result.mapM
          (lam pair. match pair with (k, vs) in result.map (lam vs. (k, vs)) (result.mapM identity vs))
          (mapBindings x.fields)) in
      let mkProd
        : [PartialSymbol]
        -> [MExpr]
        -> Map String [MExpr]
        -> (MExpr, Production GenLabel ())
        = lam symbols. lam terms. lam fields.
          let temp = foldl
            (lam acc. lam x : PartialSymbol.
              match acc with (repr, pat, info, sym) in
              (snoc repr x.repr, snoc pat x.pat, snoc info x.info, snoc sym x.sym))
            ([], [], [], [])
            symbols in
          match temp with (reprs, pats, infos, syms) in
          let action: MExpr =
            let mkField : String -> (String, MExpr) = lam field.
              let exprs = match mapLookup field fields with Some exprs then exprs else [] in
              (field, join_ exprs) in
            let fields : [(String, MExpr)] = map mkField (mapKeys x.record) in
            let fields = concat fields [(infoFieldLabel, mergeInfos_ infos), (termsFieldLabel, join_ terms)] in
            let stateName = nameSym "state" in
            let seqName = nameSym "res" in
            let pats = pseqtot_ pats in
            let toRebind = map
              (lam pair. match pair with (name, ty) in nlet_ name ty (fromDyn_ (nvar_ name)))
              (collectNamesWithTypes pats) in
            nlam_ stateName stateTy
              (nulam_ seqName
                (match_ (nvar_ seqName) pats
                  (bindall_
                    (snoc toRebind
                      (asDyn_ (wrap (urecord_ fields)))))
                  never_))
          in
          let exprProduction = urecord_
            [ ("nt", nvar_ nt)
            , ("label", unit_)
            , ("rhs", seq_ reprs)
            , ("action", action)
            ] in
          let production =
            { nt = nt
            , label = label
            , rhs = syms
            , action = lam. lam. asDyn ()
            } in
          (exprProduction, production)
      in result.map3 mkProd symbols terms fields
  in

  -- NOTE(vipa, 2022-04-11): Process a single terminal, producing the
  -- components to be added to a PartialProduction for that symbol.
  let processTerminal
    : Terminal -> (Res PartialSymbol, [Res MExpr], Res MExpr, Res CarriedType)
    = lam term. switch term
      case NtTerm conf then
        let ty = result.map (lam config: TypeInfo. targetableType config.ty) conf.config in
        let pairName = nameSym "ntVal" in
        let pairPat = withTypePat (tytuple_ [tycon_ "Info", ntycon_ conf.name]) (npvar_ pairName) in
        let sym =
          { repr = app_ (var_ "ntSym") (nvar_ conf.name)
          , pat = pcon_ "UserSym" pairPat
          , info = tupleproj_ 0 (nvar_ pairName)
          , sym = ntSym conf.name
          } in
        (result.ok sym, [], result.ok (seq_ [tupleproj_ 1 (nvar_ pairName)]), ty)

      case TokenTerm config then
        let valName = nameSym "x" in
        let ty = result.map
          (lam config: TokenInfo. untargetableType (tyrecord_ [("v", config.ty), ("i", tycon_ "Info")]))
          config in
        let sym = result.map
          (lam config: TokenInfo.
            { repr = app_ (var_ "tokSym") config.repr
            , pat = pcon_ "TokParsed" (npcon_ config.tokConstructor (npvar_ valName))
            , info = config.getInfo (nvar_ valName)
            , sym = tokSym (PreRepr {constructorName = config.tokConstructor})
            })
          config in
        let info = result.map (lam config: TokenInfo. seq_ [config.getInfo (nvar_ valName)]) config in
        let val = result.map
          (lam config: TokenInfo. seq_ [urecord_ [("v", config.getValue (nvar_ valName)), ("i", config.getInfo (nvar_ valName))]])
          config in
        (sym, [info], val, ty)

      case LitTerm lit then
        let valName = nameSym "l" in
        ( result.ok
          { repr = app_ (var_ "litSym") (str_ lit)
          , pat = pcon_ "LitParsed" (npvar_ valName)
          , info = recordproj_ "info" (nvar_ valName)
          , sym = tokSym (PreLitRepr {lit = lit})
          }
        , [result.ok (seq_ [recordproj_ "info" (nvar_ valName)])]
        , result.ok (seq_ [recordproj_ "info" (nvar_ valName)])
        , result.ok (untargetableType (tycon_ "Info"))
        )

      end in

  -- NOTE(vipa, 2022-04-11): Produce a PartialProduction for a given
  -- SRegex, part of the rhs of the production defined through
  -- `prodName`.
  recursive let computeSyntax
    : {v: Name, i: Info} -> SRegex -> PartialProduction
    = lam prodName. lam reg. switch reg
      case TerminalReg x then
        match processTerminal x.term with (sym, terms, fieldExpr, fieldTy) in
        let res =
          { record = emptyRecordInfo
          , symbols = [sym]
          , terms = terms
          , fields = mapEmpty cmpString
          } in
        match x.field with Some (info, field) then
          {{res with record = singleRecordInfo field info fieldTy }
            with fields = mapInsert field [fieldExpr] res.fields }
        else res

      case RecordReg x then
        let res = concattedSyntax (map (computeSyntax prodName) x.content) in
        match x.field with Some (info, field) then
          let ty = reifyRecord x.info res.record in
          let expr = prodToRecordExpr (None ()) res.record res.fields in
          {{res with record = singleRecordInfo field info ty}
            with fields = mapInsert field [result.map (lam x. seq_ [x]) expr] (mapEmpty cmpString) }
        else {{res with record = emptyRecordInfo} with fields = mapEmpty cmpString }

      case KleeneReg x then
        let one = concattedSyntax (map (computeSyntax prodName) x.content.v) in
        let record = kleeneRecordInfo one.record in
        let nt = nameSym "kleene" in
        let sym = mkRecordOfSeqsSymbol nt record in
        let consProd = completeSeqProduction identity nt
          (ProdInternal {name = prodName, info = x.content.i})
          (concatSyntax one sym) in
        let nilProd = completeSeqProduction identity nt
          (ProdInternal {name = prodName, info = x.info})
          { record = record, symbols = [], terms = [], fields = mapEmpty cmpString } in
        modref productions (concat (deref productions) [consProd, nilProd]);
        sym

      case AltReg x then
        let alts = map (lam regs: {v: [SRegex], i: Info}. {v = concattedSyntax (map (computeSyntax prodName) regs.v), i = regs.i}) x.alts in
        let record =
          match map (lam p: {v: PartialProduction, i: Info}. p.v.record) alts with [first] ++ rest in
          foldl altRecordInfo first rest in
        let nt = nameSym "alt" in
        let prods = map
          (lam p: {v: PartialProduction, i: Info}.
            completeSeqProduction identity nt (ProdInternal {name = prodName, info = p.i})
              {p.v with record = record})
          alts in
        modref productions (concat (deref productions) prods);
        mkRecordOfSeqsSymbol nt record

      end
  in

  -- NOTE(vipa, 2022-03-31): Add the info field, erroring if it's
  -- already defined
  let addInfoField
    : Info -> RecordInfo -> RecordInfo
    = lam info. lam content.
      let count = {min = 1, max = Some 1, ty = [(NoInfo (), result.ok (untargetableType (tycon_ "Info")))]} in
      let mkError : all a. FieldInfo -> a -> FieldInfo = lam prev. lam.
        let highlight = multiHighlight info (map (lam x. match x with (info, _) in info) prev.ty) in
        let msg = join ["The 'info' field is reserved, it must not be manually defined:\n", highlight, "\n"] in
        let err = result.err (info, msg) in
        {prev with ty = snoc prev.ty (NoInfo (), err)}
      in mapInsertWith mkError "info" count content
  in

  let checkCommonField
    : Info -> Name -> RecordInfo -> RecordInfo
    = lam info. lam nt. lam content.
      match mapFindExn nt typeMap with Left config then
        match result.toOption config with Some config then
          let config: TypeInfo = config in
          let update = lam field. lam count : FieldInfo.
            match mapLookup field config.commonFields with Some _ then
              let infos = map (lam x. match x with (info, _) in info) count.ty in
              let msg = join
                [ "Each ", nameGetStr nt, " already has a '", field
                , "' field, you may not redeclare it here.\n"
                ] in
              let msg = multiMsg info infos msg in
              {count with ty = snoc count.ty (NoInfo (), result.err msg)}
            else count
          in mapMapWithKey update content
        else content
      else content
  in

  -- NOTE(vipa, 2022-03-31): Fix the name of the constructor, if it should be suffixed
  let computeConstructorName
    : {constructor : {v: Name, i: Info}, nt : {v: Name, i: Info}} -> Res Name
    = lam x.
      switch mapFindExn x.nt.v typeMap
      case Left config then
        let mkName = lam config: TypeInfo.
          if config.ensureSuffix then
            if isSuffix eqc (nameGetStr x.nt.v) (nameGetStr x.constructor.v)
            then x.constructor.v
            else nameSym (concat (nameGetStr x.constructor.v) (nameGetStr x.nt.v))
          else x.constructor.v
        in result.map mkName config
      case Right _ then
        result.err (x.nt.i, join ["The type of a production must be a type, not a token.\n", simpleHighlight x.nt.i, "\n"])
      end
  in

  -- NOTE(vipa, 2022-04-01): Figure out the operatorness of a production
  let findOperator
    : ProductionDeclRecord -> Name -> [SRegex] -> Res Operator
    = lam x. lam name. lam reg.
      let temp =
        match reg with [TerminalReg {field = Some (_, field), term = NtTerm {name = lname}}] ++ rest then
          if nameEq x.nt.v lname then (Some field, rest) else (None (), reg)
        else (None (), reg) in
      match temp with (lfield, reg) in
      let temp =
        match reg with rest ++ [TerminalReg {field = Some (_, field), term = NtTerm {name = rname}}] then
          if nameEq x.nt.v rname then (rest, Some field) else (reg, None ())
        else (reg, None ()) in
      match temp with (mid, rfield) in
      let assoc =
        match x.assoc with Some id then
          let id: {v : String, i : Info} = id in
          let res = switch id.v
            case "left" then result.ok (LAssoc ())
            case "right" then result.ok (RAssoc ())
            case _ then result.err (simpleMsg id.i "Invalid associativity, expected 'left' or 'right'.\n")
            end in
          if and (optionIsSome lfield) (optionIsSome rfield)
          then res
          else result.withAnnotations
            (result.err (simpleMsg id.i "Associativity is only valid on an infix operator, i.e., a production that is both left- and right-recursive.\n"))
            res
        else result.ok (NAssoc ()) in
      let fixAssoc = lam assoc.
        switch (lfield, rfield)
        case (Some _, None ()) then LAssoc ()
        case (None (), Some _) then RAssoc ()
        case _ then assoc
        end in
      let assoc = result.map fixAssoc assoc in
      let mkOperator = lam assoc.
        { lfield = lfield
        , rfield = rfield
        , mid = mid
        , nt = x.nt.v
        , names =
          { prodCon = name
          , prodLang = nameSym (concat (nameGetStr name) "Ast")
          , opCon = nameSym (concat (nameGetStr name) "Op")
          }
        , assoc = assoc
        , definition = x.name
        } in
      result.map mkOperator assoc
  in

  let mkOperatorConstructor
    : Operator
    -> RecordInfo
    -> PartialProduction
    -> Res GenOperator
    = lam op. lam record. lam prod.
      let #var"" =
        let opNtNames : {prefix : Name, infix : Name, postfix : Name, atom : Name} =
          mapFindExn op.nt operatorNtNames in
        let nt = switch (op.lfield, op.rfield)
          case (None _, None _) then opNtNames.atom
          case (Some _, None _) then opNtNames.postfix
          case (None _, Some _) then opNtNames.prefix
          case (Some _, Some _) then opNtNames.infix
          end in
        modref productions
          (snoc (deref productions)
            (completeSeqProduction (nconapp_ op.names.opCon) nt (ProdTop op.definition) prod)) in
      let mkUnsplit = switch (op.lfield, op.rfield)
        case (None _, None _) then AtomUnsplit
          (lam conf : {record : MExpr, info : MExpr}.
            let fields =
              mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
            let res = prodToRecordExpr (Some [result.ok conf.info]) record fields in
            match result.toOption res with Some record in
            nconapp_ op.names.prodCon record)
        case (Some lfield, None _) then PostfixUnsplit
          (lam conf : {record : MExpr, info : MExpr, left : MExpr}.
            let fields =
              mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
            let fields =
              mapInsertWith (lam prev. lam new. concat new prev) lfield [result.ok (seq_ [conf.left])] fields in
            let res = prodToRecordExpr (Some [result.ok conf.info]) record fields in
            match result.toOption res with Some record in
            nconapp_ op.names.prodCon record)
        case (None _, Some rfield) then PrefixUnsplit
          (lam conf : {record : MExpr, info : MExpr, right : MExpr}.
            let fields =
              mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
            let fields =
              mapInsertWith (lam prev. lam new. concat prev new) rfield [result.ok (seq_ [conf.right])] fields in
            let res = prodToRecordExpr (Some [result.ok conf.info]) record fields in
            match result.toOption res with Some record in
            nconapp_ op.names.prodCon record)
        case (Some lfield, Some rfield) then InfixUnsplit
          (lam conf : {record : MExpr, info : MExpr, left : MExpr, right : MExpr}.
            let fields =
              mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
            let fields =
              mapInsertWith (lam prev. lam new. concat new prev) lfield [result.ok (seq_ [conf.left])] fields in
            let fields =
              mapInsertWith (lam prev. lam new. concat prev new) rfield [result.ok (seq_ [conf.right])] fields in
            let res = prodToRecordExpr (Some [result.ok conf.info]) record fields in
            match result.toOption res with Some record in
            nconapp_ op.names.prodCon record)
        end in
      let f = lam ty.
        { requiredFragments = [op.names.prodLang]
        , opConstructorName = op.names.opCon
        , precedenceKey = Some op.names.prodCon
        , baseTypeName = op.nt
        , carried = ty
        , mkUnsplit = mkUnsplit
        , assoc = op.assoc
        } in
      result.map f (mkRecordOfSeqsTy prod.record)
  in

  -- NOTE(vipa, 2022-03-31): Compute all info for the constructors
  let operators : Ref (Map Name (Res Operator)) = ref (mapEmpty nameCmp) in
  type ConstructorInfo =
    { constructor : Constructor
    , operator : Operator
    , genOperator : GenOperator
    } in
  let constructors : Res [ConstructorInfo] =
    let check = lam decl.
      match decl with ProductionDecl x then
        let name = computeConstructorName {constructor = x.name, nt = x.nt} in
        let regInfo = get_Regex_info x.regex in
        let reg = regexToSRegex x.regex in
        let content = result.map concatted reg in
        let content = result.map (addInfoField x.info) content in
        let content = result.map (checkCommonField regInfo x.nt.v) content in
        let carried = result.bind content (reifyRecord regInfo) in
        let operator = result.bind2 name reg (findOperator x) in
        let partProd = result.map (lam op: Operator. map (computeSyntax x.name) op.mid) operator in
        let partProd = result.map concattedSyntax partProd in
        let genOp = result.bind3 operator content partProd mkOperatorConstructor in
        let mkRes = lam name. lam carried. lam operator. lam genOp.
          { constructor =
            { name = name
            , synType = x.nt.v
            , carried = carried
            , fragment = operator.names.prodLang
            }
          , operator = operator
          , genOperator = genOp
          } in
        modref operators (mapInsert x.name.v operator (deref operators));
        Some (result.map4 mkRes name carried operator genOp)
      else
        None ()
      in
    result.mapM identity (mapOption check decls)
  in

  let foldWithLater
    : all a. all acc. (a -> acc -> a -> acc) -> acc -> [a] -> acc
    = lam f.
      recursive let work = lam acc. lam seq.
        match seq with [a] ++ seq then
          work (foldl (f a) acc seq) seq
        else acc
      in work
  in

  let operators : Map Name (Res Operator) = deref operators in
  let cmpNamePair = lam a: (Name, Name). lam b: (Name, Name).
    let res = nameCmp a.0 b.0 in
    match res with 0 then nameCmp a.1 b.1 else res in
  let precedences : Res (Map Name (Map (Name, Name) Ordering)) =
    type OrderDef = {ordering: Ordering, surround: Info, i1: Info, i2: Info} in
    type Acc = (Map Name (Map (Name, Name) [OrderDef]), Res ()) in
    let addPrec : (Name, Name) -> OrderDef -> Map (Name, Name) [OrderDef] -> Map (Name, Name) [OrderDef]
      = lam pair. lam def. if leqi (nameCmp pair.0 pair.1) 0
        then mapInsertWith concat pair [def]
        else mapInsertWith concat (pair.1, pair.0) [{def with ordering = flipOrdering def.ordering}]
    in
    let computeOrders : Acc -> Decl -> Acc = lam acc. lam decl.
      match decl with PrecedenceTableDecl x then
        let ensureNonAtomic : Info -> Operator -> Res Operator = lam info. lam op.
          match (op.lfield, op.rfield) with !(None _, None _) then result.ok op else
          result.err (simpleMsg info "This is not an operator") in
        let levels : [{noeq: Option Info, operators: [{v: Res Operator, i: Info}]}] = map
          (lam level: {noeq: Option Info, operators: [{v: Name, i: Info}]}.
            { operators = mapOption
              (lam n: {v: Name, i: Info}. match mapLookup n.v operators with Some op
                then Some {v = result.bind op (ensureNonAtomic n.i), i = n.i}
                else None ())
              level.operators
            , noeq = level.noeq
            })
          x.levels in
        let exceptions : [(Set Name, Set Name)] = map
          (lam x: {lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}.
            let getName: {v: Name, i: Info} -> Name = lam x. x.v in
            ( setOfSeq nameCmp (map getName x.lefts)
            , setOfSeq nameCmp (map getName x.rights)
            ))
          x.exceptions in
        let isException : (Name, Name) -> Bool = lam pair. any
          (lam row: (Set Name, Set Name).
            if (if setMem pair.0 row.0 then setMem pair.1 row.1 else false) then true
            else (if setMem pair.1 row.0 then setMem pair.0 row.1 else false))
          exceptions in
        let maybeAddPrec : Name -> (Name, Name) -> OrderDef -> Map Name (Map (Name, Name) [OrderDef]) -> Map Name (Map (Name, Name) [OrderDef]) =
          lam nt. lam n. lam def. lam m. if isException n then m else
            let inner = match mapLookup nt m with Some m then m else mapEmpty cmpNamePair in
            let inner = addPrec n def inner in
            mapInsert nt inner m in
        recursive let foldNames
          : all acc. (acc -> {v: Res Operator, i: Info} -> acc)
          -> acc
          -> [{noeq: Option Info, operators: [{v: Res Operator, i: Info}]}]
          -> acc
          = lam f. lam acc. lam levels.
            match levels with [level] ++ levels then
              foldNames f (foldl f acc level.operators) levels
            else acc
        in
        recursive let processLevel
          : Acc
          -> [{noeq: Option Info, operators: [{v: Res Operator, i: Info}]}]
          -> Acc
          = lam acc. lam levels.
            match levels with [level] ++ levels then
              let f
                : Ordering
                -> {v: Res Operator, i: Info}
                -> Acc
                -> {v: Res Operator, i: Info}
                -> Acc
                = lam ordering. lam op1. lam acc. lam op2.
                  let mkAddDef = lam rop1: Operator. lam rop2: Operator.
                    maybeAddPrec rop1.nt (rop1.names.prodCon, rop2.names.prodCon) {ordering = ordering, surround = x.info, i1 = op1.i, i2 = op2.i}
                  in
                  let res = result.map2 mkAddDef op1.v op2.v in
                  let defs = match result.toOption res with Some f then f acc.0 else acc.0 in
                  (defs, result.withAnnotations res acc.1) in
              let acc =
                match level.noeq with None _ then
                  foldWithLater (f (EQ ())) acc level.operators
                else acc in
              let acc = foldl
                (lam acc. lam op1. foldNames (f (GT ()) op1) acc levels)
                acc
                level.operators
              in processLevel acc levels
            else acc
        in
        match processLevel acc levels with (orders, res) in
        let types: Map Name [Info] = foldNames
          (lam acc. lam rop: {v: Res Operator, i: Info}.
            match result.toOption rop.v with Some op then
              let op: Operator = op in
              mapInsertWith concat op.nt [rop.i] acc
            else acc)
          (mapEmpty nameCmp)
          levels in
        let res =
          match mapBindings types with types & ([_, _] ++ _) then
            let f : (Name, [Info]) -> String = lam binding.
              let theOps = match binding.1 with [_] then "This operator has type " else "These operators have type " in
              join [theOps, nameGetStr binding.0, ":\n", multiHighlight x.info binding.1, "\n"] in
            let msg = join (cons "A precedence table must not mix types\n" (map f types)) in
            let here = result.err (x.info, msg) in
            result.withAnnotations here res
          else res in
        (orders, res)
      else acc
    in
    match foldl computeOrders (mapEmpty nameCmp, result.ok ()) decls with (orders, res) in
    let findUnique : ((Name, Name), [OrderDef]) -> Res ((Name, Name), Ordering) = lam binding.
      let groupByOrdering: [OrderDef] -> Map Ordering [OrderDef] =
        foldl
          (lam m. lam def: OrderDef. mapInsertWith concat (def.ordering) [def] m)
          (mapEmpty (lam l. lam r. subi (constructorTag l) (constructorTag r))) in
      switch mapBindings (groupByOrdering binding.1)
      case [(ordering, _)] then result.ok (binding.0, ordering)
      case orderings then
        let f : (Ordering, [OrderDef]) -> String = lam pair.
          let ordToStr : Ordering -> String = lam x. switch x
            case LT _ then " < "
            case GT _ then " > "
            case EQ _ then " = "
            end in
          let theseImply = match pair.1 with [_, _] ++ _ then "These definitions imply " else "This definition implies " in
          let msg = join [theseImply, nameGetStr binding.0 .0, ordToStr pair.0, nameGetStr binding.0 .1, "\n"] in
          let f : OrderDef -> String = lam def. join
            [ info2str def.surround, "\n"
            , multiHighlight def.surround [def.i1, def.i2], "\n"
            ] in
          concat msg (join (map f pair.1)) in
        result.err (NoInfo (), concat "Inconsistent precedence\n" (join (map f orderings)))
      end in
    let orders = result.map (mapFromSeq nameCmp)
      (result.mapM
        (lam inner: (Name, Map (Name, Name) [OrderDef]). result.map
          (lam m. (inner.0, mapFromSeq cmpNamePair m))
          (result.mapM findUnique (mapBindings inner.1)))
        (mapBindings orders)) in
    result.withAnnotations res orders
  in

  let badConstructors : Res [Constructor] =
    let f = lam nt.
      let carried = addInfoField (NoInfo ()) emptyRecordInfo in
      let carried = checkCommonField (NoInfo ()) nt carried in
      let carried = reifyRecord (NoInfo ()) carried in
      let f = lam carried.
        { name = nameSym (concat "Bad" (nameGetStr nt))
        , synType = nt
        , carried = carried
        , fragment = nameSym (join ["Bad", nameGetStr nt, "Ast"])
        } in
      result.map f carried in
    result.mapM f nts
  in

  let groupingOperators : Res [GenOperator] =
    let f = lam nt.
      match mapFindExn nt typeMap with Left tinfo in
      let f : TypeInfo -> Res (Option GenOperator) = lam tinfo.
        match tinfo.grouping with Some (lpar, rpar) then
          let lpar: {v: Either Name String, i: Info} = lpar in
          let rpar: {v: Either Name String, i: Info} = rpar in
          let carried = tyrecord_
            [ (infoFieldLabel, tycon_ "Info")
            , (termsFieldLabel, tyseq_ (tycon_ "Info"))
            , ("inner", tinfo.ty)
            ] in
          let parToTerminal : {v: Either Name String, i: Info} -> Terminal = lam sym.
            switch sym.v
            case Left name then
              match mapFindExn name typeMap with Right config in
              TokenTerm config
            case Right lit then
              LitTerm lit
            end in
          let ntTerminal : Terminal = NtTerm
            { config = match mapFindExn nt typeMap with Left config in config
            , name = nt
            } in
          match processTerminal (parToTerminal lpar) with (lPartSym, _, _, _) in
          match processTerminal ntTerminal with (ntSym, _, ntVal, _) in
          match processTerminal (parToTerminal rpar) with (rPartSym, _, _, _) in
          let f : PartialSymbol -> PartialSymbol -> PartialSymbol -> MExpr -> GenOperator
            = lam lPartSym. lam ntSym. lam rPartSym. lam ntVal.
              let conName = nameSym (concat (nameGetStr nt) "Grouping") in
              let atomNt =
                let opNames: {prefix : Name, infix : Name, postfix : Name, atom : Name} =
                  mapFindExn nt operatorNtNames in
                opNames.atom
              in
              let action =
                let seqName = nameSym "seq" in
                let pats = pseqtot_ [lPartSym.pat, ntSym.pat, rPartSym.pat] in
                let toRebind = map
                  (lam pair. match pair with (name, ty) in nlet_ name ty (fromDyn_ (nvar_ name)))
                  (collectNamesWithTypes pats) in
                ulam_ ""
                  (nulam_ seqName
                    (match_ (nvar_ seqName) pats
                      (bindall_
                        (snoc toRebind
                          (asDyn_
                            (nconapp_ conName
                              (urecord_
                                [ (infoFieldLabel, mergeInfos_ [lPartSym.info, ntSym.info, rPartSym.info])
                                , (termsFieldLabel, seq_ [lPartSym.info, rPartSym.info])
                                , ("inner", match_ ntVal (pseqtot_ [pvar_ "x"]) (var_ "x") never_)
                                ])))))
                      never_))
              in
              let prod =
                ( urecord_
                  [ ("nt", nvar_ atomNt)
                  , ("label", unit_)
                  , ("rhs", seq_ [lPartSym.repr, ntSym.repr, rPartSym.repr])
                  , ("action", action)
                  ]
                , { nt = atomNt
                  , label = TyGrouping {left = lpar.i, right = rpar.i}
                  , rhs = [lPartSym.sym, ntSym.sym, rPartSym.sym]
                  , action = lam. lam. asDyn ()
                  }
                ) in
              modref productions (snoc (deref productions) (result.ok prod));
              { requiredFragments = []
              , opConstructorName = conName
              , precedenceKey = None ()
              , baseTypeName = nt
              , carried = carried
              , mkUnsplit = AtomUnsplit
                (lam x: {record : MExpr, info : MExpr}. recordproj_ "inner" x.record)
              , assoc = NAssoc ()
              }
          in result.map (lam x. Some x) (result.map4 f lPartSym ntSym rPartSym ntVal)
        else result.ok (None ())
      in result.bind tinfo f
    in result.map (mapOption identity) (result.mapM f nts)
  in

  let extraFragments : Res [Name] =
    result.map (lam ss. setToSeq (setOfSeq nameCmp ss))
      (result.mapM identity (deref fragments))
  in

  let composedParseFragmentName = nameSym (concat "Parse" langName) in
  let composedAstFragmentName = nameSym (concat langName "Ast") in

  let genOpResult : Res GenOpResult =
    let mkMirroredProduction
      : all label. { nt : Name, rhs : [Name], label : label, action : MExpr }
      -> (MExpr, Production label ())
      = lam prod.
        let liftSpec : Name -> MExpr = lam sym.
          (app_ (var_ "ntSym") (nvar_ sym)) in
        ( urecord_
          [ ("nt", nvar_ prod.nt)
          , ("rhs", seq_ (map liftSpec prod.rhs))
          , ("label", unit_)
          , ("action", prod.action)
          ]
        , { nt = prod.nt
          , rhs = map ntSym prod.rhs
          , label = prod.label
          , action = lam. lam. error "impossible"
          }
        )
    in
    let synInfo : Res [(Name, SynDesc)] =
      let f : Map Name (Map (Name, Name) Ordering) -> Constructor -> Res (Name, SynDesc) = lam precedence. lam constructor.
        let precedence = mapLookupOrElse (lam. mapEmpty cmpNamePair) constructor.synType precedence in
        match mapFindExn constructor.synType typeMap with Left tinfo in
        let f : TypeInfo -> (Name, SynDesc) = lam tinfo.
          let parToStr : {v: Either Name String, i: Info} -> String = lam x. switch x.v
            case Left n then snoc (cons '<' (nameGetStr n)) '>'
            case Right lit then lit
            end in
          let parsToStr : ({v: Either Name String, i: Info}, {v: Either Name String, i: Info}) -> (String, String) = lam pair.
            (parToStr pair.0, parToStr pair.1) in
          let desc =
            { bad =
              { conName = constructor.name
              , langName = constructor.fragment
              }
            , baseFragmentName = composedAstFragmentName
            , grouping = optionMap parsToStr tinfo.grouping
            , precedence = precedence
            } in
          (constructor.synType, desc)
        in result.map f tinfo
      in result.bind2 precedences badConstructors (lam precedences. lam cs. result.mapM (f precedences) cs)
    in
    let f : [(Name, SynDesc)] -> [ConstructorInfo] -> [GenOperator] -> [Name] -> GenOpResult = lam syns. lam constructors. lam groupingOperators. lam extraFragments.
      use MkOpLanguages in
      let genOpInput =
        { fieldLabels = { info = infoFieldLabel, terms = termsFieldLabel }
        , syns = mapFromSeq nameCmp syns
        , namingScheme =
          { synName = lam str. concat str "Op"
          , opBaseLangName = lam str. concat str "OpBase"
          }
        , operators = concat
          (map (lam x: ConstructorInfo. x.genOperator) constructors)
          groupingOperators
        , composedName = composedParseFragmentName
        , extraFragments = cons (nameNoSym "LL1Parser") extraFragments
        } in
      let genOpResult : GenOpResult = mkOpLanguages genOpInput in
      let mkRegexProductions : {v: Name, i: Info} -> [Res (MExpr, Production GenLabel ())] = lam original.
        let lclosed = nameSym (concat (nameGetStr original.v) "_lclosed") in
        let lopen = nameSym (concat (nameGetStr original.v) "_lopen") in
        let regexNts : {prefix : Name, infix : Name, postfix : Name, atom : Name} =
          mapFindExn original.v operatorNtNames in
        let top = mkMirroredProduction
          { nt = original.v
          , label = TyTop original
          , rhs = [lclosed]
          , action = ulam_ "" (ulam_ "seq"
            (match_ (var_ "seq") (pseqtot_ [pcon_ "UserSym" (pvar_ "cont")])
              (app_ (fromDyn_ (var_ "cont")) (conapp_ "Some" (app_ (var_ "breakableInitState") unit_)))
              never_
            ))
          } in
        let atom = mkMirroredProduction
          { nt = lclosed
          , label = TyRegex {nt = original, kind = LRegAtom ()}
          , rhs = [regexNts.atom, lopen]
          , action = ulam_ "p" (ulam_ "seq"
            (match_ (var_ "seq")
              (pseqtot_ [pcon_ "UserSym" (pvar_ "x"), pcon_ "UserSym" (pvar_ "cont")])
              (asDyn_
                (ulam_ "st"
                  (app_ (fromDyn_ (var_ "cont"))
                    (genOpResult.addAtomFor original.v (var_ "p") (fromDyn_ (var_ "x")) (var_ "st")))))
              never_))
          } in
        let infix = mkMirroredProduction
          { nt = lopen
          , label = TyRegex {nt = original, kind = LRegInfix ()}
          , rhs = [regexNts.infix, lclosed]
          , action = ulam_ "p" (ulam_ "seq"
            (match_ (var_ "seq")
              (pseqtot_ [pcon_ "UserSym" (pvar_ "x"), pcon_ "UserSym" (pvar_ "cont")])
              (asDyn_
                (ulam_ "st"
                  (app_ (fromDyn_ (var_ "cont"))
                    (genOpResult.addInfixFor original.v (var_ "p") (fromDyn_ (var_ "x")) (var_ "st")))))
              never_))
          } in
        let prefix = mkMirroredProduction
          { nt = lclosed
          , label = TyRegex {nt = original, kind = LRegPrefix ()}
          , rhs = [regexNts.prefix, lclosed]
          , action = ulam_ "p" (ulam_ "seq"
            (match_ (var_ "seq")
              (pseqtot_ [pcon_ "UserSym" (pvar_ "x"), pcon_ "UserSym" (pvar_ "cont")])
              (asDyn_
                (ulam_ "st"
                  (app_ (fromDyn_ (var_ "cont"))
                    (genOpResult.addPrefixFor original.v (var_ "p") (fromDyn_ (var_ "x")) (var_ "st")))))
              never_))
          } in
        let postfix = mkMirroredProduction
          { nt = lopen
          , label = TyRegex {nt = original, kind = LRegPostfix ()}
          , rhs = [regexNts.postfix, lopen]
          , action = ulam_ "p" (ulam_ "seq"
            (match_ (var_ "seq")
              (pseqtot_ [pcon_ "UserSym" (pvar_ "x"), pcon_ "UserSym" (pvar_ "cont")])
              (asDyn_
                (ulam_ "st"
                  (app_ (fromDyn_ (var_ "cont"))
                    (genOpResult.addPostfixFor original.v (var_ "p") (fromDyn_ (var_ "x")) (var_ "st")))))
              never_))
          } in
        let final = mkMirroredProduction
          { nt = lopen
          , label = TyRegex {nt = original, kind = LRegEnd ()}
          , rhs = []
          , action = ulam_ "p" (ulam_ ""
            (asDyn_ (ulam_ "st" (genOpResult.finalizeFor original.v (var_ "p") (var_ "st")))))
          } in
        map result.ok [top, atom, infix, prefix, postfix, final]
      in
      let newProds = map mkRegexProductions ntsWithInfo in
      modref productions (join (cons (deref productions) newProds));
      genOpResult
    in result.map4 f synInfo constructors groupingOperators extraFragments
  in

  let productions : Res [(MExpr, Production GenLabel ())] = result.mapM identity (deref productions) in
  let ll1Error : Res () =
    let snd = lam prod: (MExpr, Production GenLabel ()). prod.1 in
    let productions = result.map (map snd) productions in
    result.bind2 start productions
      (lam start: Name. lam productions: [Production GenLabel ()].
        match genParsingTable {start = start, productions = productions} with Left err then
          let errs : [(SpecSymbol Token TokenRepr () GenLabel, [GenLabel])] = join (map mapBindings (mapValues err)) in
          let regexKindToStr = lam x. switch x
            case LRegAtom _ then "production"
            case LRegInfix _ then "infix operator"
            case LRegPrefix _ then "prefix operator"
            case LRegPostfix _ then "postfix operator"
            case LRegEnd _ then error "impossible"
            end in
          let genLabelToString = lam x. switch x
            case TyTop x then join ["A ", nameGetStr x.v, "\n"]
            case TyRegex {nt = nt, kind = LRegEnd _} then join ["Something coming after a ", nameGetStr nt.v, "\n"]
            case TyRegex x then join ["A ", nameGetStr x.nt.v, " ", regexKindToStr x.kind, "\n"]
            case TyGrouping x then snoc (multiHighlight (NoInfo ()) [x.left, x.right]) '\n'
            case ProdTop x then snoc (simpleHighlight x.i) '\n'
            case ProdInternal x then snoc (simpleHighlight x.info) '\n'
            end in
          let mkErr : (SpecSymbol Token TokenRepr () GenLabel, [GenLabel]) -> Res () = lam pair.
            let msg = join
              [ "LL1 conflict when seeing a ", symSpecToStr pair.0
              , ", it might be the start of one of these:\n"
              ] in
            let msg = concat msg (join (map genLabelToString pair.1)) in
            result.err (NoInfo (), msg)
          in result.map (lam. ()) (result.mapM mkErr errs)
        else result.ok ()
      )
  in

  let table : Res MDecl =
    let f : Name -> GenOpResult -> [(MExpr, Production GenLabel ())] -> MDecl =
      lam start. lam genOpResult. lam prods.
        let getNt = lam x. match x with NtSpec nt then Some nt else None () in
        let nts = join (map
          (lam x: (MExpr, Production GenLabel ()). match x with (_, x) in
            cons x.nt (mapOption getNt x.rhs))
          prods) in
        let nts = setToSeq (setOfSeq nameCmp nts) in
        let nts = map (lam name. nulet_ name (app_ (var_ "nameSym") (str_ (nameGetStr name)))) nts in
        let prods = map (lam x. match x with (x, _) in x) prods in
        let grammar = urecord_
          [ ("start", nvar_ start)
          , ("productions", genOpResult.wrapProductions (seq_ prods))
          ] in
        let grammar = bindall_ (snoc nts grammar) in
        let table = _uletin_ "target" (app_ (var_ "genParsingTable") grammar)
          (match_ (var_ "target") (pcon_ "Right" (pvar_ "table"))
            (var_ "table")
            never_) in
        use LetDeclAst in
        use UseAst in
        DeclLet
          { ident = nameNoSym "_table"
          , tyAnnot = tyunknown_
          , tyBody = tyunknown_
          , body = TmUse
            { ident = composedParseFragmentName
            , info = NoInfo ()
            , ty = tyunknown_
            , inexpr =  table
            }
          , info = NoInfo ()
          }
    in result.map3 f start genOpResult productions
  in

  let parseFunctions : Res [MDecl] =
    let f = lam start.
      use LetDeclAst in
      use UseAst in
      use BootParser in
      let parse = parseMExprStringExn {_defaultBootParserParseMExprStringArg () with allowFree = true} in
      let body = parse
        (strJoin "\n"
          [ "  let config = {errors = ref [], content = content} in"
          , "  let res = parseWithTable _table filename config content in"
          , "  switch (res, deref config.errors)"
          , "  case (Right dyn, []) then"
          , "    match fromDyn dyn with (_, res) in Right res"
          , "  case (Left err, errors) then"
          , "    let err = ll1DefaultHighlight content (ll1ToErrorHighlightSpec err) in"
          , "    Left (snoc errors err)"
          , "  case (_, errors) then"
          , "    Left errors"
          , "  end"
          ]) in
      let parseStr = join ["parse", langName] in
      let parseNormal = DeclLet
        { ident = nameNoSym parseStr
        , info = NoInfo ()
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_
        , body = ulam_ "filename"
          (ulam_ "content"
            (TmUse
              { ident = composedParseFragmentName
              , inexpr = body
              , ty = tyunknown_
              , info = NoInfo ()
              }))
        } in
      let exnBody = parse
        (strJoin "\n"
          [ "lam filename. lam content."
          , join ["  switch ", parseStr, " filename content"]
          , "  case Left errors then"
          , "    for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));"
          , "    exit 1"
          , "  case Right file then file"
          , "  end"
          ]) in
      let parseExn = DeclLet
        { ident = nameNoSym (concat parseStr "Exn")
        , info = NoInfo ()
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_
        , body = exnBody
        } in
      [parseNormal, parseExn]
    in result.map f start
  in

  let tableAndFunctions : Res [MDecl] =
    result.map2 cons table parseFunctions
  in

  -- NOTE(vipa, 2022-03-21): Generate the actual language fragments
  let generated: Res [MDecl] = result.bind5 constructors badConstructors requestedFieldAccessors genOpResult tableAndFunctions
    (lam constructors : [ConstructorInfo]. lam badConstructors. lam requestedFieldAccessors. lam genOpResult : GenOpResult. lam tableAndFunctions.
      let genInput =
        { baseName = nameSym (concat langName "BaseAst")
        , composedName = Some composedAstFragmentName
        , constructors = concat
          (map (lam x. x.constructor) constructors)
          badConstructors
        , sfunctions = requestedSFunctions
        , fieldAccessors = requestedFieldAccessors
        } in
      use IncludeDeclAst in
      result.ok (join
        [ [ DeclInclude {path = "seq.mc", info = NoInfo ()}
          , DeclInclude {path = "parser/ll1.mc", info = NoInfo ()}
          , DeclInclude {path = "parser/breakable.mc", info = NoInfo ()}
          ]
        , map (lam x. DeclInclude {path = x.path.v, info = x.info}) includes
        , mkLanguages genInput
        , genOpResult.fragments
        , tableAndFunctions
        ])
    ) in

  match result.consume (result.withAnnotations ll1Error (result.withAnnotations allResolved generated)) with (warnings, res) in
  for_ warnings (lam x. match x with (info, msg) in printLn (infoWarningString info msg));
  switch res
  case Left errors then
    for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
    exit 1
  case Right res then
    printLn (join ["Writing the generated code to file '", destinationFile, "'"]);
    writeFile destinationFile (use MLangPrettyPrint in mlang2str {decls = res, expr = unit_});
    printLn "Done"
  end

mexpr

match argv with [_, synFile, outFile] then
  runParserGenerator {synFile = synFile, outFile = outFile}
else
  ()
