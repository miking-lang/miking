include "selfhost-sketch.mc"
include "gen-ast.mc"
include "gen-op-ast.mc"
include "result.mc"
include "seq.mc"
include "mexpr/cmp.mc"

-- NOTE(vipa, 2022-04-05): A token type only ever intended for
-- analysis, thus only containing a TokenRepr, no Token. This is used
-- for all tokens declared with the `token` declaration.
lang PreToken = TokenParser
  syn Token =
  syn TokenRepr =
  | PreRepr {constructorName : Name}

  sem tokReprToStr =
  | PreRepr x -> join ["<", nameGetStr x.constructorName, ">"]

  sem tokReprCompare =
  | (PreRepr l, PreRepr r) -> nameCmp l.constructorName r.constructorName
end

lang PreLitToken = TokenParser
  syn TokenRepr =
  | PreLitRepr {lit : String}

  sem tokReprToStr =
  | PreLitRepr x -> snoc (cons '\'' x.lit) '\''

  sem tokReprCompare =
  | (PreLitRepr l, PreLitRepr r) -> cmpString l.lit r.lit
end

lang LL1Analysis = ParserGeneration + PreToken + PreLitToken
end

mexpr

use MExprCmp in
use MExprPrettyPrint in
use CarriedBasic in
use LL1Analysis in
use SelfhostAst in

type TypeInfo = {ty : Type, ensureSuffix : Bool, commonFields : Map String (Type, Expr)} in
type TokenInfo = {ty : Type, repr : Expr, tokConstructor : Name, getInfo : Expr -> Expr, getValue : Expr -> Expr} in

type Terminal in
con NtTerm : {config : Res TypeInfo, name : Name} -> Terminal in
con TokenTerm : Res TokenInfo -> Terminal in
con LitTerm : String -> Terminal in
type SRegex in
con TerminalReg : {term: Terminal, info: Info, field: Option (Info, String)} -> SRegex in
con RecordReg : {content: [SRegex], info: Info, field: Option (Info, String)} -> SRegex in
con KleeneReg : {content: {v: [SRegex], i: Info}, info: Info} -> SRegex in
con AltReg : {alts: [{v: [SRegex], i: Info}]} -> SRegex in

type Assoc in
con NAssoc : () -> Assoc in
con LAssoc : () -> Assoc in
con RAssoc : () -> Assoc in
type Operator =
  { lfield : Option String
  , rfield : Option String
  , mid : [SRegex]
  , nt : Name
  , definition : {v: Name, i: Info}
  , conName : Name
  , opConName : Name
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
con ProdTop : {v: Name, i: Info} -> GenLabel in
con ProdInternal : {name: {v: Name, i: Info}, info: Info} -> GenLabel in

match argv with ![_, _] then
  printLn "Please provide exactly one argument; a .syn file";
  exit 0
else match argv with [_, filename] in
let content = readFile filename in
match parseSelfhostExn filename content with File {decls = decls} in

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

type Res a = Result (Info, String) (Info, String) a in

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
let resolveDecl
  : Decl -> Res Decl
  = lam decl.
    switch decl
    case TypeDecl x then
      result.map
        (lam name. TypeDecl {x with name = name})
        (lookupName x.name nameEnv.types)
    case TokenDecl x then
      result.map
        (lam name. TokenDecl {x with name = name})
        (match x.name with Some name then result.map (lam x. Some x) (lookupName name nameEnv.types) else result.ok (None ()))
    case StartDecl x then
      result.map
        (lam name. StartDecl {x with name = name})
        (lookupName x.name nameEnv.types)
    case PrecedenceTableDecl x then
      let resolveLevel = lam level: {noeq : Option {v: (), i: Info}, operators : [{v: Name, i: Info}]}.
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

-- NOTE(vipa, 2022-03-21): Compute the required sfunctions
let nts: [Name] =
  let inner = lam x. match x with TypeDecl x then Some x.name.v else None () in
  mapOption inner decls in
let requestedSFunctions: [(Name, Type)] =
  let mkPair = lam a. lam b. (a, ntycon_ b) in
  seqLiftA2 mkPair nts nts in

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

-- NOTE(vipa, 2022-03-28):  Compute type information
let typeMap: Map Name (Either (Res TypeInfo) (Res TokenInfo)) =
  let addDecl = lam m. lam decl. switch decl
    case TypeDecl x then
      let info: TypeInfo =
        { ty = ntycon_ x.name.v
        , ensureSuffix = true
        , commonFields = mapEmpty cmpString
        } in
      mapInsert x.name.v (Left (result.ok info)) m
    case TokenDecl (x & {name = Some n}) then
      -- TODO(vipa, 2022-03-28): get this information in a more principled way
      let n : {v: Name, i: Info} = n in
      let info: TokenInfo =
        { ty = tycon_ (nameGetStr n.v)
        , repr = conapp_ (concat (nameGetStr n.v) "Repr") unit_
        , tokConstructor = nameNoSym (concat (nameGetStr n.v) "Tok")
        , getInfo = recordproj_ "info"
        , getValue = recordproj_ "val"
        } in
      mapInsert n.v (Right (result.ok info)) m
    case _ then
      m
    end in
  foldl addDecl (mapEmpty nameCmp) decls
in

let requestedFieldAccessors : Res [(Name, String, Type)] =
  let surfaceTypeInfo = lam x. match x with (n, Left config) then Some (n, config) else None () in
  let buryName = lam x. match x with (n, config) in result.map (lam x. (n, x)) config in
  let mkAccessors = lam x. match x with (name, config) in
    let config: TypeInfo = config in
    let common = map (lam x. match x with (field, (ty, _)) in (name, field, ty)) (mapBindings config.commonFields) in
    cons (name, "info", tycon_ "Info") common in
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
        result.ok [TerminalReg {term = LitTerm x.val, info = x.info, field = field}]
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
let singleRecordInfo : String -> Info -> a -> RecordInfo = lam field. lam info. lam a.
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
    let buryInfo : (Info, Res a) -> Res (Info, a) = lam x. result.map (lam a. (x.0, a)) x.1 in
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
  : Ref [Res (Expr, Production GenLabel ())] -- Each `Expr` evaluates to a production for ll1.mc
  = ref []
in

type PartialSymbol =
  { repr : Expr
  , pat : Pat
  , info : Expr
  , sym : SpecSymbol
  } in
type PartialProduction =
  { record : RecordInfo
  -- `repr` evaluates to a `SpecSymbol`, `pat` matches the
  -- corresponding `ParsedSymbol`, `info` evaluates to a single `Info`
  -- for the corresponding symbol
  , symbols : [Res PartialSymbol]
  , terms : [Res Expr] -- Each `Expr` evaluates to a sequence of `Info`s
  , fields : Map String [Res Expr] -- Each `Expr` evaluates to a sequence of the underlying type
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
let join_ : [Expr] -> Expr = lam exprs. switch exprs
  case [] then seq_ []
  case [x] then x
  case [a, b] then concat_ a b
  case exprs then app_ (var_ "join") (seq_ exprs)
  end in
let mergeInfos_ : [Expr] -> Expr = lam exprs. switch exprs
  case [] then conapp_ "NoInfo" unit_
  case [x] then x
  case [a, b] then appf2_ (var_ "mergeInfo") a b
  case [first] ++ exprs then appf3_ (var_ "foldl") (var_ "mergeInfo") first (seq_ exprs)
  end in

let prodToRecordExpr
  : Option [Res Expr] -> RecordInfo -> Map String [Res Expr] -> Res Expr
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
    let res = result.mapM mkField (mapBindings record) in
    let res =
      match infos with Some infos then
        let infos = result.mapM identity infos in
        let infos = result.map mergeInfos_ infos in
        let infos = result.map (lam x. ("info", x)) infos in
        result.map2 cons infos res
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
      -- TODO(vipa, 2022-04-05): Attach ty to the npvar
      , pat = pcon_ "UserSym" (npvar_ valName)
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
  : (Expr -> Expr) -> Name -> GenLabel -> PartialProduction -> Res (Expr, Production GenLabel ())
  = lam wrap. lam nt. lam label. lam x.
    let symbols =
      result.mapM identity x.symbols in
    let terms = result.mapM identity x.terms in
    let fields = result.map (mapFromSeq cmpString)
      (result.mapM
        (lam pair. match pair with (k, vs) in result.map (lam vs. (k, vs)) (result.mapM identity vs))
        (mapBindings x.fields)) in
    let mkProd
      : [PartialProduction]
      -> [Expr]
      -> Map String [Expr]
      -> (Expr, Production GenLabel ())
      = lam symbols. lam terms. lam fields.
        let temp = foldl
          (lam acc. lam x : PartialSymbol.
            match acc with (repr, pat, info, sym) in
            (snoc repr x.repr, snoc pat x.pat, snoc info x.info, snoc sym x.sym))
          ([], [], [], [])
          symbols in
        match temp with (reprs, pats, infos, syms) in
        let action: Expr =
          let mkField : String -> (String, Expr) = lam field.
            let exprs = match mapLookup field fields with Some exprs then exprs else [] in
            (field, join_ exprs) in
          let fields : [(String, Expr)] = map mkField (mapKeys x.record) in
          let fields = concat fields [(infoFieldLabel, mergeInfos_ infos), (termsFieldLabel, join_ terms)] in
          let stateName = nameSym "state" in
          let seqName = nameSym "res" in
          nlam_ stateName stateTy
            (nulam_ seqName
              (match_ (nvar_ seqName) (pseqtot_ pats)
                -- TODO(vipa, 2022-04-05): Add type annotations plucked from the `Pat`s captures
                (wrap (urecord_ fields))
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
          , action = lam. lam. ()
          } in
        (exprProduction, production)
    in result.map3 mkProd symbols terms fields
in

-- NOTE(vipa, 2022-04-11): Process a single terminal, producing the
-- components to be added to a PartialProduction for that symbol.
let processTerminal
  : Terminal -> (Res PartialSymbol, [Res Expr], Res Expr, Res CarriedType)
  = lam term. switch term
    case NtTerm conf then
      let ty = result.map (lam config: TypeInfo. targetableType config.ty) conf.config in
      let infoName = nameSym "info" in
      let valName = nameSym "val" in
      let sym =
        { repr = app_ (var_ "ntSym") (nvar_ conf.name)
        , pat = pcon_ "UserSym" (ptuple_ [npvar_ infoName, npvar_ valName])
        , info = nvar_ infoName
        , sym = ntSym conf.name
        } in
      (result.ok sym, [], result.ok (seq_ [nvar_ valName]), ty)

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
      let val = result.map (lam config: TokenInfo. seq_ [config.getValue (nvar_ valName)]) config in
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
    let mkError : FieldInfo -> a -> FieldInfo = lam prev. lam.
      let highlight = multiHighlight info (map (lam x. match x with (info, _) in info) prev.ty) in
      let msg = join ["The 'info' field is reserved, it must not be manually defined:\n", highlight, "\n"] in
      let err = result.err (info, msg) in
      {prev with ty = snoc prev.ty (NoInfo (), err)}
    in mapInsertWith mkError "info" count content
in

let checkCommonField
  : ProductionDeclRecord -> RecordInfo -> RecordInfo
  = lam x. lam content.
    match mapFindExn x.nt.v typeMap with Left config then
      match result.toOption config with Some config then
        let config: TypeInfo = config in
        let update = lam field. lam count : FieldInfo.
          match mapLookup field config.commonFields with Some _ then
            let infos = map (lam x. match x with (info, _) in info) count.ty in
            let msg = join
              [ "Each ", nameGetStr x.nt.v, " already has a '", field
              , "' field, you may not redeclare it here.\n"
              ] in
            let msg = multiMsg (get_Regex_info x.regex) infos msg in
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
      , conName = name
      , opConName = nameSym (concat (nameGetStr name) "Op")
      , assoc = assoc
      , definition = x.name
      } in
    result.map mkOperator assoc
in

let mkOperatorConstructor
  : Operator
  -> PartialProduction
  -> Res GenOpInput
  = lam op. lam prod.
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
          (completeSeqProduction (nconapp_ op.opConName) nt (ProdTop op.definition) prod)) in
    let mkUnsplit = switch (op.lfield, op.rfield)
      case (None _, None _) then AtomUnsplit
        (lam conf : {record : Expr, info : Expr}.
          let fields =
            mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
          let res = prodToRecordExpr (Some [result.ok conf.info]) prod.record fields in
          match result.toOption res with Some record in
          nconapp_ op.conName record)
      case (Some lfield, None _) then PostfixUnsplit
        (lam conf : {record : Expr, info : Expr, left : Expr}.
          let fields =
            mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
          let fields =
            mapInsertWith (lam prev. lam new. concat new prev) lfield [result.ok conf.left] fields in
          let res = prodToRecordExpr (Some [result.ok conf.info]) prod.record fields in
          match result.toOption res with Some record in
          nconapp_ op.conName record)
      case (None _, Some rfield) then PrefixUnsplit
        (lam conf : {record : Expr, info : Expr, right : Expr}.
          let fields =
            mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
          let fields =
            mapInsertWith (lam prev. lam new. concat prev new) rfield [result.ok conf.right] fields in
          let res = prodToRecordExpr (Some [result.ok conf.info]) prod.record fields in
          match result.toOption res with Some record in
          nconapp_ op.conName record)
      case (Some lfield, Some rfield) then InfixUnsplit
        (lam conf : {record : Expr, info : Expr, left : Expr, right : Expr}.
          let fields =
            mapMapWithKey (lam field. lam. [result.ok (recordproj_ field conf.record)]) prod.fields in
          let fields =
            mapInsertWith (lam prev. lam new. concat new prev) lfield [result.ok conf.left] fields in
          let fields =
            mapInsertWith (lam prev. lam new. concat prev new) rfield [result.ok conf.right] fields in
          let res = prodToRecordExpr (Some [result.ok conf.info]) prod.record fields in
          match result.toOption res with Some record in
          nconapp_ op.conName record)
      end in
    let f = lam ty.
      { baseConstructorName = op.conName
      , opConstructorName = op.opConName
      , baseTypeName = op.nt
      , carried = ty
      , mkUnsplit = mkUnsplit
      } in
    result.map f (mkRecordOfSeqsTy prod.record)
in

-- NOTE(vipa, 2022-03-31): Compute all info for the constructors
type ConstructorInfo =
  { constructor : Constructor
  , operator : Operator
  , genOperator : GenOperator
  } in
let constructors : Res [ConstructorInfo] =
  let check = lam decl. switch decl
    case ProductionDecl x then
      let name = computeConstructorName {constructor = x.name, nt = x.nt} in
      let regInfo = get_Regex_info x.regex in
      let reg = regexToSRegex x.regex in
      let content = result.map concatted reg in
      let content = result.map (addInfoField x.info) content in
      let content = result.map (checkCommonField x) content in
      let carried = result.bind content (reifyRecord regInfo) in
      let operator = result.bind2 name reg (findOperator x) in
      let partProd = result.map (lam op: Operator. map (computeSyntax x.name) op.mid) operator in
      let partProd = result.map concattedSyntax partProd in
      let genOp = result.bind2 operator partProd mkOperatorConstructor in
      let mkRes = lam name. lam carried. lam operator. lam genOp.
        { constructor =
          { name = name
          , synType = x.nt.v
          , carried = carried
          }
        , operator = operator
        , genOperator = genOp
        } in
      Some (result.map4 mkRes name carried operator genOp)
    case _ then
      None ()
    end in
  result.mapM identity (mapOption check decls)
in

let productions : Res [(Expr, Production GenLabel ())] = result.mapM identity (deref productions) in
let ll1Error : Res () =
  let fst = lam prod: (Expr, Production GenLabel ()). prod.1 in
  let productions = result.map (map fst) productions in
  result.bind2 start productions
    (lam start: Name. lam productions: [Production GenLabel ()].
      match genParsingTable {start = start, productions = productions} with Left err then
        let errs : [(SpecSymbol, [GenLabel])] = join (map mapBindings (mapValues err)) in
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
          case ProdTop x then snoc (simpleHighlight x.i) '\n'
          case ProdInternal x then snoc (simpleHighlight x.info) '\n'
          end in
        let mkErr : (SpecSymbol, [GenLabel]) -> Res () = lam pair.
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

-- NOTE(vipa, 2022-03-21): Generate the actual language fragments
let generated: Res String = result.bind2 constructors requestedFieldAccessors
  (lam constructors : [ConstructorInfo]. lam requestedFieldAccessors.
    let genInput =
      { baseName = "SelfhostBaseAst"
      , composedName = Some "SelfhostAst"
      , fragmentName = lam name. concat (nameGetStr name) "Ast"
      , constructors = map (lam x: ConstructorInfo. x.constructor) constructors
      , requestedSFunctions = requestedSFunctions
      , fieldAccessors = requestedFieldAccessors
      } in
    let genOpInput =
      { infoFieldLabel = infoFieldLabel
      , termsFieldLabel = termsFieldLabel
      , mkSynName = lam name. concat (nameGetStr name) "Op"
      , mkSynAstBaseName = lam. "SelfhostBaseAst"
      , mkConAstName = lam name. concat (nameGetStr name) "Ast"
      , mkBaseName = lam str. concat str "Base"
      , composedName = "ParseSelfhost"
      , operators = map (lam x: ConstructorInfo. x.genOperator) constructors
      } in
    result.ok (strJoin "\n\n" ["include \"seq.mc\"", mkLanguages genInput, mkOpLanguages genOpInput])
  ) in

let prodsToStr = lam prods: [(Expr, a)].
  let res = map (lam x. match x with (x, _) in x) prods in
  let res = seq_ res in
  expr2str res in
let foo =
  match result.toOption (result.map prodsToStr productions)
  with Some str then printLn str
  else ()
in

match result.consume (result.withAnnotations ll1Error (result.withAnnotations allResolved generated)) with (warnings, res) in
for_ warnings (lam x. match x with (info, msg) in printLn (infoWarningString info msg));
switch res
case Left errors then
  for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
  exit 1
case Right res then
  printLn res
  -- dprintLn productions
  -- dprintLn temp;
  -- printLn "Ok"
end
