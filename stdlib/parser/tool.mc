include "selfhost-sketch.mc"
include "gen-ast.mc"
include "result.mc"
include "seq.mc"
include "mexpr/cmp.mc"

mexpr

use MExprCmp in
use MExprPrettyPrint in
use CarriedBasic in
use SelfhostAst in

type TypeInfo = {ty : Type, ensureSuffix : Bool} in
type TokenInfo = {ty : Type, repr : Expr, tokConstructor : Name, getInfo : Expr -> Expr, getValue : Expr -> Expr} in

type Terminal in
con NtTerm : {config : Res TypeInfo, name : Name} -> Terminal in
con TokenTerm : Res TokenInfo -> Terminal in
con LitTerm : String -> Terminal in
type SRegex in
con TerminalReg : {term: Terminal, info: Info, field: Option (Info, String)} -> SRegex in
con RecordReg : {content: [SRegex], info: Info, field: Option (Info, String)} -> SRegex in
con KleeneReg : {content: {v: [SRegex], i: Info}, info: Info} -> SRegex in
con AltReg : {alts: [[SRegex]]} -> SRegex in

type Assoc in
con NAssoc : () -> Assoc in
con LAssoc : () -> Assoc in
con RAssoc : () -> Assoc in
type Operator =
  { lfield : Option String
  , rfield : Option String
  , mid : [SRegex]
  , nt : Name
  , assoc : Assoc
  } in

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
        let sregAlts = lam regs. match regs with [AltReg x]
          then x.alts
          else [regs] in
        let combine = lam ls. lam rs. [AltReg {alts = concat (sregAlts ls) (sregAlts rs)}] in
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
        let mkReg = lam regs. [AltReg {alts = [[], regs]}] in
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
type FieldCount a = {min : Int, max : Option Int, ty : [(Info, a)]} in
type ParseContent a = Map String (FieldCount a) in
let emptyContent : ParseContent a = mapEmpty cmpString in
let singleContent : String -> Info -> a -> ParseContent a = lam field. lam info. lam a.
  mapInsert field {min = 1, max = Some 1, ty = [(info, a)]} emptyContent in
let concatContent
  : ParseContent a -> ParseContent a -> ParseContent a
  = lam l. lam r.
    let f : FieldCount a -> FieldCount a -> FieldCount a = lam l. lam r.
      { min = addi l.min r.min
      , max = match (l.max, r.max) with (Some l, Some r) then Some (addi l r) else None ()
      , ty = concat l.ty r.ty
      } in
    foldl (lam acc. lam x. match x with (k, v) in mapInsertWith f k v acc) l (mapBindings r)
in
let altContent
  : ParseContent a -> ParseContent a -> ParseContent a
  = lam l. lam r.
    let f : FieldCount a -> FieldCount a -> FieldCount a = lam l. lam r.
      { min = mini l.min r.min
      , max = match (l.max, r.max) with (Some l, Some r) then Some (maxi l r) else None ()
      , ty = concat l.ty r.ty
      } in
    let minToZero : FieldCount a -> FieldCount a = lam c. {c with min = 0} in
    -- OPT(vipa, 2022-03-28): Ideally this would use a generalized merging function, roughly:
    -- `merge : (k -> a -> c) -> (k -> a -> b -> c) -> (k -> b -> c) -> Map k a -> Map k b -> Map k c`
    let isIn : ParseContent a -> (String, FieldCount a) -> Bool = lam m. lam entry.
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
let kleeneContent
  : ParseContent a -> ParseContent a
  = lam c.
    let f : FieldCount a -> FieldCount a = lam c. {{c with min = 0} with max = None ()} in
    mapMap f c
in

-- NOTE(vipa, 2022-03-31): Compute the record type implied by a
-- [SRegex]
recursive
  let computeRecordType
    : SRegex -> ParseContent (Res CarriedType)
    = lam reg.
      switch reg
      case TerminalReg x then
        match x.field with Some (info, field) then
          switch x.term
          case NtTerm {config = config} then
            let ty = result.map (lam config: TypeInfo. targetableType config.ty) config in
            singleContent field info ty
          case TokenTerm config then
            let ty = result.map
              (lam config: TokenInfo. untargetableType (tyrecord_ [("v", config.ty), ("i", tycon_ "Info")]))
              config in
            singleContent field info ty
          case LitTerm _ then
            singleContent field info (result.ok (untargetableType (tycon_ "Info")))
          end
        else emptyContent
      case RecordReg x then
        -- NOTE(vipa, 2022-03-30): There's presently no way to pass on
        -- errors discovered in an unlabelled record, which is a bit
        -- annoying. It should be unlikely to matter in practice, but
        -- it's a thing
        match x.field with Some (info, field) then
          let ty = reifyRecord x.info (concatted x.content) in
          singleContent field info ty
        else emptyContent
      case KleeneReg x then
        kleeneContent (concatted x.content.v)
      case AltReg x then
        match map concatted x.alts with [first] ++ rest in
        foldl altContent first rest
      end
  let concatted
    : [SRegex] -> ParseContent (Res CarriedType)
    = lam regs. foldl concatContent emptyContent (map computeRecordType regs)
  let reifyRecord
    : Info -> ParseContent (Res CarriedType) -> Res CarriedType
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
      let fixField : (String, FieldCount (Res CarriedType)) -> Res (String, CarriedType) = lam pair.
        match pair with (field, count) in
        let tys : Res [(Info, CarriedType)] = result.mapM buryInfo count.ty in
        let tys : Res (Map Type [(Info, CarriedType)]) = result.map groupByTypeRepr tys in
        result.bind tys (extractUniqueType field (count.min, count.max))
      in result.map recordType (result.mapM fixField (mapBindings content))
in

-- NOTE(vipa, 2022-03-31): Add the info field, erroring if it's
-- already defined
let addInfoField
  : Info -> ParseContent (Res CarriedType) -> ParseContent (Res CarriedType)
  = lam info. lam content.
    let count = {min = 1, max = Some 1, ty = [(NoInfo (), result.ok (untargetableType (tycon_ "Info")))]} in
    let mkError : FieldCount (Res CarriedType) -> a -> FieldCount (Res CarriedType) = lam prev. lam.
      let highlight = multiHighlight info (map (lam x. match x with (info, _) in info) prev.ty) in
      let msg = join ["The 'info' field is reserved, it must not be manually defined:\n", highlight, "\n"] in
      let err = result.err (info, msg) in
      {prev with ty = snoc prev.ty (NoInfo (), err)}
    in mapInsertWith mkError "info" count content
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
  : ProductionDeclRecord -> [SRegex] -> Res Operator
  = lam x. lam reg.
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
      , assoc = assoc
      } in
    result.map mkOperator assoc
in

-- NOTE(vipa, 2022-03-31): Compute all info for the constructors
type ConstructorInfo =
  { constructor : Constructor
  , operator : Operator
  } in
let constructors : Res [ConstructorInfo] =
  let check = lam decl. switch decl
    case ProductionDecl x then
      let name = computeConstructorName {constructor = x.name, nt = x.nt} in
      let regInfo = get_Regex_info x.regex in
      let reg = regexToSRegex x.regex in
      let content = result.map concatted reg in
      let content = result.map (addInfoField x.info) content in
      let carried = result.bind content (reifyRecord regInfo) in
      let operator = result.bind reg (findOperator x) in
      let mkRes = lam name. lam carried. lam operator.
        { constructor =
          { name = name
          , synType = x.nt.v
          , carried = carried
          }
        , operator = operator
        } in
      Some (result.map3 mkRes name carried operator)
    case _ then
      None ()
    end in
  result.mapM identity (mapOption check decls)
in

-- NOTE(vipa, 2022-03-21): Generate the actual language fragments
let generated: Res String = result.bind constructors -- TODO(vipa, 2022-03-22): Replace this with something appropriate once we're generating more stuff
  (lam constructors : [ConstructorInfo].
    let genInput =
      { baseName = "SelfhostBaseAst"
      , composedName = Some "SelfhostAst"
      , fragmentName = lam name. concat (nameGetStr name) "Ast"
      , constructors = map (lam x: ConstructorInfo. x.constructor) constructors
      , requestedSFunctions = requestedSFunctions
      }
    in result.ok (concat "include \"seq.mc\"\n\n" (mkLanguages genInput))
  ) in

match result.consume (result.withAnnotations start (result.withAnnotations allResolved generated)) with (warnings, res) in
for_ warnings (lam x. match x with (info, msg) in printLn (infoWarningString info msg));
switch res
case Left errors then
  for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
  exit 1
case Right res then
  printLn res
  -- dprintLn temp;
  -- printLn "Ok"
end
