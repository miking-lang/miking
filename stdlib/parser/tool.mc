include "selfhost-sketch.mc"
include "gen-ast.mc"
include "result.mc"
include "seq.mc"

mexpr

use SelfhostAst in
match argv with [_, filename] in
let content = readFile filename in
match parseSelfhostExn filename content with File {decls = decls} in

let simpleHighlight
  : Info -> String
  = lam info.
    formatHighlights terminalHighlightErrorConfig content [Relevant info]
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
      let msg = join
        [ nameGetStr name.v, " is unbound.\n"
        , "  ", simpleHighlight name.i, "\n"
        ]
      in result.err (name.i, msg) in
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
        (match x.name with Some name then lookupName name nameEnv.types else result.ok (None ()))
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
-- NOTE(vipa, 2022-03-21): We can continue to do some analysis on each
-- decl individually, so don't merge the list into a single Res yet.
let decls: [Res Decl] = map resolveDecl decls in



-- NOTE(vipa, 2022-03-21): Remaining analysis uses the complete list,
-- thus we want to merge it into a single Res
let decls: Res [Decl] = result.mapM identity decls in

-- NOTE(vipa, 2022-03-21): Compute the required sfunctions
let nts: Res [Name] =
  let inner = lam x. match x with TypeDecl x then Some x.name.v else None () in
  result.map (mapOption inner) decls in
let requestedSFunctions: Res [(SynType, Type)] =
  let mkPair = lam a. lam b. (stringToSynType (nameGetStr a), ntycon_ b) in
  result.map (lam nts. seqLiftA2 mkPair nts nts) nts in

-- NOTE(vipa, 2022-03-22): Find the starting non-terminal
let start: Res Name =
  let inner = lam x. match x with StartDecl x then Some (x.info, x.name.v) else None () in
  let starts: Res [(Info, Name)] = result.map (mapOption inner) decls in
  result.bind starts
    (lam starts. switch starts
      case [] then result.err (infoVal filename 0 0 0 0, "Missing start symbol")
      case [(_, start)] then result.ok start
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
    )
in

-- NOTE(vipa, 2022-03-21): Generate the actual language fragments
let generated: Res String = result.bind requestedSFunctions
  (lam requestedSFunctions.
    let genInput =
      { namePrefix = "Selfhost"
      , constructors = []
      , requestedSFunctions = requestedSFunctions
      , composedName = None ()
      }
    in use CarriedTypeGenerate in result.ok (mkLanguages genInput)
  ) in

match result.consume (result.withAnnotations start generated) with (warnings, res) in
switch res
case Left errors then
  for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
  exit 1
case Right res then
  printLn res
end
