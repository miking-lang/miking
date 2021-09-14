include "assoc.mc"
include "common.mc"
include "option.mc"
include "string.mc"

type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  debugProfile : Bool,
  exitBefore : Bool,
  runTests : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  printHelp : Bool
}

-- Option structure
let options = {
  debugParse = false,
  debugGenerate = false,
  debugTypeAnnot = false,
  debugProfile = false,
  exitBefore = false,
  runTests = false,
  disableOptimizations = false,
  useTuned = false,
  printHelp = false
}

-- Option map, maps strings to structure updates
let optionsMap = [
("--debug-parse", lam o : Options. {o with debugParse = true}),
("--debug-generate", lam o : Options. {o with debugGenerate = true}),
("--debug-type-annot", lam o : Options. {o with debugTypeAnnot = true}),
("--debug-profile", lam o : Options. {o with debugProfile = true}),
("--exit-before", lam o : Options. {o with exitBefore = true}),
("--test", lam o : Options. {o with runTests = true}),
("--disable-optimizations", lam o : Options. {o with disableOptimizations = true}),
("--use-tuned", lam o : Options. {o with useTuned = true}),
("--help", lam o: Options. {o with printHelp = true})
]

let mapStringLookup = assocLookup {eq=eqString}

-- Simple handling of options before we have an argument parsing library.
let parseOptions = lam xs.
  foldl
    (lam accOps. lam s.
      match mapStringLookup s optionsMap with Some f
      then f accOps
      else printLn (concat "Unknown option " s); exit 1
    ) options xs

-- Split the program arguments before and after the empty '--'
let splitDashDash = lam lst.
  match index (eqString "--") lst with Some n then
    let r = splitAt lst n in
    {first = r.0, last = tail r.1}
  else
    {first = lst, last = []}

-- Split the program arguments at the first occurrence of a non-option.
let splitOptionPrefix = lam lst.
  match index (compose not (isPrefix eqChar "--")) lst with Some n then
    let r = splitAt lst n in
    {first = r.0, last = r.1}
  else
    {first = lst, last = []}
