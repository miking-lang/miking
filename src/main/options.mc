include "assoc.mc"
include "common.mc"
include "option.mc"
include "string.mc"

type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  exitBefore : Bool,
  runTests : Bool,
  excludeIntrinsicsPreamble : Bool,
  disableOptimizations : Bool
}

-- Option structure
let options = {
  debugParse = false,
  debugGenerate = false,
  exitBefore = false,
  runTests = false,
  excludeIntrinsicsPreamble = false,
  disableOptimizations = false
}

-- Option map, maps strings to structure updates
let optionsMap = [
("--debug-parse", lam o : Options. {o with debugParse = true}),
("--debug-generate", lam o : Options. {o with debugGenerate = true}),
("--exit-before", lam o : Options. {o with exitBefore = true}),
("--test", lam o : Options. {o with runTests = true}),
("--exclude-intrinsics-preamble", lam o : Options. {o with excludeIntrinsicsPreamble = true}),
("--disable-optimizations", lam o : Options. {o with disableOptimizations = true})
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

