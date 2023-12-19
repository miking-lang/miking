include "assoc.mc"
include "option.mc"
include "ext/toml-ext.mc"

type SearchMethod
con Exhaustive         : () -> SearchMethod

let tuneSearchMethodMap =
[ ("exhaustive", Exhaustive ())
]

-- Options for tuning
type TuneOptions =
{ verbose : Bool
, iters : Int
, timeoutMs : Option Float
, warmups : Int
, method : SearchMethod
, args : [String]
, epsilonMs : Float
, stepSize : Int
, ignoreErrors : Bool
, exitEarly : Bool
, seed : Option Int
, dependencyAnalysis : Bool
, cleanup : Bool
, debugDependencyAnalysis : Bool
, debugInstrumentation : Bool
, debugExpansion : Bool
, reduceDependencies : Float
, printStats : Bool
}

-- Default options
let tuneOptionsDefault : TuneOptions =
{ verbose = false
, iters = 10
, timeoutMs = None ()
, warmups = 1
, method = Exhaustive ()
, args = []
, epsilonMs = 10.0
, stepSize = 1
, ignoreErrors = false
, exitEarly = true
, seed = None ()
, dependencyAnalysis = true
, debugDependencyAnalysis = false
, debugInstrumentation = false
, debugExpansion = false
, reduceDependencies = 0.0
, cleanup = false
, printStats = false
}

let tuneOptionsFromToml: TuneOptions -> String -> TuneOptions =
  lam default. lam tomlString.
    let toml = tomlBindings (tomlFromStringExn tomlString) in
    foldl (lam acc. lam bind: (String, TomlValue).
      match bind with (k,v) in
      switch k
      case "verbose" then {acc with verbose = tomlValueToBoolExn v}
      case "iters" then {acc with iters = tomlValueToIntExn v}
      case "timeoutMs" then {acc with timeoutMs = Some (tomlValueToFloatExn v)}
      case "warmups" then {acc with warmups = tomlValueToIntExn v}
      case "method" then
        let method = tomlValueToStringExn v in
        {acc with method = optionGetOrElse
          (lam. error (concat "Unknown method: " method))
          (assocLookup {eq=eqString} method tuneSearchMethodMap)}
      case "args" then {acc with args = tomlValueToStringSeqExn v}
      case "epsilonMs" then {acc with epsilonMs = tomlValueToFloatExn v}
      case "stepSize" then {acc with stepSize = tomlValueToIntExn v}
      case "ignoreErrors" then {acc with ignoreErrors = tomlValueToBoolExn v}
      case "exitEarly" then {acc with exitEarly = tomlValueToBoolExn v}
      case "seed" then {acc with seed = Some (tomlValueToIntExn v)}
      case "dependencyAnalysis" then
        {acc with dependencyAnalysis = tomlValueToBoolExn v}
      case "debugDependencyAnalysis" then
        {acc with debugDependencyAnalysis = tomlValueToBoolExn v}
      case "debugInstrumentation" then
        {acc with debugInstrumentation = tomlValueToBoolExn v}
      case "debugExpansion" then
        {acc with debugExpansion = tomlValueToBoolExn v}
      case "reduceDependencies" then
        {acc with reduceDependencies = tomlValueToFloatExn v}
      case "cleanup" then {acc with cleanup = tomlValueToBoolExn v}
      case "printStats" then {acc with printStats = tomlValueToBoolExn v}
      case key then error (concat "Unknown option: " key)
      end
    ) default toml

mexpr

utest tuneOptionsFromToml tuneOptionsDefault
"
verbose = true
iters = 3
timeoutMs = 0.1
method = \"exhaustive\"
args = [\"3000 3 1\", \"20000 3 2\"]
epsilonMs = 1.0
stepSize = 102
ignoreErrors = true
exitEarly = false
seed = 42
dependencyAnalysis = false
debugDependencyAnalysis = true
debugInstrumentation = true
debugExpansion = false
reduceDependencies = 10.0
cleanup = true
printStats = true
"
with
{ verbose = true
, iters = 3
, timeoutMs = Some 0.1
, warmups = 1
, method = Exhaustive ()
, args = ["3000 3 1", "20000 3 2"]
, epsilonMs = 1.0
, stepSize = 102
, ignoreErrors = true
, exitEarly = false
, seed = Some 42
, dependencyAnalysis = false
, debugDependencyAnalysis = true
, debugInstrumentation = true
, debugExpansion = false
, reduceDependencies = 10.0
, cleanup = true
, printStats = true
}
in
()
