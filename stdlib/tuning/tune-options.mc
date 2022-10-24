include "option.mc"

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
, seqTransform : Bool
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
, dependencyAnalysis = false
, debugDependencyAnalysis = false
, debugInstrumentation = false
, debugExpansion = false
, seqTransform = false
, reduceDependencies = 0.0
, cleanup = false
, printStats = false
}
