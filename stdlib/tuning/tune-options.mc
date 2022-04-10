include "option.mc"

type SearchMethod
con SimulatedAnnealing : () -> SearchMethod
con TabuSearch         : () -> SearchMethod
con RandomWalk         : () -> SearchMethod
con Exhaustive         : () -> SearchMethod
con SemiExhaustive     : () -> SearchMethod
con BinarySearch       : () -> SearchMethod

let tuneSearchMethodMap =
[ ("simulated-annealing", SimulatedAnnealing {})
, ("tabu-search", TabuSearch {})
, ("random-walk", RandomWalk {})
, ("exhaustive", Exhaustive {})
, ("semi-exhaustive", SemiExhaustive {})
, ("binary-search", BinarySearch {})
]

-- Options for tuning
type TuneOptions =
{ verbose : Bool
, iters : Int
, timeoutMs : Option Float
, warmups : Int
, method : SearchMethod
, input : [String]
, saInitTemp : Float
, saDecayFactor : Float
, tabuSize : Int
, epsilonMs : Float
, stepSize : Int
, ignoreErrors : Bool
, exitEarly : Bool
, seed : Option Int
, dependencyAnalysis : Bool
, cleanup : Bool
}

-- Default options
let tuneOptionsDefault : TuneOptions =
{ verbose = false
, iters = 10
, timeoutMs = None ()
, warmups = 1
, method = RandomWalk ()
, input = []
, saInitTemp = 100.0
, saDecayFactor = 0.95
, tabuSize = 10
, epsilonMs = 10.0
, stepSize = 1
, ignoreErrors = false
, exitEarly = true
, seed = None ()
, dependencyAnalysis = false
, cleanup = false
}
