include "options-config.mc"
include "options-type.mc"
include "assoc.mc"

type SearchMethod
con SimulatedAnnealing : Unit -> SearchMethod
con TabuSearch         : Unit -> SearchMethod
con RandomWalk         : Unit -> SearchMethod
con Exhaustive         : Unit -> SearchMethod
con SemiExhaustive     : Unit -> SearchMethod
con BinarySearch       : Unit -> SearchMethod

type TuneOptions =
{ debug : Bool
, iters : Int
, timeoutMs : Option Float
, warmups : Int
, method : SearchMethod
, input : [[String]]
, saInitTemp : Float
, saDecayFactor : Float
, tabuSize : Int
, epsilonMs : Float
, stepSize : Int
, ignoreErrors : Bool
, exitEarly : Bool
, seed : Option Int
}

let tuneOptionsDefault : TuneOptions =
{ debug = false
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
}

let tuneSearchMethodMap =
[ ("simulated-annealing", SimulatedAnnealing {})
, ("tabu-search", TabuSearch {})
, ("random-walk", RandomWalk {})
, ("exhaustive", Exhaustive {})
, ("semi-exhaustive", SemiExhaustive {})
, ("binary-search", BinarySearch {})
]

let tuneOptionsConfig : ParseConfig = concat optionsConfig [
  ([("--debug", "", "")],
    "Debug the tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with debug = true}}),
  ([("--iters", " ", "<n>")],
    "Maximum number of iterations to perform before exiting the search",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with iters = argToIntMin p 0}}),
  ([("--timeout-ms", " ", "<ms>")],
    "Maximum time in ms to conduct the tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with timeoutMs = Some (argToFloatMin p 0.0)}}),
  ([("--warmups", " ", "<n>")],
    "Number of warmup iterations before starting tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with warmups = argToIntMin p 0}}),
  ([("--method", " ", "<method>")],
    concat "Search method, one of "
      (join ["{", strJoin ", " (assocKeys {eq=eqString} tuneSearchMethodMap), "}"]),
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      match assocLookup {eq=eqString} p.str tuneSearchMethodMap
      with Some method then
        {o with tuneOptions = {to with method = method}}
      else
        modref p.fail (Some (ParseTypeGeneric ("Unknown search method", p.str)));
        o),
  ([("--input", " ", "<s>")],
    "Input data to the tuned program. Note that several inputs can be given by providing several --input",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with input = cons to.input p.str}}),
  ([("--sa-init-temp", " ", "<t>")],
    join ["If --method simulated-annealing is used, this gives the initial temperature (default ",
          float2string tuneOptionsDefault.saInitTemp, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with saInitTemp = argToFloatMin p 0.0}}),
  ([("--sa-decay-factor", " ", "<d>")],
    join ["If --method simulated-annealing is used, this gives the decay factor (default ",
          float2string tuneOptionsDefault.saDecayFactor, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with saDecayFactor = argToFloatMin p 0.0}}),
  ([("--tabu-size", " ", "<n>")],
    join ["If --method tabu-search is used, this gives the number of configurations to keep in the tabu list (default ",
          int2string tuneOptionsDefault.tabuSize, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with tabuSize = argToIntMin p 0}}),
  ([("--step-size", " ", "<n>")],
    join ["Step size for integer ranges (default ",
          int2string tuneOptionsDefault.stepSize, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with stepSize = argToIntMin p 0}}),
  ([("--ignore-errors", "", "")],
    "Ignore errors during tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with ignoreErrors = true}}),
  ([("--disable-exit-early", "", "")],
    "Let the process run to completion during tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with exitEarly = false}}),
  ([("--seed", " ", "<n>")],
    "Set the seed for random search",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with seed = argToInt p}})
]
