include "options-config.mc"
include "options-type.mc"
include "assoc.mc"
include "tuning/tune-options.mc"

let tuneOptionsConfig : ParseConfig Options = concat optionsConfig [
  ([("--verbose", "", "")],
    "Print the search state during tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with verbose = true}}),
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
  ([("--args", " ", "<s>")],
    "Command line arguments (space-separated) to provide to the the tuned program. Note that several inputs can be given by providing several --args.",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with args = snoc to.args p.str}}),
  ([("--epsilon-ms", " ", "<n>")],
    join ["Threshold value for execution time difference (default ",
          float2string tuneOptionsDefault.epsilonMs, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with epsilonMs = argToFloatMin p 0.0}}),
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
      {o with tuneOptions = {to with seed = Some (argToInt p)}}),
  ([("--dependency-analysis", "", "")],
    "Perform dependency analysis",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with dependencyAnalysis = true}}),
  ([("--debug-dependency-analysis", "", "")],
    "Debug dependency analysis",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with debugDependencyAnalysis = true}}),
  ([("--debug-instrumentation", "", "")],
    "Debug instrumentation",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with debugInstrumentation = true}}),
  ([("--debug-expansion", "", "")],
    "Debug context expansion",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with debugExpansion = true}}),
  ([("--reduce-dependencies", " ", "<t>")],
    join ["Reduce the dependency graph by filtering out measuring points with runtimes below this threshold value (default ",
          float2string tuneOptionsDefault.reduceDependencies, ")"],
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with reduceDependencies = argToFloatMin p 0.0}}),
  ([("--print-stats", "", "")],
    "Output detailed information about measuring points",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with printStats = true}}),
  ([("--enable-cleanup", "", "")],
    "Clean up tune file after tuning",
    lam p: ArgPart Options.
      let o: Options = p.options in
      let to : TuneOptions = o.tuneOptions in
      {o with tuneOptions = {to with cleanup = true}})

]
