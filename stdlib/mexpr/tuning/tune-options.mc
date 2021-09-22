include "string.mc"

-- Options for tuning

type TuneOptions =
{ debug : Bool          -- Whether to do debug prints during search
, iters : Int           -- Number of search iterations
, warmups : Int         -- Number of warmup runs
, method : SearchMethod -- Search method
, input : [[String]]    -- Input data
, saInitTemp : Float    -- Initial temperature for simulated annealing
, saDecayFactor : Float -- Decay factor for simulated annealing
, tabuSize : Int        -- Maximum size of tabu set
, epsilonMs : Float     -- Precision of time measurement
, stepSize : Int        -- Step size in int range
, ignoreErrors : Bool   -- Ignore errors during tuning
, exitEarly : Bool      -- Exit process upon timeout (might speed up tuning)
}

type SearchMethod
con SimulatedAnnealing : Unit -> SearchMethod
con TabuSearch         : Unit -> SearchMethod
con RandomWalk         : Unit -> SearchMethod
con Exhaustive         : Unit -> SearchMethod
con SemiExhaustive     : Unit -> SearchMethod
con BinarySearch       : Unit -> SearchMethod

let string2SearchMethod : String -> SearchMethod = lam s.
  match s with "simulated-annealing" then SimulatedAnnealing {}
  else match s with "tabu-search" then TabuSearch {}
  else match s with "random-walk" then RandomWalk {}
  else match s with "exhaustive" then Exhaustive {}
  else match s with "semi-exhaustive" then SemiExhaustive {}
  else match s with "binary-search" then BinarySearch {}
  else error (concat "Unknown search method: " s)

let tuneOptionsDefault : TuneOptions =
{ debug = false
, iters = 10
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
}

let tuneMenu =
"
Usage: mi tune [<options>] file [-- [<tune-options>]]

Options:
  --help                    Print this message and exit
  --debug-parse             Print the AST after parsing
  --debug-generate          Print the AST after code generation
  --exit-before             Exit before evaluation or compilation
  --test                    Generate utest code
  --disable-optimizations   Disables optimizations to decrease compilation time
  --tuned                   Use values from tuning during compilation
  --enable-seq-transform    Transform sequence literals into using decision points
  -- <tune-options>         Tuning options follow the --

Tune options (after -- ):
  --verbose                 Print status during search
  --iters <n>               Maximum number of search iterations (default 10)
  --warmups <n>             Number of warmup runs before search begins
                            (default 1)
  --method <search-method>  Search method (default random-walk)
  --input <s>               Input data to the tuned program. Input with
                            whitespace must be quoted, e.g.
                            --input \"compile src/main/mi.mc\". Note that
                            several input data can be given by providing
                            several --input.
  --epsilon-ms <ms>         The epsilon in ms used for time measurement. E.g.,
                            --epsilon-ms 10.0 means that two measurements that
                            differ with <= 10.0 ms will be considered equal
                            (deafult 10.0)
  --sa-init-temperature <t> If --method simulated-annealing is used, this gives
                            the initial temperature (default 100.0)
  --sa-decay-factor <d>     If --method simulated-annealing is used, this gives
                            the decay factor (default 0.95)
  --tabu-size <n>           If --method tabu-search is used, this gives the
                            number of configufations to keep in the tabu list.
  --step-size <n>.          If --method semi-exhaustive is used, use this as step
                            size for integer ranges. TODO: should be number of steps
  --ignore-errors           Ignore errors during tuning.
  --disable-exit-early      Always let the process run to completion during
                            tuning (default is to kill it when it has run for
                            longer than the current best runtime.)

Search methods (after --method):
   random-walk              Each decision point is assigned a value from its
                            domain uniformly at random in each iteration.
   exhaustive               Explore the search space exhaustively
   semi-exhaustive          Try all values of each decision point one at a time,
                            from left to right, keeping the best assignments
                            so far
   simulated-annealing      Use simulated annealing (see options
                            --sa-init-temperature and --sa-decay-factor)
   tabu-search              Use tabu-search (see option --tabu-size)
   binary-search            Use binary search
"

recursive let parseTuneOptions = lam o : TuneOptions. lam args : [String].
  match args with [] then o

  else match args with ["--verbose"] ++ args then
    parseTuneOptions {o with debug = true} args

  else match args with ["--ignore-errors"] ++ args then
    parseTuneOptions {o with ignoreErrors = true} args

  else match args with ["--disable-exit-early"] ++ args then
    parseTuneOptions {o with exitEarly = false} args

  else match args with ["--iters"] ++ args then
    match args with [i] ++ args then
      let iters = string2int i in
      if geqi iters 0 then
        parseTuneOptions {o with iters = string2int i} args
      else error "iters cannot be negative"
    else error "--iters without an argument"

  else match args with ["--warmups"] ++ args then
    match args with [i] ++ args then
      let warmups = string2int i in
      if geqi warmups 0 then
        parseTuneOptions {o with warmups = string2int i} args
      else error "warmups cannot be negative"
    else error "--warmups without an argument"

  else match args with ["--method"] ++ args then
    match args with [m] ++ args then
      parseTuneOptions {o with method = string2SearchMethod m} args
    else error "--method without an argument"

  else match args with ["--input"] ++ args then
    match args with [a] ++ args then
      parseTuneOptions {o with input = cons (strSplit " " a) o.input} args
    else error "--input without an argument"

  else match args with ["--sa-init-temp"] ++ args then
    match args with [a] ++ args then
      let temp = string2float a in
      if geqf temp 0.0 then
        parseTuneOptions {o with saInitTemp = string2float a} args
      else error "temperature cannot be negative"
    else error "--sa-init-temp without an argument"

  else match args with ["--sa-decay-factor"] ++ args then
    match args with [a] ++ args then
      let decay = string2float a in
      if geqf decay 0.0 then
        parseTuneOptions {o with saDecayFactor = string2float a} args
      else error "decay cannot be negative"
    else error "--sa-decay-factor without an argument"

  else match args with ["--tabu-size"] ++ args then
    match args with [a] ++ args then
      let size = string2int a in
      if geqi size 1 then
        parseTuneOptions {o with tabuSize = size} args
      else error "tabu size must be at least 1"
    else error "--tabu-size without an argument"

  else match args with ["--epsilon-ms"] ++ args then
    match args with [a] ++ args then
      let eps = string2float a in
      if geqf eps 0.0 then
        parseTuneOptions {o with epsilonMs = eps} args
      else error "epsilon-ms cannot be negative"
    else error "--epsilon-ms without an argument"

else match args with ["--step-size"] ++ args then
match args with [a] ++ args then
let step = string2int a in
if geqi step 0 then
parseTuneOptions {o with stepSize = step} args
else error "step-size cannot be negative"
else error "--step-size without an argument"

  else match args with [a] ++ args then
    error (concat "Unknown tune option: " a)

  else never
end
