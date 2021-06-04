include "string.mc"

-- Options for tuning

-- TODO(Linnea, 2021-05-18): Naive implementation of tuning options before we
-- have an argparser

type TuneOptions =
{ debug : Bool          -- Whether to do debug prints during search
, iters : Int           -- Number of search iterations
, warmups : Int         -- Number of warmup runs
, method : SearchMethod -- Search method
, input : [[String]]    -- Input data
, saInitTemp : Float    -- Initial temperature for simulated annealing
, saDecayFactor : Float -- Decay factor for simulated annealing
, tabuSize : Int        -- Maximum size of tabu set
-- , epsilonMs : Float     -- Precision of time measurement
}

type SearchMethod
con SimulatedAnnealing : Unit -> SearchMethod
con TabuSearch         : Unit -> SearchMethod
con RandomWalk         : Unit -> SearchMethod
con SemiExhaustive     : Unit -> SearchMethod

let string2SearchMethod : String -> SearchMethod = lam s.
  match s with "simulated-annealing" then SimulatedAnnealing {}
  else match s with "tabu-search" then TabuSearch {}
  else match s with "random-walk" then RandomWalk {}
  else match s with "semi-exhaustive" then SemiExhaustive {}
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
}

recursive let parseTuneOptions = lam o : TuneOptions. lam args : [String].
  match args with [] then o

  else match args with ["--debug-tune"] ++ args then
    parseTuneOptions {o with debug = true} args

  else match args with ["--iters"] ++ args then
    match args with [i] ++ args then
      let iters = string2int i in
      if geqi iters 0 then
        parseTuneOptions {o with iters = string2int i} args
      else error "iters cannot be negative"
    else error "--iters with no argument"

  else match args with ["--warmups"] ++ args then
    match args with [i] ++ args then
      let warmups = string2int i in
      if geqi warmups 0 then
        parseTuneOptions {o with warmups = string2int i} args
      else error "warmups cannot be negative"
    else error "--warmups with no argument"

  else match args with ["--method"] ++ args then
    match args with [m] ++ args then
      parseTuneOptions {o with method = string2SearchMethod m} args
    else error "--method with no argument"

  else match args with ["--input"] ++ args then
    match args with [a] ++ args then
      parseTuneOptions {o with input = cons (strSplit " " a) o.input} args
    else error "--input with no argument"

  else match args with ["--saInitTemp"] ++ args then
    match args with [a] ++ args then
      let temp = string2float a in
      if geqf temp 0.0 then
        parseTuneOptions {o with saInitTemp = string2float a} args
      else error "temperature cannot be negative"
    else error "--saInitTemp with no argument"

  else match args with ["--saDecayFactor"] ++ args then
    match args with [a] ++ args then
      let decay = string2float a in
      if geqf decay 0.0 then
        parseTuneOptions {o with saDecayFactor = string2float a} args
      else error "decay cannot be negative"
    else error "--saDecayFactor with no argument"

  else match args with ["--tabuSize"] ++ args then
    match args with [a] ++ args then
      let size = string2int a in
      if geqi size 1 then
        parseTuneOptions {o with tabuSize = string2int a} args
      else error "tabu size must be at least 1"
    else error "--tabuSize with no argument"

  else match args with [a] ++ args then
    error (concat "Unknown tune option: " a)

  else never
end
