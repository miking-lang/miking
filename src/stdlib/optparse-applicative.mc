-- This file implements an argument parser using an applicative
-- interface, inspired by (but with many less features than)
-- https://hackage.haskell.org/package/optparse-applicative

-- The key idea of the interface is to have a central type `OptParser
-- a` that represents a set of options that can be parsed from a
-- commandline to produce a value of type `a`. This type is a functor
-- (via `optMap`), an applicative (via `optPure` and `optApply`), and
-- supports alternatives (via `optOr`). Parsing a command line is done
-- with `optParse`, and an auto-generated `--help` command can be
-- added with `optParserWithHelp`. For examples, see the tests at the
-- end of the file.

-- TODO(vipa, 2025-03-28): Some features missing from this library
-- that are present in the Haskell package seem particularly
-- interesting to port:
-- * Subcommands (e.g., `eval` and `compile` for `mi`).
-- * Automatic generation of auto-complete interfaces.

include "common.mc"
include "option.mc"
include "either.mc"
include "seq.mc"
include "string.mc"
include "map.mc"

type OptName
con OptShort : Char -> OptName
con OptLong : String -> OptName

let eqOptName : OptName -> OptName -> Bool
  = lam a. lam b. switch (a, b)
    case (OptShort a, OptShort b) then eqc a b
    case (OptLong a, OptLong b) then eqString a b
    case _ then false
    end

let optNameToStr : OptName -> String
  = lam a. switch a
    case OptShort c then ['-', c]
    case OptLong str then concat "--" str
    end

type OptReader a
con OptWithArg : all a. {names : [OptName], parse : String -> Either String a} -> OptReader a
con OptNoArg : all a. {names : [OptName], value : a} -> OptReader a
con OptPositional : all a. {parse : String -> Either String a} -> OptReader a

-- NOTE(vipa, 2025-04-11): This kind of option is experimental, and
-- notably absent from the original Haskell library. Normal options
-- with arguments match regardless of the shape of their arguments,
-- but can raise an error if the argument is malformed. A "Specific"
-- option can check its argument to determine if it should match, but
-- cannot raise an error if it is malformed. For example, given a
-- "Specific" option with short name "-x" that only matches the
-- argument "true", means that the command line "-x" raises "-x
-- requires an argument" and "-x false" raises "unexpected option -x".
con OptWithSpecificArg : all a. {names : [OptName], parse : String -> Option a} -> OptReader a

type OptItem a =
  { reader : OptReader a
  , shortForm : String
  , description : String
  , category : String
  }

type OptParser a
con NilP : all a. a -> OptParser a
con OptP : all a. OptItem a -> OptParser a
con AltP : all a. (OptParser a, OptParser a) -> OptParser a
-- NOTE(vipa, 2025-03-26): We don't actually handle existentials
-- properly, when we pattern match on `MultP` or `BindP` the `x` will
-- be instantiated to *anything*, instead of some unknowable type. Be
-- *very* cautious when unwrapping it.
con MultP : all x. all a. (OptParser (x -> a), OptParser x) -> OptParser a
con BindP : all x. all a. (OptParser x, x -> OptParser a) -> OptParser a

let optPure
  : all a. a -> OptParser a
  = lam a. NilP a

let _optItemMap : all a. all b. (a -> b) -> OptItem a -> OptItem b
  = lam f. lam o.
    { reader = switch o.reader
      case OptWithArg x then
        OptWithArg {names = x.names, parse = lam s. eitherMapRight f (x.parse s)}
      case OptWithSpecificArg x then
        OptWithSpecificArg {names = x.names, parse = lam s. optionMap f (x.parse s)}
      case OptNoArg x then
        OptNoArg {names = x.names, value = f x.value}
      case OptPositional x then
        OptPositional {parse = lam s. eitherMapRight f (x.parse s)}
      end
    , shortForm = o.shortForm
    , description = o.description
    , category = o.category
    }

recursive let optMap
  : all a. all b. (a -> b) -> OptParser a -> OptParser b
  = lam f. lam p. switch p
    case NilP o then NilP (f o)
    case OptP o then OptP (_optItemMap f o)
    case AltP (a, b) then AltP (optMap f a, optMap f b)
    case MultP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser (Never -> a) = a in
      MultP (optMap (lam f2. lam x. f (f2 x)) a, b)
    case BindP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser Never = a in
      BindP (a, lam x. optMap f (b x))
    end
end

let optApply
  : all a. all b. OptParser (a -> b) -> OptParser a -> OptParser b
  = lam f. lam a.
    MultP (f, a)

let optOr
  : all a. OptParser a -> OptParser a -> OptParser a
  = lam a. lam b. AltP (a, b)

let optOptional : all a. OptParser a -> OptParser (Option a)
  = lam o. optOr (optMap (lam x. Some x) o) (optPure (None ()))

type OptParserM a = all x. (a -> OptParser x) -> OptParser x

let _optPureM : all a. a -> OptParserM a
  = lam x.
    let f : all x. (a -> OptParser x) -> OptParser x = lam k. k x in
    #frozen"f"

let _optBindM : all a. all b. OptParserM a -> (a -> OptParserM b) -> OptParserM b
  = lam f. lam g.
    let ret = lam k. f (lam x. let g = g x in g k) in
    #frozen"ret"

let _optMapM : all a. all b. (a -> b) -> OptParserM a -> OptParserM b
  = lam f. lam a.
    _optBindM #frozen"a" (lam a. _optPureM (f a))

let _optMap2M : all a. all b. all c. (a -> b -> c) -> OptParserM a -> OptParserM b -> OptParserM c
  = lam f. lam a. lam b.
    _optBindM #frozen"a" (lam a. _optBindM #frozen"b" (lam b. _optPureM (f a b)))

let _optFromM : all a. OptParserM a -> OptParser a
  = lam f. f optPure

let _optOneM : all a. OptParser a -> OptParserM a
  = lam a.
    let f = lam k. BindP (a, k) in
    #frozen"f"

recursive let _optManyM : all a. OptParser a -> OptParserM [a]
  = lam p. _optBindM (_optOneM (optOptional p))
    (optionMapOrElse (lam. _optPureM [])
      (lam x. _optMapM (cons x) (_optManyM p)))
end

let _optSomeM : all a. OptParser a -> OptParserM [a]
  = lam p. _optMap2M cons (_optOneM p) (_optManyM p)

let optMany : all a. OptParser a -> OptParser [a] = lam p. _optFromM (_optManyM p)
let optSome : all a. OptParser a -> OptParser [a] = lam p. _optFromM (_optSomeM p)

let optMap2
  : all a. all b. all c. (a -> b -> c) -> OptParser a -> OptParser b -> OptParser c
  = lam f. lam a. lam b. optApply (optMap f a) b

let optMap3
  : all a. all b. all c. all d. (a -> b -> c -> d) -> OptParser a -> OptParser b -> OptParser c -> OptParser d
  = lam f. lam a. lam b. lam c. optApply (optApply (optMap f a) b) c

let optMap4
  : all a. all b. all c. all d. all e. (a -> b -> c -> d -> e) -> OptParser a -> OptParser b -> OptParser c -> OptParser d -> OptParser e
  = lam f. lam a. lam b. lam c. lam d. optApply (optApply (optApply (optMap f a) b) c) d

let optMap5
  : all a. all b. all c. all d. all e. all f. (a -> b -> c -> d -> e -> f) -> OptParser a -> OptParser b -> OptParser c -> OptParser d -> OptParser e -> OptParser f
  = lam f. lam a. lam b. lam c. lam d. lam e. optApply (optApply (optApply (optApply (optMap f a) b) c) d) e

let optApply2
  : all a. all b. all c. OptParser (a -> b -> c) -> OptParser a -> OptParser b -> OptParser c
  = lam f. lam a. lam b. optApply (optApply f a) b

let optApply3
  : all a. all b. all c. all d. OptParser (a -> b -> c -> d) -> OptParser a -> OptParser b -> OptParser c -> OptParser d
  = lam f. lam a. lam b. lam c. optApply (optApply (optApply f a) b) c

let optApply4
  : all a. all b. all c. all d. all e. OptParser (a -> b -> c -> d -> e) -> OptParser a -> OptParser b -> OptParser c -> OptParser d -> OptParser e
  = lam f. lam a. lam b. lam c. lam d. optApply (optApply (optApply (optApply f a) b) c) d

let optApply5
  : all a. all b. all c. all d. all e. all f. OptParser (a -> b -> c -> d -> e -> f) -> OptParser a -> OptParser b -> OptParser c -> OptParser d -> OptParser e -> OptParser f
  = lam f. lam a. lam b. lam c. lam d. lam e. optApply (optApply (optApply (optApply (optApply f a) b) c) d) e

let optArgDef : all x. {long : String, short : String, parse : String -> x, arg : String, description : String, category : String} =
  { long = ""
  , short = ""
  , parse = lam. error "No parser specified for optArgDef"
  , arg = "ARG"
  , description = ""
  , category = ""
  }
let optArgDefString =
  { optArgDef with parse = lam str.
    Right str
  , arg = "ARG"
  }
let optArgDefInt =
  { optArgDef with parse = lam str.
    if stringIsInt str then Right (string2int str) else Left "not an integer"
  , arg = "INT"
  }
let optArgDefFloat =
  { optArgDef with parse = lam str.
    if stringIsFloat str then Right (string2float str) else Left "not a float"
  , arg = "FLOAT"
  }
let optArg : all a. {long : String, short : String, parse : String -> Either String a, arg : String, description : String, category : String} -> OptParser a = lam conf.
  let names = map (lam c. OptShort c) conf.short in
  let names = if null conf.long
    then names
    else cons (OptLong conf.long) names in
  let shortForm = match names with [name] ++ _
    then join [optNameToStr name, " ", conf.arg]
    else error "optArg called with neither 'long' nor 'short'" in
  OptP
  { reader = OptWithArg
    { names = names
    , parse = conf.parse
    }
  , shortForm = shortForm
  , description = conf.description
  , category = conf.category
  }
let optExactArg = lam str.
  { optArgDef with arg = str
  , parse = lam other.
    if eqString str other then Some () else None ()
  }
let optSpecificArg : all a. {long : String, short : String, parse : String -> Option a, arg : String, description : String, category : String} -> OptParser a = lam conf.
  let names = map (lam c. OptShort c) conf.short in
  let names = if null conf.long
    then names
    else cons (OptLong conf.long) names in
  let shortForm = match names with [name] ++ _
    then join [optNameToStr name, " ", conf.arg]
    else error "optSpecificArg called with neither 'long' nor 'short'" in
  OptP
  { reader = OptWithSpecificArg
    { names = names
    , parse = conf.parse
    }
  , shortForm = shortForm
  , description = conf.description
  , category = conf.category
  }

let optNoArgDef : all a. a -> {long : String, short : String, value : a, description : String, category : String} = lam value.
  { long = ""
  , short = ""
  , value = value
  , description = ""
  , category = ""
  }
let optNoArg : all a. {long : String, short : String, value : a, description : String, category : String} -> OptParser a = lam conf.
  let names = map (lam c. OptShort c) conf.short in
  let names = if null conf.long
    then names
    else cons (OptLong conf.long) names in
  let shortForm = match names with [name] ++ _
    then optNameToStr name
    else error "optNoArg called with neither 'long' nor 'short'" in
  OptP
  { reader = OptNoArg
    { names = names
    , value = conf.value
    }
  , shortForm = shortForm
  , description = conf.description
  , category = conf.category
  }

let optFlagDef =
  { long = ""
  , short = ""
  , description = ""
  , category = ""
  }
let optFlag = lam conf.
  let names = map (lam c. OptShort c) conf.short in
  let names = if null conf.long
    then names
    else cons (OptLong conf.long) names in
  let shortForm = match names with [name] ++ _
    then optNameToStr name
    else error "optNoArg called with neither 'long' nor 'short'" in
  let present = OptP
    { reader = OptNoArg
      { names = names
      , value = true
      }
    , shortForm = shortForm
    , description = conf.description
    , category = conf.category
    } in
  optOr present (optPure false)

let optPosDef : all a. {parse : String -> Either String a, arg : String, description : String, category : String} =
  { parse = lam. error "No parse function given to optPosDef"
  , arg = "ARG"
  , description = ""
  , category = ""
  }
let optPosDefString =
  { optPosDef with parse = lam str. Right str
  }
let optPos : all a. {parse : String -> Either String a, arg : String, description : String, category : String} -> OptParser a
  = lam conf. OptP
    { reader = OptPositional {parse = conf.parse}
    , shortForm = conf.arg
    , description = conf.description
    , category = conf.category
    }

type OptMissing
con OptMissingOpt : String -> OptMissing
con OptMissingMult : [OptMissing] -> OptMissing
con OptMissingAlt : [OptMissing] -> OptMissing

let _optMissingMult : OptMissing -> OptMissing -> OptMissing
  = lam a. lam b. switch (a, b)
    case (OptMissingMult [], x) | (x, OptMissingMult []) then x
    case (OptMissingMult as, OptMissingMult bs) then OptMissingMult (concat as bs)
    case (OptMissingMult as, a) then OptMissingMult (snoc as a)
    case (b, OptMissingMult bs) then OptMissingMult (cons b bs)
    case (a, b) then OptMissingMult [a, b]
    end

let _optMissingAlt : OptMissing -> OptMissing -> OptMissing
  = lam a. lam b. switch (a, b)
    case (OptMissingAlt as, OptMissingAlt bs) then OptMissingAlt (concat as bs)
    case (OptMissingAlt as, a) then OptMissingAlt (snoc as a)
    case (b, OptMissingAlt bs) then OptMissingAlt (cons b bs)
    case (a, b) then OptMissingAlt [a, b]
    end

recursive let _optMissingToString : OptMissing -> String
  = lam o.
    let mWithParens = lam o. match o with OptMissingAlt _
      then snoc (cons '(' (_optMissingToString o)) ')'
      else _optMissingToString o in
    switch o
    case OptMissingOpt str then str
    case OptMissingMult ms then strJoin " " (map mWithParens ms)
    case OptMissingAlt ms then strJoin " | " (map _optMissingToString ms)
    end
end

recursive let optParserEval
  : all w. all a. OptParser a -> Either OptMissing a
  = lam p. switch p
    case NilP a then Right a
    case OptP x then
      Left (OptMissingOpt x.shortForm)
    case AltP (a, b) then
      switch (optParserEval a, optParserEval b)
      case (Right x, _) | (_, Right x) then Right x
      case (Left a, Left b) then Left (_optMissingAlt a b)
      end
    case MultP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser (Never -> a) = a in
      switch (optParserEval a, optParserEval b)
      case (Right a, Right b) then Right (a b)
      case (Left a, Left b) then Left (_optMissingMult a b)
      case (Left x, _) | (_, Left x) then Left x
      end
    case BindP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser Never = a in
      switch optParserEval a
      case Right a then optParserEval (b a)
      case Left x then Left x
      end
    end
end

type ParserSearchRet r
con PSROk : all r. ([String], OptParser r) -> ParserSearchRet r
con PSRNotFound : all r. () -> ParserSearchRet r
con PSRError : all r. String -> ParserSearchRet r

recursive let _searchParser
  : all a. (all r. OptItem r -> ParserSearchRet r) -> OptParser a -> ParserSearchRet a
  = lam f. lam p. switch p
    case NilP _ then PSRNotFound ()
    case OptP o then f o
    case AltP (a, b) then
      switch (_searchParser #frozen"f" a, _searchParser #frozen"f" b)
      case (PSROk (args, a), PSROk (_, b)) then
        PSROk (args, AltP (a, b))
      case (res & PSRError _, _) | (_, res & PSRError _) then
        res
      case (res & PSROk _, _) | (_, res & PSROk _) then
        res
      case (PSRNotFound _, PSRNotFound _) then
        PSRNotFound ()
      end
    case MultP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser (Never -> a) = a in
      switch _searchParser #frozen"f" a
      case PSROk (args, a) then
        PSROk (args, optApply a b)
      case PSRNotFound _ then
        switch _searchParser #frozen"f" b
        case PSROk (args, b) then
          PSROk (args, optApply a b)
        case PSRNotFound _ then
          PSRNotFound ()
        case PSRError err then
          PSRError err
        end
      case PSRError err then
        PSRError err
      end
    case BindP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser Never = a in
      switch _searchParser #frozen"f" a
      case PSROk (args, a) then
        PSROk (args, BindP (a, b))
      case PSRNotFound _ then
        match optParserEval a with Right a then
          _searchParser #frozen"f" (b a)
        else PSRNotFound ()
      case PSRError err then
        PSRError err
      end
    end
end

type OptParseMode
con OPMBoth : () -> OptParseMode
con OPMPositional : () -> OptParseMode

let _processOpt : all r. OptName -> [String] -> OptItem r -> ParserSearchRet r
  = lam name. lam args. lam item. switch item.reader
    case OptWithArg x then
      if seqMem eqOptName x.names name then
        match args with [arg] ++ args then
          switch x.parse arg
          case Left err then
            PSRError (join ["Option '", optNameToStr name, "' was given a malformed argument: ", err])
          case Right a then
            PSROk (args, NilP a)
          end
        else PSRError (join ["Option '", optNameToStr name, "' requires an argument."])
      else PSRNotFound ()
    case OptWithSpecificArg x then
      if seqMem eqOptName x.names name then
        match args with [arg] ++ args then
          match x.parse arg with Some a then
            PSROk (args, NilP a)
          else PSRNotFound ()
        else PSRError (join ["Option '", optNameToStr name, "' requires an argument."])
      else PSRNotFound ()
    case OptNoArg x then
      if seqMem eqOptName x.names name then
        PSROk (args, NilP x.value)
      else PSRNotFound ()
    case OptPositional _ then
      PSRNotFound ()
    end

let _processPos : all r. String -> [String] -> OptItem r -> ParserSearchRet r
  = lam arg. lam args. lam item. switch item.reader
    case OptPositional x then
      switch x.parse arg
      case Left err then
        PSRError (join ["Could not parse positional argument: ", err])
      case Right a then
        PSROk (args, NilP a)
      end
    case OptWithArg _ | OptWithSpecificArg _ | OptNoArg _ then
      PSRNotFound ()
    end

let _optStepParser
  : all a. OptParseMode -> String -> [String] -> OptParser a -> (OptParseMode, ParserSearchRet a)
  = lam mode. lam arg. lam args. lam p.
    switch (mode, arg)
    case (OPMBoth _, "--") then (OPMPositional (), PSROk (args, p))
    case (OPMBoth _, "--" ++ long) then
      let name = OptLong long in
      let f = lam item. _processOpt name args item in
      (mode, _searchParser #frozen"f" p)
    case (OPMBoth _, "-" ++ shorts) then
      recursive let work = lam args. lam p. lam names.
        match names with [n] ++ names then
          let name = OptShort n in
          let f = lam item. _processOpt name args item in
          switch _searchParser #frozen"f" p
          case PSROk (args, p) then work args p names
          case res & (PSRError _ | PSRNotFound _) then res
          end
        else PSROk (args, p)
      in
      (mode, work args p shorts)
    case (_, positional) then
      let f = lam item. _processPos positional args item in
      (mode, _searchParser #frozen"f" p)
    end

type OptParseResult a
con OptParseOk : all a. a -> OptParseResult a
con OptParseMissing : all a. OptMissing -> OptParseResult a
con OptParseError : all a. String -> OptParseResult a

let optParse
  : all a. all w. OptParser a -> [String] -> Either String a
  = lam p. lam args.
    recursive let work = lam mode. lam args. lam p.
      match args with [arg] ++ args then
        switch _optStepParser mode arg args p
        case (mode, PSROk (args, p)) then
          work mode args p
        case (_, PSRNotFound _) then
          Left (join ["Unexpected argument '", arg, "'"])
        case (_, PSRError err) then
          Left err
        end
      else switch optParserEval p
        case Left missing then
          Left (concat "Missing argument(s):\n" (_optMissingToString missing))
        case Right a then
          Right a
        end
    in work (OPMBoth ()) args p

type DescTree
type OptDesc = {shortForm : String, description : String, category : String}
con DescTreeOpt : OptDesc -> DescTree
con DescTreeMult : [DescTree] -> DescTree
con DescTreeAlt : {alts : [DescTree], optional : Bool} -> DescTree
con DescTreeBind : DescTree -> DescTree

let _optDescTreeMult : DescTree -> DescTree -> DescTree
  = lam a. lam b. switch (a, b)
    case (DescTreeAlt {alts = []}, dt) | (dt, DescTreeAlt {alts = []}) then dt
    case (DescTreeMult [], dt) | (dt, DescTreeMult []) then dt
    case (DescTreeMult as, DescTreeMult bs) then DescTreeMult (concat as bs)
    case (DescTreeMult as, a) then DescTreeMult (snoc as a)
    case (b, DescTreeMult bs) then DescTreeMult (cons b bs)
    case (a, b) then DescTreeMult [a, b]
    end

let _optDescTreeAlt : DescTree -> DescTree -> DescTree
  = lam a. lam b. switch (a, b)
    case (DescTreeAlt as, DescTreeAlt bs) then
      DescTreeAlt {alts = concat as.alts bs.alts, optional = or as.optional bs.optional}
    case (DescTreeAlt as, a) then
      DescTreeAlt {as with alts = snoc as.alts a}
    case (b, DescTreeAlt bs) then
      DescTreeAlt {bs with alts = cons b bs.alts}
    case (a, b) then
      DescTreeAlt {alts = [a, b], optional = false}
    end

recursive let _optDescTreeToString : DescTree -> String
  = lam t.
    let mWithParens = lam o. match o with DescTreeAlt {optional = false}
      then snoc (cons '(' (_optDescTreeToString o)) ')'
      else _optDescTreeToString o in
      switch t
    case DescTreeOpt {shortForm = shortForm} then shortForm
    case DescTreeMult dts then strJoin " " (map mWithParens dts)
    case DescTreeAlt x then
      let res = strJoin " | " (map _optDescTreeToString x.alts) in
      if x.optional then snoc (cons '[' res) ']' else res
    case DescTreeBind x then
      match x with DescTreeMult _
      then concat (cons '(' (_optDescTreeToString x)) ")..."
      else concat (_optDescTreeToString x) "..."
    end
end

recursive let _optDescTreeRemoveUnconditionalOptional : DescTree -> Option DescTree
  = lam dt. switch dt
    case DescTreeOpt _ then Some dt
    case DescTreeMult dts then
      switch mapOption _optDescTreeRemoveUnconditionalOptional dts
      case [] then None ()
      case [dt] then Some dt
      case dts then Some (DescTreeMult dts)
      end
    case DescTreeAlt {alts = [] | [_], optional = true} then None ()
    case DescTreeAlt _ | DescTreeBind _ then Some dt
    end
end

recursive let _optDescGetDescs : DescTree -> [OptDesc]
  = lam dt. switch dt
    case DescTreeOpt desc then
      if null desc.description then [] else [desc]
    case DescTreeMult dts then
      foldl (lam acc. lam dt. concat acc (_optDescGetDescs dt)) [] dts
    case DescTreeAlt x then
      foldl (lam acc. lam dt. concat acc (_optDescGetDescs dt)) [] x.alts
    case DescTreeBind x then
      _optDescGetDescs x
    end
end

let _optDescSplitOnce : DescTree -> [DescTree]
  = lam dt. switch dt
    case DescTreeOpt _ | DescTreeBind _ then [dt]
    case DescTreeMult dts then
      let f : all a. ([a], [a]) -> Option (([a], a, [a]), ([a], [a])) = lam split.
        match split with (pre ++ [here], rest)
        then Some ((pre, here, rest), (pre, cons here rest))
        else None () in
      let complexity = lam dt. match dt with DescTreeAlt {alts = alts}
        then foldl muli 1 (map (lam dt. match dt with DescTreeMult dts then length dts else 1) alts)
        else 1 in
      let foci = unfoldr f (dts, []) in
      let foci = map (lam x. (complexity x.1, x)) foci in
      let mostComplex = max (lam a. lam b. subi a.0 b.0) foci in
      match mostComplex with Some (_, (pre, here, post)) in
      let here = match here with DescTreeAlt x
        then if x.optional then cons (DescTreeMult []) x.alts else x.alts
        else [here] in
      let pre = DescTreeMult pre in
      let post = DescTreeMult post in
      map (lam here. _optDescTreeMult (_optDescTreeMult pre here) post) here
    case DescTreeAlt x then
      if x.optional then cons (DescTreeMult []) x.alts else x.alts
    end

recursive let _describeTree : all a. OptParser a -> DescTree
  = lam p. switch p
    case NilP _ then DescTreeAlt {alts = [], optional = true}
    case OptP x then
      DescTreeOpt {shortForm = x.shortForm, description = x.description, category = x.category}
    case AltP (a, b) then
      let aDesc = _describeTree a in
      let bDesc = _describeTree b in
      _optDescTreeAlt aDesc bDesc
    case MultP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser (Never -> a) = a in
      let aDesc = _describeTree a in
      let bDesc = _describeTree b in
      _optDescTreeMult aDesc bDesc
    case BindP (a, b) then
      -- NOTE(vipa, 2025-03-26): Emulate an existential type by
      -- creating a new empty type
      type Never in
      let a : OptParser Never = a in
      let aDesc = _describeTree a in
      match optParserEval a with Right a
      then DescTreeBind (_optDescTreeMult aDesc (_describeTree (b a)))
      else DescTreeBind aDesc
    end
end

let optParserHelpText : all a. String -> String -> OptParser a -> String
  = lam appName. lam bigDescription. lam p.
    let bigDescription = switch bigDescription
      case "" then ""
      case _ ++ "\n\n" then bigDescription
      case _ ++ "\n" then snoc bigDescription '\n'
      case _ then concat bigDescription "\n\n"
      end in
    let dt = _describeTree p in

    let options = _optDescGetDescs dt in
    -- OPT(vipa, 2025-03-26): `distinct` is quadratic, could reduce to n log n
    let options = distinct
      (lam a. lam b.
        if eqString a.shortForm b.shortForm
        then if eqString a.description b.description
          then eqString a.category b.category
          else false
        else false)
      options in
    let optsToStr = lam options.
      let longest = foldl (lam acc. lam pair. maxi acc (length pair.shortForm)) 0 options in
      let padToLength = lam l. lam str. concat str (make (subi l (length str)) ' ') in
      let optToStr = lam opt. join ["  ", padToLength longest opt.shortForm, " ", opt.description] in
      strJoin "\n" (map optToStr options) in

    let options = foldl (lam m. lam o. mapInsertWith concat o.category [o] m) (mapEmpty cmpString) options in
    let otherOptions = mapLookup "" options in
    let options = mapRemove "" options in
    let options = map (lam pair. join [pair.0, "\n", optsToStr pair.1]) (mapBindings options) in
    let options = switch (options, otherOptions)
      case ([], Some others) then [concat "Options:\n" (optsToStr others)]
      case (opts, Some others) then snoc opts (concat "Other options:\n" (optsToStr others))
      case (opts, None _) then opts
      end in
    let options = strJoin "\n\n" options in

    let dt = _optDescTreeRemoveUnconditionalOptional dt in
    let dts = optionMapOr [] _optDescSplitOnce dt in
    let shortUsage = strJoin "\n" (map (lam dt. join [appName, " ", _optDescTreeToString dt]) dts) in

    join [shortUsage, "\n\n", bigDescription, options]

let optParserWithHelp : all a. String -> String -> OptParser a -> OptParser (Either String a)
  = lam appName. lam bigDescription. lam p.
    let help = optNoArg
      { optNoArgDef (Left (optParserHelpText appName bigDescription p)) with short = "h"
      , long = "help"
      } in
    optOr (optMap (lam x. Right x) p) help

let optParseWithHelp : all a. String -> String -> OptParser a -> [String] -> a
  = lam appName. lam bigDescription. lam p. lam args.
    let p = optParserWithHelp appName bigDescription p in
    switch optParse p args
    case Left err then
      printLn err;
      exit 1
    case Right (Left help) then
      printLn help;
      exit 0
    case Right (Right res) then
      res
    end

mexpr

type Example in
con Ex1 : {shared : Int, opt1 : Bool, extra : Bool} -> Example in
con Ex2 : {shared : Int, opt2 : Int} -> Example in

let shared : OptParser Int = optArg
  { optArgDef with
    long = "shared"
  , short = "s"
  , parse = lam s.
    if stringIsInt s then Right (string2int s) else Left "not an integer"
  , arg = "INT"
  , description = "shared is a thing"
  } in
let parseEx1 : OptParser Example =
  let mk = lam shared. lam opt1. lam extra. Ex1 {shared = shared, opt1 = opt1, extra = extra} in
  let opt1 : OptParser Bool = optNoArg
    { optNoArgDef true with
      long = "opt1"
    , description = "opt1 is here"
    } in
  let opt1 : OptParser Bool = optOr opt1 (optPure false) in
  let extra = optFlag {optFlagDef with long = "extra", description = "extra extra"} in
  optMap3 mk shared opt1 extra in
let parseEx2 : OptParser Example =
  let mk = lam shared. lam opt2. Ex2 {shared = shared, opt2 = opt2} in
  let yes : OptParser Int = optNoArg
    { optNoArgDef 0 with
      long = "yes"
    , description = "yes yes"
    } in
  let no : OptParser Int = optNoArg
    { optNoArgDef 1 with
      long = "no"
    , description = "no no"
    } in
  optApply (optMap mk shared) (optOr yes no) in

let thing : OptParser Float = optArg
  { optArgDef with
    long = "thing"
  , parse = lam s.
    if stringIsFloat s then Right (string2float s) else Left "not an float"
  , arg = "FLOAT"
  , description = "thing is a thing"
  } in

let withCategory : OptParser Bool = optFlag
  { optFlagDef with
    long = "with-category"
  , description = "This flag has a category"
  , category = "Weird flags:"
  } in

let verbose : OptParser Int = optMap length (optMany (optNoArg
  { optNoArgDef () with long = "verbose"
  , description = "verbosity or something"
  })) in

let filename : OptParser String = optPos {optPosDefString with arg = "FILENAME", description = "file and stuff"} in
let parser = optMap4 (lam a. lam b. lam c. lam d. (a, b, c, d)) (optOr parseEx1 parseEx2) thing (optOr filename (optPure "")) verbose in

let test : [String] -> Either String (Example, Float, String, Int)
  = lam args. optParse parser args in

utest test []
with Left "Missing argument(s):\n(--shared INT | --shared INT (--yes | --no)) --thing FLOAT" in

utest test ["--shared"]
with Left "Option '--shared' requires an argument." in

utest test ["--shared", "blue"]
with Left "Option '--shared' was given a malformed argument: not an integer" in

utest test ["--shared", "7", "--thing", "30"]
with Right ((Ex1 {opt1 = false, shared = 7, extra = false}), 30., "", 0) in

utest test ["--shared", "7", "--verbose", "--thing", "30"]
with Right ((Ex1 {opt1 = false, shared = 7, extra = false}), 30., "", 1) in

utest test ["--shared", "7", "--verbose", "--thing", "30", "--verbose"]
with Right ((Ex1 {opt1 = false, shared = 7, extra = false}), 30., "", 2) in

utest test ["--shared", "7", "--opt1", "--thing", "30"]
with Right ((Ex1 {opt1 = true, shared = 7, extra = false}), 30., "", 0) in

utest test ["--shared", "7", "file", "--opt1", "--thing", "30"]
with Right ((Ex1 {opt1 = true, shared = 7, extra = false}), 30., "file", 0) in

utest test ["--opt1", "--shared", "7", "--thing", "30"]
with Right ((Ex1 {opt1 = true, shared = 7, extra = false}), 30., "", 0) in

utest test ["--opt1"]
with Left "Missing argument(s):\n--shared INT --thing FLOAT" in

utest test ["--shared", "7", "--yes", "--thing", "30"]
with Right ((Ex2 {opt2 = 0, shared = 7}), 30., "", 0) in

utest test ["--thing", "42.7", "--shared", "7", "--no"]
with Right ((Ex2 {opt2 = 1, shared = 7}), 42.7, "", 0) in

utest test ["--shared", "7", "--no", "--opt1"]
with Left "Unexpected argument '--opt1'" in

let helpText = strJoin "\n"
  [ "test --shared INT [--opt1] [--extra] --thing FLOAT [--verbose]..."
  , "test --shared INT (--yes | --no) --thing FLOAT [--verbose]..."
  , ""
  , "This thing can do stuff."
  , ""
  , "Options:"
  , "  --shared INT  shared is a thing"
  , "  --opt1        opt1 is here"
  , "  --extra       extra extra"
  , "  --yes         yes yes"
  , "  --no          no no"
  , "  --thing FLOAT thing is a thing"
  , "  FILENAME      file and stuff"
  , "  --verbose     verbosity or something"
  ] in
utest optParserHelpText "test" "This thing can do stuff." parser with helpText using eqString else lam l. lam. l in

let helpText = strJoin "\n"
  [ "test --shared INT [--opt1] [--extra] --thing FLOAT [--verbose]..."
  , "test --shared INT (--yes | --no) --thing FLOAT [--verbose]..."
  , ""
  , "Options:"
  , "  --shared INT  shared is a thing"
  , "  --opt1        opt1 is here"
  , "  --extra       extra extra"
  , "  --yes         yes yes"
  , "  --no          no no"
  , "  --thing FLOAT thing is a thing"
  , "  FILENAME      file and stuff"
  , "  --verbose     verbosity or something"
  ] in
utest optParserHelpText "test" "" parser with helpText using eqString else lam l. lam. l in

let helpText = strJoin "\n"
  [ "test --shared INT [--opt1] [--extra] --thing FLOAT [--verbose]..."
  , "test --shared INT (--yes | --no) --thing FLOAT [--verbose]..."
  , ""
  , "Stuff"
  , ""
  , "Weird flags:"
  , "  --with-category This flag has a category"
  , ""
  , "Other options:"
  , "  --shared INT  shared is a thing"
  , "  --opt1        opt1 is here"
  , "  --extra       extra extra"
  , "  --yes         yes yes"
  , "  --no          no no"
  , "  --thing FLOAT thing is a thing"
  , "  FILENAME      file and stuff"
  , "  --verbose     verbosity or something"
  ] in
utest optParserHelpText "test" "Stuff" (optMap2 (lam a. lam b. (a, b)) parser withCategory) with helpText using eqString else lam l. lam. l in

()
