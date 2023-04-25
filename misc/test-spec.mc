include "sys.mc"
include "stringid.mc"
include "arg.mc"
include "map.mc"
include "set.mc"
include "common.mc"

-- NOTE(vipa, 2023-03-30): `Path` should be considered to be opaque,
-- don't depend on the underlying type

-- type Path = SID
-- let stringToPath = stringToSid
-- let pathToString = sidToString
-- let cmpPath = cmpSID
-- let eqPath = eqSID

-- OPT(vipa, 2023-04-16): It ends up being significantly faster to
-- work with paths directly as strings rather than as SIDs, the
-- overhead of the translation costs more than we gain. That said, the
-- paths are typically quite long, so finding something smarter here
-- is probably still a very good avenue for optimization.
type Path = String
let stringToPath = lam x. x
let pathToString = lam x. x
let cmpPath = cmpString
let eqPath = eqString

-- This represents whether we should run a task, and if so, what the
-- expected outcome is. This types is ordered, where Dont < Fail <
-- Success
type ExpectedResult
con Dont : () -> ExpectedResult
con Fail : () -> ExpectedResult
con Success : () -> ExpectedResult

-- There are three normal tasks for testing all .mc files in the
-- compiler: compilation, interpretation, and running the compiled
-- program. We have two invariants we assume on the values for any
-- given file:
--
-- * if compile < Success, then run = Dont
-- * interpret <= run
--
-- These will be maintained by lowering run and/or interpret if
-- needed.
type NormalTasks =
  { compile : ExpectedResult
  , interpret : ExpectedResult
  , run : ExpectedResult
  }

let defaultTasks : NormalTasks =
  { compile = Success (), interpret = Success (), run = Success () }
let noTasks : NormalTasks =
  { compile = Dont (), interpret = Dont (), run = Dont () }

type ConditionStatus
-- All dependencies are met for this set of tests
con ConditionsMet : () -> ConditionStatus
-- Not all dependencies are met for this set of tests, but it's
-- theoretically possible for them to be met, i.e., they should be
-- included in `test-all`.
con ConditionsUnmet : () -> ConditionStatus
-- Not all dependencies are met for this set of tests, and they
-- *cannot* be, e.g., there are hardware requirements that are
-- unmet. This means that these tests should *not* be included in
-- `test-all`. (Note that they can still be included if explicitly
-- listed)
con ConditionsImpossible : () -> ConditionStatus

type MidCmd = {input : Path, cmd : String, tag : String} -> Path
type EndCmd = {input : Path, cmd : String, tag : String} -> ()

type TestApi =
  { mi : { m : MidCmd, e : EndCmd, f : EndCmd }
  , sh : { m : MidCmd, e : EndCmd, f : EndCmd }
  }

type TestCollection =
  -- The name of this set of tests, i.e., how it is identified on the
  -- commandline. Must be unique, and preferably without spaces or
  -- other characters that are special to a shell (which would then
  -- require quoting by the user, which is unfriendly).
  { name : String

  -- This function should call its argument with all paths that is in
  -- some way exceptional, in the sense that there's some part of the
  -- normal testing flow that should not run.
  , exclusions : (NormalTasks -> [Path] -> ()) -> ()

  -- This function should call its argument with all paths that should
  -- only be tested as normal if some dependencies are met. Note that:
  --
  -- * This function takes precedence over `exclusions` above.
  -- * This function is also used to remove conditional inclusions
  --   when the condition isn't met. This is done by pretending that
  --   the given `NormalTasks` says `Dont` for all components, needing
  --   no change in the function itself.
  --
  -- This means that you don't need to specify the same path in both
  -- `exclusions` and `conditionalInclusions`, the latter is enough.
  , conditionalInclusions : (NormalTasks -> [Path] -> ()) -> ()

  -- This function should check if all dependencies are met for this
  -- set of tests and/or if they theoretically *could* be met, i.e.,
  -- if they should be included in the `smart` and/or `all` targets.
  , checkCondition : () -> ConditionStatus

  -- Setup new tests that do not follow the normal testing
  -- strategy. Two functions are available for adding build/test
  -- steps:
  --
  -- * `mi`, for invoking the correct `mi`, since there are multiple
  --   versions that could be used, and we must also setup where to
  --   look for the standard library. The `String` argument is the
  --   command to use, e.g., `compile --test %i --output %o`.
  -- * `sh`, for running anything else, e.g., `sort %i | uniq > %o`.
  --
  -- Both of these come in three versions:
  --
  -- * `m` for `mid`, a command that takes one input and produces one
  --   output. `%i` and `%o` will be replaced by the input and output,
  --   respectively.
  -- * `e` for `end`, a command that takes one input and produces no
  --   output; all information we care about is printed to
  --   stdout/stderr or in the return code.
  -- * `f` for `fail`, a command that takes one input and produces no
  --   input, and is expected to fail, as reported by the return code.
  --
  -- Other useful information:
  --
  -- * `%i` and `%o` are replaced by the input and the output
  --   respectively. There is presently no way to escape these.
  -- * All commands are run with the current working directory set to
  --   the root of the repository, i.e., scripts in `misc` are readily
  --   available.
  -- * The outputs are put in a different directory from the inputs,
  --   to not pollute things. This is presently not overridable, thus
  --   all commands must use and honor `%o`.
  -- * Stdout and stderr are captured and saved for all steps.
  -- * Command output is only printed if the returncode is incorrect.
  , newTests : TestApi -> ()
  }

-- Small helper to setup a test collection. Example usage:
-- { testColl "foo"
--   with conditionalInclusions = lam add.
--     add defaultTasks (glob "stdlib/foo/**/*.mc")
-- }
let testColl : String -> TestCollection = lam name.
  { name = name
  , exclusions = lam. ()
  , conditionalInclusions = lam. ()
  , checkCondition = lam. ConditionsMet ()
  , newTests = lam. ()
  }

let _dir = sysGetCwd ()

-- Find all files that match a given glob. Uses bash-style globs,
-- including `**` for matching any number of nested directories. Only
-- matches files under `src/`.
let glob : String -> [Path] = lam glob.
  let bashCmd = join ["\"for f in src/", glob, "; do echo \\$f; done\""] in
  let res = sysRunCommand ["bash", "-O", "globstar", "-O", "nullglob", "-c", bashCmd] "" _dir in
  let paths = map stringToPath (init (strSplit "\n" res.stdout)) in
  (if null paths then printLn (concat "Warning, empty glob: " glob) else ());
  paths

-------------------------------------------------------------------
-- The public API ends here, with one exception: `testMain` is also
-- considered public
-------------------------------------------------------------------

let _minER : ExpectedResult -> ExpectedResult -> ExpectedResult = lam a. lam b.
  switch (a, b)
  case (x & Dont _, _) | (_, x & Dont _) then x
  case (x & Fail _, _) | (_, x & Fail _) then x
  case (x & Success _, _) | (_, x & Success _) then x
  end

let _maxER : ExpectedResult -> ExpectedResult -> ExpectedResult = lam a. lam b.
  switch (a, b)
  case (x & Success _, _) | (_, x & Success _) then x
  case (x & Fail _, _) | (_, x & Fail _) then x
  case (x & Dont _, _) | (_, x & Dont _) then x
  end

let _intersectTasks : NormalTasks -> NormalTasks -> NormalTasks = lam a. lam b.
  { compile = _minER a.compile b.compile
  , interpret = _minER a.interpret b.interpret
  , run = _minER a.run b.run
  }

let _unionTasks : NormalTasks -> NormalTasks -> NormalTasks = lam a. lam b.
  { compile = _maxER a.compile b.compile
  , interpret = _maxER a.interpret b.interpret
  , run = _maxER a.run b.run
  }

let _expandFormat : String -> {i : String, o : String} -> String = lam format. lam data.
  recursive let work : String -> String -> String = lam acc. lam str.
    switch str
    case "" then acc
    case "%i" ++ str then work (concat acc data.i) str
    case "%o" ++ str then work (concat acc data.o) str
    case [c] ++ str then work (snoc acc c) str
    end
  in work "" format

let _phaseTime = ref (wallTimeMs ())
let _phase : String -> () = lam phase.
  let now = wallTimeMs () in
  printError (join [phase, ": ", float2string (subf now (deref _phaseTime))]);
  printError "\n";
  flushStderr ();
  modref _phaseTime now
-- let _phase = lam. ()

let testMain : [TestCollection] -> () = lam colls.
  _phase "start";
  -- NOTE(vipa, 2023-03-30): Check that the collections are reasonable
  let colls : Map String TestCollection =
    foldl (lam acc. lam c. mapInsertWith (lam. lam. error (concat "Duplicate test collection: " c.name)) c.name c acc)
      (mapEmpty cmpString)
      colls in
  let knownColls : Set String = setInsert "smart" (setInsert "all" (mapMap (lam. ()) colls)) in
  _phase "knownColls";

  -- NOTE(vipa, 2023-03-30): Set up options and apply defaults if needed
  type Mode in
  con BuildPerLine : () -> Mode in
  con TupRules : () -> Mode in
  con TupFilter : () -> Mode in
  type Options =
    { bootstrapped : Bool, installed : Bool, cheated : Bool, mode : Mode } in
  let options : Options =
    { bootstrapped = false, installed = false, cheated = false, mode = BuildPerLine () } in

  let optionsConfig : ParseConfig Options =
    [ ( [("--installed", "", "")]
      , "Use an already installed mi"
      , lam p. {p.options with installed = true}
      )
    , ( [("--bootstrapped", "", "")]
      , "Use (and build) a fully bootstrapped mi"
      , lam p. {p.options with bootstrapped = true}
      )
    , ( [("--cheated", "", "")]
      , "Use an installed mi to \"bootstrap\" in one step (default)"
      , lam p. {p.options with cheated = true}
      )
    , ( [("--tup-rules", "", "")]
      , "Print rules in a format tup expects"
      , lam p. {p.options with mode = TupRules ()}
      )
    , ( [("--tup-filter", "", "")]
      , "Print targets that have an explicit connection to the mentioned files, for use with tup"
      , lam p. {p.options with mode = TupFilter ()}
      )
    , ( [("--build-per-line", "", "")]
      , "Collect (filtered) targets and print their commands such that dependent targets are on the same line and in an appropriate order (default)"
      , lam p. {p.options with mode = BuildPerLine ()}
      )
    ] in
  match
    let args = tail argv in
    match index (eqString "--") args
    with Some idx then splitAt args idx
    else (args, [])
  with (args, files) in
  let res = argParse_general {args = args, optionsStartWith = ["--"]} options optionsConfig in
  match res with !ParseOK _ then
    argPrintError res;
    exit 1
  else
  match res with ParseOK {strings = argColls, options = options} in
  let options = match options with {bootstrapped = false, cheated = false, installed = false}
    then {options with cheated = true}
    else options in
  let options = match options.mode with TupRules _
    then {options with bootstrapped = true, cheated = true, installed = true}
    else options in
  _phase "options";

  -- NOTE(vipa, 2023-03-30): Check the validity of the requested sets
  let argColls : Set String = setOfSeq cmpString argColls in
  let unknownColls = setSubtract argColls knownColls in
  (if setIsEmpty unknownColls then () else
    let msg = join
      [ "Unknown test set(s): ", strJoin ", " (setToSeq unknownColls), "\n"
      , "Try one of these:    ", strJoin ", " (setToSeq knownColls)] in
    printLn msg;
    exit 1);
  _phase "unknownColls";

  let chosenColls =
    let explicitColls = mapFilter (lam k. lam. setMem k argColls) colls in
    let smartColls =
      switch (setMem "all" argColls, setMem "smart" argColls, options.mode)
      case (true, _, _) | (_, _, TupRules _) then
        mapFilter
          (lam. lam c. match c.checkCondition () with !ConditionsImpossible _ then true else false)
          colls
      case (_, true, _) then
        mapFilter
          (lam. lam c. match c.checkCondition () with ConditionsMet _ then true else false)
          colls
      case _ then
        mapEmpty cmpString
      end in
    mapUnion explicitColls smartColls in
  let unchosenColls = mapDifference colls chosenColls in
  _phase "chosenColls";

  -- NOTE(vipa, 2023-03-30): find all the files we'd normally expect
  -- to test, if no collection makes changes.
  let normals : Ref (Map Path NormalTasks) =
    let x = glob "**/*.mc" in
    let x = map (lam p. (p, defaultTasks)) x in
    ref (mapFromSeq cmpPath x) in
  _phase "basicNormals";

  let intersectAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normals (mapInsertWith _intersectTasks p t (deref normals))) paths in
  let unionAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normals (mapInsertWith _unionTasks p t (deref normals))) paths in
  let exactAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normals (mapInsert p t (deref normals))) paths in
  let excludeAdd : NormalTasks -> [Path] -> () = lam. lam paths.
    iter (lam p. modref normals (mapInsert p noTasks (deref normals))) paths in

  mapMap (lam c. c.exclusions intersectAdd) colls;
  mapMap (lam c. c.conditionalInclusions excludeAdd) unchosenColls;
  mapMap (lam c. c.conditionalInclusions exactAdd) chosenColls;
  _phase "coll normals";

  -- NOTE(vipa, 2023-03-30): API for adding build tasks
  type TargetData =
    { origin : Path
    , input : Path
    , command : String
    , stdout : Path
    , stderr : Path
    , friendlyCommand : String
    , extraDep : Option Path
    } in
  let targets : Ref (Map Path TargetData) = ref (mapEmpty cmpPath) in
  let orderedTargets : Ref [(Path, TargetData)] = ref [] in
  let addRaw
    : String
    -> Bool
    -> {input : Path, cmd : String, tag : String, friendlyCommand : String, extraDep : Option Path}
    -> Path
    = lam namespace. lam addOutput. lam data.
      let currTargets = deref targets in
      let origPath = pathToString data.input in
      let path = if isPrefix eqc namespace origPath then origPath else concat namespace origPath in
      let stdout = join [path, ".", data.tag, ".log"] in
      let stderr = join [path, ".", data.tag, ".err"] in
      -- TODO(vipa, 2023-03-31): Call _expandFormat earlier, maybe even peval it?
      let cmd = _expandFormat data.cmd in
      let friendlyCommand = _expandFormat data.friendlyCommand in
      match
        if addOutput then
          let target = join [path, ".", data.tag] in
          (friendlyCommand {i = origPath, o = target}, cmd {i = origPath, o = target}, target)
        else (friendlyCommand {i = origPath, o = "%o"}, cmd {i = origPath, o = "%o"}, stdout)
      with (friendlyCommand, cmd, target) in
      let cmd = join
        [ "{ ", cmd, "; } >'", stdout, "' 2>'", stderr
        , "' || { misc/elide-cat stdout '", stdout, "'; misc/elide-cat stderr '", stderr, "'; false; }"
        ] in
      -- OPT(vipa, 2023-04-16): It seems that map operations are the
      -- most costly presently. It doesn't *seem* to be the direct
      -- operations below, so I'm guessing it's via stringToSid.
      let origin = optionMapOr data.input (lam td. td.origin)
        (mapLookup data.input currTargets) in
      let td =
        { origin = origin
        , input = data.input
        , command = cmd
        , stdout = stringToPath stdout
        , stderr = stringToPath stderr
        , extraDep = data.extraDep
        , friendlyCommand = friendlyCommand
        } in
      -- TODO(vipa, 2023-03-31): Error on duplicate target definition
      let target = stringToPath target in
      modref targets (mapInsert target td currTargets);
      modref orderedTargets (snoc (deref orderedTargets) (target, td));
      target
  in
  let negateCmd = lam data.
    { data with cmd = join ["! { ", data.cmd, "; }"]
    , friendlyCommand = concat "FAIL " data.friendlyCommand
    } in
  let mkSh : String -> String -> { m : MidCmd, e : EndCmd, f : EndCmd } = lam miTag. lam namespace.
    let fixData = lam data.
      { friendlyCommand = data.cmd
      , extraDep = None ()
      , cmd = data.cmd
      , tag = data.tag
      , input = data.input
      } in
    let namespace = join [miTag, "/", namespace, "/"] in
    { m = lam data. addRaw namespace true (fixData data)
    , e = lam data. addRaw namespace false (fixData data); ()
    , f = lam data. addRaw namespace false (negateCmd (fixData data)); ()
    } in
  let mkMi
    : {pre : String, tag : String, extraDep : Option Path, kind : String}
    -> String
    -> { m : MidCmd, e : EndCmd, f : EndCmd }
    = lam config. lam namespace.
      let fixData = lam data.
        { friendlyCommand = join [config.kind, " MI ", data.cmd]
        , extraDep = config.extraDep
        , cmd = join [config.pre, " ", data.cmd]
        , tag = data.tag
        , input = data.input
        } in
      let namespace = join [config.tag, "/", namespace, "/"] in
      { m = lam data. addRaw namespace true (fixData data)
      , e = lam data. addRaw namespace false (fixData data); ()
      , f = lam data. addRaw namespace false (negateCmd (fixData data)); ()
      }
  in

  -- NOTE(vipa, 2023-03-31): Add targets for each mi version used
  let addTargets = lam mkMi. lam mkSh.
    let addNormals =
      let mi = mkMi "normal" in
      let sh = mkSh "normal" in
      lam src. lam tasks.
        switch tasks.compile
        case Dont _ then ()
        case Fail _ then
          mi.f {input = src, cmd = "compile --test %i --exit-before", tag = "exe"}
        case Success _ then
          let exe = mi.m {input = src, cmd = "compile --test %i --output %o", tag = "exe"} in
          (switch tasks.run
           case Dont _ then ()
           case Fail _ then
             sh.f {input = exe, cmd = "%i", tag = "run"}
           case Success _ then
             sh.e {input = exe, cmd = "%i", tag = "run"}
           end);
          (switch _minER tasks.run tasks.interpret
           case Dont _ then ()
           case Fail _ then
             mi.f {input = src, cmd = "eval --test %i", tag = "eval"}
           case Success _ then
             mi.e {input = src, cmd = "eval --test %i", tag = "eval"}
           end)
        end
    in
    let addNews = lam testColl. lam config.
      config.newTests {mi = mkMi testColl, sh = mkSh testColl} in
    mapMapWithKey addNormals (deref normals);
    mapMapWithKey addNews chosenColls;
    ()
  in
  _phase "target api";
  let buildDir = match options.mode with TupRules _ | TupFilter _ then "build/tup/" else "build/" in
  (if options.bootstrapped then
    let tag = concat buildDir "bootstrapped" in
    let mkMi = mkMi
      { pre = join ["MCORE_LIBS=stdlib=", _dir, "/src/stdlib ", buildDir, "mi"]
      , tag = tag
      , extraDep = Some (stringToPath (concat buildDir "mi"))
      , kind = "BOOTSTRAPPED"
      } in
    let mkSh = mkSh tag in
    addTargets mkMi mkSh
  else ());
  _phase "bootstrapped";
  (if options.installed then
    let tag = concat buildDir "installed" in
    let mkMi = mkMi
      { pre = join ["MCORE_STDLIB=", _dir, "/src/stdlib mi"]
      , tag = tag
      , extraDep = None ()
      , kind = "INSTALLED"
      } in
    let mkSh = mkSh tag in
    addTargets mkMi mkSh
  else ());
  _phase "installed";
  (if options.cheated then
    let tag = concat buildDir "cheated" in
    let mkMi = mkMi
      { pre = join ["MCORE_STDLIB=", _dir, "/src/stdlib ", buildDir, "mi-cheat"]
      , tag = tag
      , extraDep = Some (stringToPath (concat buildDir "mi-cheat"))
      , kind = "CHEATED"
      } in
    let mkSh = mkSh tag in
    addTargets mkMi mkSh
  else ());
  _phase "cheated";

  switch options.mode
  case TupRules _ then
    let cpDirStructure : all a. String -> a -> () = lam coll. lam.
      command (join ["find src -type d -exec mkdir -p ", buildDir, "{installed,bootstrapped,cheated}/", coll, "/{} \\;"]);
      ()
    in
    mapMapWithKey cpDirStructure colls;
    cpDirStructure "normal" ();
    _phase "tup-mk-dirs";
    let printRule = lam pair. match pair with (target, td) in
      let extra = match td.extraDep
        with Some dep then concat " | " (pathToString dep)
        else "" in
      let cmd = join
        [ ": ", pathToString td.input, extra
        , " |> ^ ", td.friendlyCommand, "^ "
        , td.command, " |> ", pathToString td.stdout, " ", pathToString td.stderr
        , if eqPath target td.stdout then "" else concat " " (pathToString target)
        ] in
      printLn cmd in
    iter printRule (deref orderedTargets);
    _phase "tup-rules"
  end

mexpr

testMain
  [ { testColl "accelerate"
    with checkCondition = lam.
      if and (sysCommandExists "nvcc") (sysCommandExists "futhark")
      then ConditionsMet ()
      -- else ConditionsImpossible () -- TODO(vipa, 2023-04-25): figure out how to check if we have nvidia hardware
      else ConditionsUnmet () -- TODO(vipa, 2023-04-25): temporarily pretend they're not impossible, to test `newTests`
    , exclusions = lam modPaths.
      -- NOTE(vipa, 2023-04-25): Accelerate isn't supported in
      -- interpreted mode, and compiled mode is already tested via the
      -- new tests below.
      modPaths noTasks (glob "test/examples/accelerate/**/*.mc")
    , newTests = lam do.
      for_ (glob "test/examples/accelerate/**/*.mc") (lam mc.
        let exe = do.mi.m {input = mc, cmd = "compile --accelerate %i --output %o", tag = "accelerate"} in
        do.sh.e {input = exe, cmd = "%i", tag = "run-accelerate"};
        let exe = do.mi.m {input = mc, cmd = "compile --debug-accelerate %i --output %o", tag = "debug-accelerate"} in
        do.sh.e {input = exe, cmd = "%i", tag = "run-debug-accelerate"})
    }
  ]
