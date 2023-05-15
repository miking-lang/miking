/-

This program is written to have single source of truth for all our
tests, in a way that is easy to modify as we get more tests, and that
also works with multiple test runners (presently `make` and `tup`).

The file starts with a public API, then internals, then at the end
(after `mexpr`) is the code using the API. New tests and exceptions
are to be added there.

-/

include "sys.mc"
include "stringid.mc"
include "arg.mc"
include "map.mc"
include "set.mc"
include "common.mc"
include "tuple.mc"

-- A path representing some file in the repository, either source or
-- generated through some command.
type Path

-- This represents whether we should run a task, and if so, what the
-- expected outcome is. This type is ordered, where Dont < Fail <
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

-- `MidCmd` and `EndCmd` are the types of functions that you can call
-- to register a new command to run as part of our testing.
-- A `MidCmd` registers a command with one input and one output.
type MidCmd = {input : Path, cmd : String, tag : String} -> Path
-- An `EndCmd` registers a command with one input and no outputs.
type EndCmd = {input : Path, cmd : String, tag : String} -> ()

type Subdirs
con IncludeSubs : () -> Subdirs
con OnlyHere : () -> Subdirs

type File
con ExactFile : String -> File
con SuffixFile : String -> File

type MarkApi =
  { mark : NormalTasks -> [Path] -> ()
  , glob : [String] -> Subdirs -> File -> [Path]
  }
type TestApi =
  { mi : { m : MidCmd, e : EndCmd, f : EndCmd }
  , sh : { m : MidCmd, e : EndCmd, f : EndCmd }
  , glob : [String] -> Subdirs -> File -> [Path]
  }

-- Example:
-- glob ["stdlib", "parser"] (IncludeSubs ()) (SuffixFile ".mc")
-- is equivalent with the following bash-style glob:
-- stdlib/parser/**/*.mc

type TestCollection =
  -- The name of this set of tests, i.e., how it is identified on the
  -- commandline. Must be unique, and preferably without spaces or
  -- other characters that are special to a shell (which would then
  -- require quoting by the user, which is unfriendly).
  { name : String

  -- This function should call its argument with all paths that is in
  -- some way exceptional, in the sense that there's some part of the
  -- normal testing flow that should not run.
  , exclusions : MarkApi -> ()

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
  , conditionalInclusions : MarkApi -> ()

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

-------------------------------------------------------------------
-- The public API ends here, with one exception: `testMain` is also
-- considered public
-------------------------------------------------------------------

type CollId = String

type Glob =
  { dirs : [String]
  , subdirs : Subdirs
  , file : File
  }

let _drop = lam n. lam s. subsequence s n (subi (length s) n)

let _restrictToDir : [String] -> Glob -> Option Glob = lam dirs. lam glob.
  let fixedGlob = {glob with dirs = tail dirs, subdirs = OnlyHere ()} in
  let actualGlobDirs = cons "src" glob.dirs in
  if isPrefix eqString actualGlobDirs dirs then
    let remainingDirs = _drop (length actualGlobDirs) dirs in
    switch (remainingDirs, glob.subdirs)
    case ([], _) then Some fixedGlob
    case (_, IncludeSubs _) then Some fixedGlob
    case _ then None ()
    end
  else None ()

let _matchesGlob : Glob -> ([String], String) -> Bool = lam glob. lam f.
  match f with (dirs, file) in
  if isPrefix eqString glob.dirs dirs then
    let remainingDirs = _drop (length glob.dirs) dirs in
    let dirsMatch = switch (remainingDirs, glob.subdirs)
      case ([], _) then true
      case (_, IncludeSubs _) then true
      case _ then false
      end in
    if dirsMatch then
      switch glob.file
      case ExactFile f then eqString f file
      case SuffixFile f then isSuffix eqc f file
      end
    else false
  else false

type MiMode
con MiBoot : () -> MiMode
con MiCheat : () -> MiMode
con MiInstalled : () -> MiMode

let _miModeToString : MiMode -> String = lam m. switch m
  case MiBoot _ then "boot"
  case MiCheat _ then "cheat"
  case MiInstalled _ then "installed"
  end

type OrigRecord =
  { path : ([String], String)
  }
con OrigPath : OrigRecord -> Path
type DerivRecord =
  { orig : OrigRecord
  , mode : MiMode
  , testColl : CollId
  , tag : String
  }
con DerivPath : DerivRecord -> Path

let _mkDeriv : Path -> MiMode -> CollId -> String -> Path
  = lam path. lam mode. lam coll. lam tag.
  let orig = switch path
    case OrigPath x then x
    case DerivPath x then x.orig
    end in
  DerivPath
  { orig = orig
  , mode = mode
  , testColl = coll
  , tag = tag
  }

let _cmpPath : Path -> Path -> Int = lam a. lam b.
  switch (a, b)
  case (OrigPath a, OrigPath b) then tupleCmp2 (seqCmp cmpString) cmpString a.path b.path
  case (OrigPath _, DerivPath _) then 1
  case (DerivPath _, OrigPath _) then negi 1
  case (DerivPath a, DerivPath b) then
    let res = subi (constructorTag a.mode) (constructorTag b.mode) in
    if neqi res 0 then res else
    let res = cmpString a.testColl b.testColl in
    if neqi res 0 then res else
    let res = cmpString a.tag b.tag in
    if neqi res 0 then res else
    tupleCmp2 (seqCmp cmpString) cmpString a.orig.path b.orig.path
  end

let _glob
  : { root : String
    , glob : Glob
    , dir : Option [String]
    , files : Option (Set String)
    }
  -> [Path]
  = lam args.
    let glob =
      match args.dir with Some dir then
        _restrictToDir dir args.glob
      else Some args.glob in
    match glob with Some glob then
      let globStr = strJoin "/" (cons "src" glob.dirs) in
      let globStr = match glob.subdirs with IncludeSubs _
        then concat globStr "/**"
        else globStr in
      let globStr = switch glob.file
        case ExactFile f then join [globStr, "/", f]
        case SuffixFile f then join [globStr, "/*", f]
        end in
      let bashCmd = join ["\"for f in ", globStr, "; do echo \\$f; done\""] in
      let res = sysRunCommand ["bash", "-O", "globstar", "-O", "nullglob", "-c", bashCmd] "" args.root in
      let stringToPath = lam s. OrigPath { path = match strSplit "/" s with dirs ++ [file] in (dirs, file) } in
      let paths = init (strSplit "\n" res.stdout) in
      let paths = match args.files with Some files
        then filter (lam p. setMem p files) paths
        else paths in
      map stringToPath paths
    else []

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
    case "%%" ++ str then work (snoc acc '%') str
    case "%i" ++ str then work (concat acc data.i) str
    case "%o" ++ str then work (concat acc data.o) str
    case [c] ++ str then work (snoc acc c) str
    end
  in work "" format

-- let _phaseTime = ref (wallTimeMs ())
-- let _phase : String -> () = lam phase.
--   let now = wallTimeMs () in
--   printError (join [phase, ": ", float2string (subf now (deref _phaseTime))]);
--   printError "\n";
--   flushStderr ();
--   modref _phaseTime now
let _phase = lam. ()

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
  con Make : () -> Mode in
  con TupRules : () -> Mode in
  con TupFilter : () -> Mode in
  type Options =
    { bootstrapped : Bool, installed : Bool, cheated : Bool, mode : Mode } in
  let options : Options =
    { bootstrapped = false, installed = false, cheated = false, mode = Make () } in

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
    , ( [("--make", "", "")]
      , "Print (filtered) targets as make-rules (default)"
      , lam p. {p.options with mode = Make ()}
      )
    ] in
  match
    let args = tail argv in
    match index (eqString "--") args with Some idx then
      let x = splitAt args idx in
      (x.0, tail x.1)
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

  -- TODO(vipa, 2023-05-12): For now assume we're always running in
  -- the root dir
  let root = "." in
  let pathDirs = lam p. switch p
    case OrigPath x then x.path.0
    case DerivPath x then cons "build" x.orig.path.0
    end in
  let pathDir = lam p. strJoin "/" (pathDirs p) in
  let pathBasename = lam p. switch p
    case OrigPath x then x.path.1
    case DerivPath x then join [x.orig.path.1, ".", x.testColl, ".", _miModeToString x.mode, ".", x.tag]
    end in
  let dir = match options.mode with TupRules _
    then match files with [dir] ++ _
      then Some (strSplit "/" dir)
      else Some []
    else None () in
  match
    match dir with Some dirs then
      let srcDir = match dirs with ["src"] ++ dirs
        then strJoin "/" (map (lam. "..") dirs)
        else strJoin "/" (snoc (map (lam. "..") dirs) "src") in
      -- NOTE(vipa, 2023-05-15): When we're working in a single
      -- directory we'll never have paths pointing to any other
      -- directory, thus we can just print the filename without any
      -- directories.
      let pathToString = lam p.
        utest pathDirs p with dirs in
        pathBasename p in
      ({src = srcDir, root = strJoin "/" (map (lam. "..") dirs)}, pathToString)
    else
      ({src = concat root "/src/", root = root}, lam p. strJoin "/" (snoc (pathDirs p) (pathBasename p)))
  with (commandPath, pathToString) in

  let globBase =
    { root = root
    , glob = {dirs = [], subdirs = OnlyHere (), file = ExactFile ""}  -- NOTE(vipa, 2023-05-15): The 'glob' field is just a placeholder, it's always replaced
    , dir = dir
    , files = match (options.mode, files) with ((TupRules _, _) | (_, []))
      then None ()
      else Some (setOfSeq cmpString files)
    } in
  let glob = lam dirs. lam subs. lam file.
    _glob {globBase with glob = {dirs = dirs, subdirs = subs, file = file}} in

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

  -- NOTE(vipa, 2023-03-30): These are all files that would normally
  -- be tested but have some form of exception from a test collection
  let normalExceptions : Ref (Map Path NormalTasks) = ref (mapEmpty _cmpPath) in

  let intersectAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normalExceptions (mapInsertWith _intersectTasks p t (deref normalExceptions))) paths in
  let unionAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normalExceptions (mapInsertWith _unionTasks p t (deref normalExceptions))) paths in
  let exactAdd : NormalTasks -> [Path] -> () = lam t. lam paths.
    iter (lam p. modref normalExceptions (mapInsert p t (deref normalExceptions))) paths in
  let excludeAdd : NormalTasks -> [Path] -> () = lam. lam paths.
    iter (lam p. modref normalExceptions (mapInsert p noTasks (deref normalExceptions))) paths in

  mapFoldWithKey (lam. lam. lam c. c.exclusions {glob = glob, mark = intersectAdd}) () colls;
  mapFoldWithKey (lam. lam. lam c. c.conditionalInclusions {glob = glob, mark = excludeAdd}) () unchosenColls;
  mapFoldWithKey (lam. lam. lam c. c.conditionalInclusions {glob = glob, mark = exactAdd}) () chosenColls;
  _phase "coll normals";

  type Command =
    { input : Path
    , miMode : MiMode
    , output : Option Path
    , stdout : Path
    , stderr : Path
    , command : String
    , friendlyCommand : String
    } in
  let commands : Ref [Command] = ref [] in
  type CommandSpec =
    { input : Path
    , miMode : MiMode
    , coll : CollId
    , tag : String
    , output : Bool
    , command : String
    , friendlyCommand : String
    } in

  let addCommand : CommandSpec -> Path = lam spec.
    let stdout = _mkDeriv spec.input spec.miMode spec.coll (concat spec.tag ".out") in
    let stderr = _mkDeriv spec.input spec.miMode spec.coll (concat spec.tag ".err") in
    let output = if spec.output
      then Some (_mkDeriv spec.input spec.miMode spec.coll spec.tag)
      else None () in
    match
      switch options.mode
      case Make _ then
        ( _expandFormat spec.command {i="$<", o="$@"}
        , _expandFormat spec.friendlyCommand {i="$<", o="$@"}
        )
      case TupRules _ then
        ( _expandFormat spec.command {i="%f", o="%3o"}
        , _expandFormat spec.friendlyCommand {i="%f", o="%3o"}
        )
      case _ then (spec.command, spec.friendlyCommand)
      end
    with (command, friendlyCommand) in
    let firstLogIdx = if spec.output then 2 else 1 in
    let stdoutStr = match options.mode with TupRules _
      then "%1o"
      else pathToString stdout in
    let stderrStr = match options.mode with TupRules _
      then "%2o"
      else pathToString stderr in
    let elideCat = match options.mode with TupRules _
      then "$(ROOT)/misc/elide-cat"
      else "misc/elide-cat" in
    let command = join
      [ "{ ", command, "; } >'", stdoutStr, "' 2>'", stderrStr
      , "' || { ", elideCat, " stdout '", stdoutStr, "'; ", elideCat, " stderr '", stderrStr, "'; false; }"
      ] in
    let cmd =
      { input = spec.input
      , miMode = spec.miMode
      , stdout = stdout
      , stderr = stderr
      , output = output
      , friendlyCommand = friendlyCommand
      , command = command
      } in
    modref commands (snoc (deref commands) cmd);
    optionGetOr stdout output
  in
  let negateCmd = lam data.
    { data with command = join ["! { ", data.command, "; }"]
    , friendlyCommand = concat "FAIL " data.friendlyCommand
    } in
  let mkSh : MiMode -> CollId -> { m : MidCmd, e : EndCmd, f : EndCmd } = lam mode. lam coll.
    let fixData = lam output. lam data.
      { input = data.input
      , miMode = mode
      , coll = coll
      , tag = data.tag
      , output = output
      , command = data.cmd
      , friendlyCommand = data.cmd
      } in
    { m = lam data. addCommand (fixData true data)
    , e = lam data. addCommand (fixData false data); ()
    , f = lam data. addCommand (negateCmd (fixData false data)); ()
    } in
  let mkMi
    : {pre : String, mode : MiMode}
    -> CollId
    -> { m : MidCmd, e : EndCmd, f : EndCmd }
    = lam config. lam coll.
      let kind = switch config.mode
        case MiBoot _ then "BOOT "
        case MiCheat _ then "CHEAT "
        case MiInstalled _ then "INSTALLED "
        end in
      let fixData = lam output. lam data.
        { input = data.input
        , miMode = config.mode
        , coll = coll
        , tag = data.tag
        , output = output
        , command = join [config.pre, " ", data.cmd]
        , friendlyCommand = join [kind, "MI ", data.cmd]
        } in
      { m = lam data. addCommand (fixData true data)
      , e = lam data. addCommand (fixData false data); ()
      , f = lam data. addCommand (negateCmd (fixData false data)); ()
      }
  in

  -- NOTE(vipa, 2023-03-31): Add targets for each mi version used
  let addTargets = lam mkMi. lam mkSh.
    let addNormals =
      let mi = mkMi "normal" in
      let sh = mkSh "normal" in
      lam src.
        let tasks = optionGetOr defaultTasks (mapLookup src (deref normalExceptions)) in
        switch tasks.compile
        case Dont _ then ()
        case Fail _ then
          mi.f {input = src, cmd = "compile --test %i --exit-before", tag = "exe"}
        case Success _ then
          let exe = mi.m {input = src, cmd = "compile --test %i --output %o", tag = "exe"} in
          (switch tasks.run
           case Dont _ then ()
           case Fail _ then
             sh.f {input = exe, cmd = "./%i", tag = "run"}
           case Success _ then
             sh.e {input = exe, cmd = "./%i", tag = "run"}
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
    let addNews = lam. lam testColl. lam config.
      config.newTests {glob = glob, mi = mkMi testColl, sh = mkSh testColl} in
    mapFoldWithKey addNews () chosenColls;
    iter addNormals (glob [] (IncludeSubs ()) (SuffixFile ".mc"))
  in
  _phase "target api";
  let ocamlPath = match options.mode with TupRules _
    then " OCAMLPATH=$(VARIANT_SRC)/lib "
    else " OCAMLPATH=\\$(pwd)/build/lib " in
  (if options.bootstrapped then
    let mi = match options.mode with TupRules _
      then "%<mi>"
      else "build/mi" in
    let mkMi = mkMi
      { pre = join ["MCORE_LIBS=stdlib=", commandPath.src, "/stdlib", ocamlPath, mi]
      , mode = MiBoot ()
      } in
    let mkSh = mkSh (MiBoot ()) in
    addTargets mkMi mkSh
  else ());
  _phase "bootstrapped";
  (if options.installed then
    let mkMi = mkMi
      { pre = join ["MCORE_LIBS=stdlib=", commandPath.src, "/stdlib mi"]
      , mode = MiInstalled ()
      } in
    let mkSh = mkSh (MiInstalled ()) in
    addTargets mkMi mkSh
  else ());
  _phase "installed";
  (if options.cheated then
    let mi = match options.mode with TupRules _
      then "%<mi-cheat>"
      else "build/mi-cheat" in
    let mkMi = mkMi
      { pre = join ["MCORE_LIBS=stdlib=", commandPath.src, "/stdlib", ocamlPath, mi]
      , mode = MiCheat ()
      } in
    let mkSh = mkSh (MiCheat ()) in
    addTargets mkMi mkSh
  else ());
  _phase "cheated";

  (if null (deref commands) then
    printLn "Found no matching tests (maybe a deactivated test collection?)";
    exit 1
   else ());

  switch options.mode
  case TupRules _ then
    let printRule = lam c.
      let extra = switch c.miMode
        case MiBoot _ then join [" | ", commandPath.src, "/<mi> ", commandPath.src, "/<boot-lib>"]
        case MiInstalled _ then ""
        case MiCheat _ then join [" | ", commandPath.src, "/<mi-cheat> ", commandPath.src, "/<boot-lib>"]
        end in
      let cmd = join
        [ ": ", pathToString c.input, extra
        , " |> ^ ", c.friendlyCommand, "^ "
        , c.command, " |> "
        , pathToString c.stdout, " ", pathToString c.stderr
        , optionMapOr "" (lam p. cons ' ' (pathToString p)) c.output
        ] in
      printLn cmd in
    iter printRule (deref commands);
    _phase "tup-rules"
  case TupFilter _ then
    let printRule = lam c. printLn (pathToString c.stdout) in
    iter printRule (deref commands);
    _phase "tup-filter"
  case Make _ then
    let printPrereq = lam c.
      let o = optionGetOr c.stdout c.output in
      print (cons ' ' (pathToString o)) in
    let printPhony = lam c.
      let o = optionGetOr c.stdout c.output in
      match c.input with OrigPath _
      then print (cons ' ' (pathToString o))
      else ()
    in
    let printRule = lam c.
      let o = optionGetOr c.stdout c.output in
      let extra = switch c.miMode
        case MiBoot _ then " | build/mi"
        case MiInstalled _ then ""
        case MiCheat _ then "| build/mi-cheat"
        end in
      let cmd = join
        [ pathToString o, " : ", pathToString c.input, "\n"
        , "\t@echo ", c.friendlyCommand, "\n"
        , "\t@mkdir -p ", pathDir c.stdout, "\n"
        , "\t@", c.command
        ] in
      printLn cmd
    in
    print "test:";
    iter printPrereq (deref commands);
    printLn "";
    print ".PHONY:";
    iter printPhony (deref commands);
    printLn "";
    iter printRule (deref commands);
    _phase "make"
  end

mexpr

testMain
  [ { testColl "accelerate"
    with checkCondition = lam.
      if and (sysCommandExists "nvcc") (sysCommandExists "futhark")
      then ConditionsMet ()
      else ConditionsImpossible () -- TODO(vipa, 2023-04-25): figure out how to check if we have nvidia hardware
    , exclusions = lam api.
      -- NOTE(vipa, 2023-04-25): Accelerate isn't supported in
      -- interpreted mode, and compiled mode is already tested via the
      -- new tests below.
      api.mark noTasks (api.glob ["test", "examples", "accelerate"] (IncludeSubs ()) (SuffixFile ".mc"))
    , newTests = lam api.
      for_ (api.glob ["test", "examples", "accelerate"] (IncludeSubs ()) (SuffixFile ".mc")) (lam mc.
        let exe = api.mi.m {input = mc, cmd = "compile --accelerate %i --output %o", tag = "exe"} in
        api.sh.e {input = exe, cmd = "%i", tag = "run"};
        let exe = api.mi.m {input = mc, cmd = "compile --debug-accelerate %i --output %o", tag = "debug-exe"} in
        api.sh.e {input = exe, cmd = "%i", tag = "debug-run"})
    }

  , { testColl "exceptions"
    with exclusions = lam api.
      let runFail = {defaultTasks with interpret = Fail (), run = Fail ()} in
      let unsupported = {defaultTasks with interpret = Fail (), compile = Fail ()} in
      let dontRun = {defaultTasks with run = Dont ()} in
      let markExact = lam tasks. lam path.
        print "";  -- TODO(vipa, 2023-05-16): Commenting out this line makes it so this entire function disappears (dead-code elim presumably)
        match strSplit "/" path with dirs ++ [file] in
        api.mark tasks (api.glob dirs (OnlyHere ()) (ExactFile file)) in

      -- Files that are expected to fail
      iter (markExact runFail)
        [ "test/examples/utest.mc"
        ];

      -- Python is only supported in boot
      iter (markExact unsupported)
        [ "stdlib/python/python.mc"
        , "test/py/python.mc"
        ];

      -- This doesn't seem to terminate in a reasonable amount of time
      iter (markExact dontRun)
        [ "test/examples/async/tick.mc"
        ];

      ()
    }

  , { testColl "microbenchmark"
    with exclusions = lam api.
      -- NOTE(vipa, 2023-05-16): These are tested via new tests instead
      api.mark noTasks (api.glob ["test", "microbenchmark"] (IncludeSubs ()) (SuffixFile ".mc"))
    , newTests = lam api.
      for_ (api.glob ["test", "microbenchmark"] (IncludeSubs ()) (SuffixFile ".mc")) (lam mc.
        let exe = api.mi.m {input = mc, cmd = "compile %i --test --output %o", tag = "exe"} in
        -- NOTE(vipa, 2023-05-16): We arbitrarily run with argument 1,
        -- since we're just testing, not benchmarking
        api.mi.e {input = mc, cmd = "eval --test %i -- 1", tag = "eval"};
        api.sh.e {input = exe, cmd = "%i 1", tag = "run"})
    }

  , { testColl "constraint-programming"
    with checkCondition = lam.
      if sysCommandExists "minizinc"
      then ConditionsMet ()
      else ConditionsUnmet ()
    , conditionalInclusions = lam api.
      api.mark defaultTasks (api.glob ["stdlib", "cp"] (IncludeSubs ()) (SuffixFile ".mc"))
    }

  , { testColl "tuning"
    with exclusions = lam api.
      -- NOTE(vipa, 2023-05-16):
      api.mark noTasks (api.glob ["test", "examples", "tuning"] (IncludeSubs ()) (SuffixFile ".mc"))
    , newTests = lam api.
      for_ (api.glob ["test", "examples", "tuning"] (IncludeSubs ()) (SuffixFile ".mc")) (lam mc.
        let exe = api.mi.m {input = mc, cmd = "tune %i --test --disable-optimizations --compile --disable-exit-early --enable-cleanup --output %o", tag = "exe"} in
        api.sh.e {input = exe, cmd = "./%i", tag = "run"})
    }
  ]
