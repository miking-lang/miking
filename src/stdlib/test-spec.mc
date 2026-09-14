-- This file provides an interface for building a test-runner, used
-- to, e.g., test the miking compiler and project.
--
-- The core assumption is that each test "belongs" to some file in a
-- project, and that each such file might have multiple, possibly
-- interdependent tests (e.g., compiling and running a file).
--
-- A test-runner should be a single `.mc` file calling `testMain`,
-- defined in the `TestSpec` language fragment. It takes a number of
-- arguments:
-- * A list of substituters. This is an advanced feature, most users
--   will just give `[noSubstituter]`. See `misc/test-spec.mc` in the
--   miking repository for an example.
-- * A list of directories in which to look for files with tests,
--   e.g., `["test"]`.
-- * An optional location of the test-runner source and executable. If
--   given, the runner will ensure the executable is up-to-date before
--   running tests.
-- * A function declaring all tests. Typically `(lam api. ...elided...)`.
--
-- The function will do two things:
-- * Declare tests that can be added to any file, via `api.midStep`
--   and `api.endStep`.
-- * Declare which files should run which tests, via `api.tests`.
--
-- For each given file, the "status" of a test can be either:
-- * `Dont ()`, i.e., don't run this test for this file.
-- * `Fail ()`, i.e., run the test for this file, and expect it to
--   fail.
-- * `Succ ()`, i.e., run the test for this file, and expect it to
--   succeed.
--
-- Dependencies between tests are handled as follows: if test A
-- depends on B, and B is set to `Dont ()` or `Fail ()`, set A to
-- `Dont ()`, otherwise leave it as is.

include "set.mc"
include "optparse-applicative.mc"
include "fileutils.mc"

type Substituter =
  { flag : String
  , description : String
  , substitutions : Map Char
    { tup : {actual : String, deps : [String]}
    , make : {actual : String, deps : [String]}
    , friendly : String
    }
  }
let noSubstituter : Substituter =
  { flag = ""
  , description = "Perform only standard substitution on commands (%f, %i, %o, and %%)."
  , substitutions = mapEmpty cmpChar
  }

let _elideCatSource = strJoin "\n"
  [ "#!/usr/bin/env bash"
  , ""
  , "lines=$(wc -l < \"$2\")"
  , "if test \"$lines\" -gt 0; then"
  , "  echo \"$1\" output \"(full output in $2)\":"
  , "  awk \"FNR <= 6 || FNR >= $lines-5 {print FNR \\\":\\t\\\" \\$0; next} !el {print \\\"...elided...\\\"; el=1}\" \"$2\""
  , "  echo"
  , "  echo"
  , "else"
  , "  echo No output on \"$1\""
  , "  echo"
  , "fi"
  , ""
  ]

let _tuprulesSource = strJoin "\n"
  [ "ROOT := $(TUP_CWD)/.."
  , concat "&genrules := ../" (head argv)
  , ""
  ]

let _tupdefaultSource = strJoin "\n"
  [ "include_rules"
  , "run &(genrules) --tup-rules $(ROOT)"
  , ""
  ]

let _tupconfigSource = strJoin "\n"
  [ ""
  ]

lang TestSpec
  -- === Public API ===

  syn DepStatus =
  | DepAvailable
  | DepUnavailable
  | DepImpossible

  syn Run =
  | Dont
  | Succ
  | Fail

  syn Step =
  | MidStep Int
  | OtherFile (String -> String)

  -- Default substitutions available in commands:
  -- * '%%' becomes just '%'
  -- * '%f' becomes the originating file
  -- * '%i' becomes a space-separated list of files in the `uses` field.
  -- * '%o' becomes the output file in `midStep.output`.
  type Api =
    -- Declare a new step with no outputs.
    { endStep : {uses : [Step], tag : String, cmd : String} -> Step
    -- Declare a new step with one output. *Must* use '%o' to
    -- designate the output.
    , midStep : {uses : [Step], tag : String, cmd : String} -> Step

    -- The function should take the basename of the current
    -- originating file, then produce path to another file. The
    -- returned path is interpreted as relative to the directory of
    -- the originating file.
    , file : (String -> String) -> Step

    -- Check if an external dependency is met, taking the current
    -- testing mode into account. The argument should do side-effects,
    -- typically running some command, to figure out the status of the
    -- dependency.
    , dependency : (() -> DepStatus) -> Bool
    -- Add new tests. First argument is a list of dependencies; if any
    -- is `false` then the returned steps will be set to
    -- `Dont`. Second argument is a predicate over the path; we'll
    -- only consider the last argument if it passes. The final
    -- argument is a list of steps to enable/disable/change for a
    -- given file. Will overwrite the `Run` status of the steps in the
    -- return sequence.
    , tests : [Bool] -> (String -> Bool) -> [(Step, Run)] -> ()
    }

  -- Give lists of all supported substituters, a list of directories
  -- to process, an optional path to the source file calling
  -- `testMain` (relative to the root of the project) and its compiled
  -- version, and a function to define tests. The first substituter is
  -- the default, if none is specified on the command line. If the
  -- source file and executable paths are provided we'll make sure the
  -- executable is up-to-date before running.
  sem testMain : [Substituter] -> [String] -> Option {src : String, exe : String} -> (Api -> ()) -> ()

  -- === Implementation ===

  sem substitute : Map Char {actual : String, deps : [String], friendly : String} -> String -> {actual : String, friendly : String, deps : [String]}
  sem substitute m = | str ->
    let f = lam rest.
      switch rest
      case "%%" ++ rest then ({actual = "%", friendly = "%", deps = []}, rest)
      case ['%', c] ++ rest then
        match mapLookup c m with Some sub
        then (sub, rest)
        else error (join ["Unknown command substitution '%", [c], "' in command: ", str])
      case "%" then
        error (concat "Lone '%' in command: " str)
      case [c] ++ rest then ({actual = [c], friendly = [c], deps = []}, rest)
      end in
    let merge = lam a. lam b.
      { actual = concat a.actual b.actual
      , friendly = concat a.friendly b.friendly
      , deps = concat a.deps b.deps
      } in
    recursive let work = lam curr. lam rest.
      if null rest then curr else
      match f rest with (here, rest) in
      work (merge curr here) rest in
    work {actual = "", friendly = "", deps = []} str

  syn Focus =
  | FocusNone
  | FocusDirectory String
  | FocusFiles [String]

  type InternalSpec =
    { uses : [Step]
    , tag : String
    , cmd : String
    , output : Bool
    }

  type Rule =
    { inputs : [String]
    , extraInputs : [String]
    , outputs : [String]
    , tag : String
    , command : String
    , friendlyCommand : String
    , dir : String
    }

  syn FileDep =
  | GenFile String
  | RealFile String

  type ResolvedSubstituter =
    { mkRule : String -> [FileDep] -> Bool -> InternalSpec -> (Rule, Option FileDep)
    }

  sem computeRules : Bool -> String -> [String] -> ((() -> DepStatus) -> Bool) -> [ResolvedSubstituter] -> (Api -> ()) -> Option (Set String) -> Focus -> [Rule]
  sem computeRules debug root paths dependencyMode substituters declareTests tags = | focus ->
    let sources = switch focus
      case FocusFiles files then
        switch partition (lam path. and (any (lam top. strStartsWith top path) paths) (fileExists path)) files
        case (files, []) then files
        case (_, invalid) then
          error (concat "Invalid test source(s): " (strJoin ", " invalid))
        end
      case FocusNone _ then
        let find = lam dir.
          filter (lam s. not (null s))
            (strSplit "\n" (sysRunCommand ["find", "-L", dir, "-type", "f"] "" root).stdout) in
        join (map find paths)
      case FocusDirectory dir then
        filter (lam s. not (null s))
          (strSplit "\n" (sysRunCommand ["find", "-L", dir, "-maxdepth", "1", "-type", "f"] "" root).stdout)
      end in

    let usedTags : Ref (Set String) = ref (setEmpty cmpString) in
    let tags : Option (Ref (Set String)) = optionMap ref tags in
    let steps : Ref [InternalSpec] = ref [] in
    let testFunctions : Ref [(String -> Bool, [(Step, Run)])] = ref [] in

    let mkStep = lam output. lam spec.
      (if setMem spec.tag (deref usedTags) then error (concat "Duplicate test tag: " spec.tag) else ());
      modref usedTags (setInsert spec.tag (deref usedTags));
      let id = length (deref steps) in
      let step = MidStep id in
      (match tags with Some tags then
        modref tags (setRemove spec.tag (deref tags))
       else ());
      modref steps (snoc (deref steps)
        { uses = spec.uses
        , tag = spec.tag
        , cmd = spec.cmd
        , output = output
        });
      step in
    let api : Api =
      { endStep = mkStep false
      , midStep = mkStep true
      , file = lam f. OtherFile f
      , dependency = dependencyMode
      , tests = lam dependencies. lam predicate. lam f.
        let f = if allb dependencies then f else
          map (lam x. (x.0, Dont ())) f in
        modref testFunctions (snoc (deref testFunctions) (predicate, f))
      } in
    declareTests api;
    let steps = deref steps in
    let testFunctions = deref testFunctions in

    (match tags with Some tags then
      if setIsEmpty (deref tags)
      then ()
      else error (concat "Unknown tag(s): " (strJoin ", " (setToSeq (deref tags))))
     else ());

    let processSource : String -> [Rule] = lam source.
      (if debug then
        printLn (join ["Processing ", source])
       else ());
      let processSubstituter = lam substituter.
        let fromStep : Step -> Int = lam st.
          switch st
          case MidStep i then i
          case OtherFile f then error "`api.tests` tried to change the `Run` status of a `file` step."
          end in
        let fmtPair : all a. (a -> Int) -> (a, Run) -> String = lam f. lam pair.
          let status = switch pair.1
            case Dont _ then "Dont"
            case Fail _ then "Fail"
            case Succ _ then "Succ"
            end in
          join ["(", (get steps (f pair.0)).tag, ", ", status, ")"] in
        let processFunction = lam acc. lam pairF.
          if pairF.0 source then
            (if debug then
              printLn (join ["  ✓  ", seq2string (fmtPair fromStep) pairF.1])
             else ());
            foldl (lam acc. lam pair. mapInsert (fromStep pair.0) pair.1 acc) acc pairF.1
          else
            (if debug then
              printLn (join ["   ✗ ", seq2string (fmtPair fromStep) pairF.1])
             else ());
            acc in
        let setSteps : Map Int Run = foldl processFunction (mapEmpty subi) testFunctions in
        (if debug then
          printLn (join ["  Result: ", seq2string (fmtPair (lam x. x)) (mapBindings setSteps)])
         else ());

        let mkRule = lam acc : ([Rule], Map Int FileDep). lam stepId. lam run.
          match acc with (rules, mids) in
          let spec = get steps stepId in
          let stepToFileDep = lam step. switch step
            case MidStep id then mapLookup id mids
            case OtherFile f then Some (RealFile (f (basename source)))
            end in
          match optionMapM stepToFileDep spec.uses with Some uses then
            switch run
            case Dont _ then (rules, mids)
            case Fail _ then (snoc rules (substituter.mkRule source uses false spec).0, mids)
            case Succ _ then
              match substituter.mkRule source uses true spec with (rule, mid) in
              (snoc rules rule, optionMapOr mids (lam mid. mapInsert stepId mid mids) mid)
            end
          else (rules, mids) in
        (mapFoldWithKey mkRule ([], mapEmpty subi) setSteps).0 in
      join (map processSubstituter substituters)
    in

    join (map processSource sources)

  sem formatTupRules : [Rule] -> String
  sem formatTupRules = | rules ->
    let f = lam rule. join
      [": ", strJoin " " rule.inputs
      , if null rule.extraInputs then "" else
        concat " | " (strJoin " " rule.extraInputs)
      , " |> ^ ", rule.friendlyCommand, "^ "
      , rule.command, " |> "
      , strJoin " " rule.outputs
      ] in
    strJoin "\n" (map f rules)

  sem formatTupFilter : Option (Set String) -> [Rule] -> [String]
  sem formatTupFilter tags = | rules ->
    let rules = match tags with Some tags
      then filter (lam rule. setMem rule.tag tags) rules
      else rules in
    let f = lam rule. concat "build/" (head rule.outputs) in
    map f rules

  sem formatMake : Option (Set String) -> [Rule] -> String
  sem formatMake tags = | rules ->
    let green = "\\033[0;32m" in
    let red = "\\033[0;31m" in
    let colorReset = "\\033[0m" in
    let passMark = join [green, "✓", colorReset] in
    let failMark = join [red, "✗", colorReset] in
    let prereq = match tags with Some tags
      then lam rule. if setMem rule.tag tags then cons ' ' (head rule.outputs) else ""
      else lam rule. cons ' ' (head rule.outputs) in
    let rule = lam rule. join
      [ head rule.outputs, " : "
      , strJoin " " rule.inputs
      , if null rule.extraInputs then "" else
        concat " | " (strJoin " " rule.extraInputs)
      , "\n\t@mkdir -p ", dirname (head rule.outputs)
      , "\n\t@cd ", rule.dir, "; if ", rule.command
      , "; then echo ", sysShellQuote (join [rule.dir, ": ", passMark, " ", rule.friendlyCommand])
      , "; else st=$$?; echo ", sysShellQuote (join [rule.dir, ": ", failMark, " ", rule.friendlyCommand])
      , " >&2; exit $$st; fi\n"
      ] in
    join
      [ "ROOT := $(realpath .)\n"
      , "__gen_test_rule .PHONY:", join (map prereq rules)
      , "\n\n", join (map rule rules)
      ]

  type RunFlags =
    { parallel : Option Int
    , keepGoing : Bool
    }

  sem runMake : RunFlags -> Option (Set String) -> [Rule] -> Int
  sem runMake flags tags = | rules ->
    let parallel = match flags.parallel with Some j
      then [concat "-j" (int2string j)]
      else [] in
    let keepGoing = if flags.keepGoing then ["-k"] else [] in
    sysWithTempFile (lam file.
      writeFile file (formatMake tags rules);
      let localFile = if eqi 0 (command "test -f Makefile")
        then ["-f", "Makefile"]
        else [] in
      exec "make" (join [["__gen_test_rule", "-f", file], localFile, parallel, keepGoing]))

  sem ensureTupSetup : Bool -> [String] -> ()
  sem ensureTupSetup force = | dirs ->
    recursive let confirmOrExit : String -> () = lam message.
      if force then () else
      print message;
      print " (Y/n):";
      flushStdout ();
      switch readLine ()
      case "" | "y" | "Y" then ()
      case "n" | "N" then printLn "Aborted"; exit 1
      case _ then confirmOrExit message
      end in

    (if sysCommandExists "tup" then () else
      error "Could not find 'tup' on your PATH, is it installed?");

    -- NOTE(vipa, 2026-04-10): It appears that running `mi eval` puts
    -- `mi` as argv[0] (even if the command starts with, e.g.,
    -- `build/mi eval` instead), which we detect here.
    (if eqString (head argv) "mi" then
      error "You seem to be running in interpreted mode, which is not supported with 'tup'. Please compile the test specification."
     else ());

    let requiredFiles = join
      [ ["build/tup.config"]
      , map (lam dir. concat dir "/Tuprules.tup") dirs
      , map (lam dir. concat dir "/Tupdefault") dirs
      ] in
    match partition (lam f. sysFileExists f) requiredFiles with (presentFiles, missingFiles) in

    -- NOTE(vipa, 2026-03-20): Ensure all required files exist
    (if null missingFiles then () else
      confirmOrExit (join ["Missing file(s): ", strJoin ", " missingFiles, "\nCreate them?"]);
      for_ missingFiles (lam file. switch file
        case _ ++ "/Tuprules.tup" then writeFile file _tuprulesSource
        case _ ++ "/Tupdefault" then writeFile file _tupdefaultSource
        case "build/tup.config" then writeFile file _tupconfigSource
        end));

    -- NOTE(vipa, 2026-03-20): Ensure existing files contain all required lines
    (if null presentFiles then () else
      sysWithTempDir (lam dir.
        let tuprules = concat dir "/Tuprules.tup" in writeFile tuprules _tuprulesSource;
        let tupdefault = concat dir "/Tupdefault" in writeFile tupdefault _tupdefaultSource;
        let tupconfig = concat dir "/tup.config" in writeFile tupconfig _tupconfigSource;
        let hasMissing = lam default. lam file. neqi 0
          (command (join ["! comm -2 -3 <(sort < ", default, ") <(sort < ", file, ") | grep -q '[^[:space:]]'"])) in
        let hasMissingLines =
          let f = lam file. switch file
            case _ ++ "/Tuprules.tup" then hasMissing tuprules file
            case _ ++ "/Tupdefault" then hasMissing tupdefault file
            case "build/tup.config" then hasMissing tupconfig file
            end in
          filter f presentFiles in
        if null hasMissingLines then () else
        let m = foldl (lam m. lam x. mapInsertWith concat (basename x) [x] m) (mapEmpty cmpString) hasMissingLines in
        printLn "The files below have missing lines. You can either:";
        printLn (join ["- Delete the files, so the next run of ", head argv, " can generate them."]);
        printLn "  Only do this if there are no other lines in there.";
        printLn "- Add the required lines manually. The lines are shown below.";
        let _drop : () = mapFoldWithKey
          (lam. lam kind. lam files.
            printLn "";
            printLn (snoc (strJoin ", " files) ':');
            printLn (switch kind
              case "Tuprules.tup" then _tuprulesSource
              case "Tupdefault" then _tupdefaultSource
              case "tup.config" then _tupconfigSource
              end))
          ()
          m in
        exit 1));

    (if eqi 0 (command "test -d .tup") then () else
      sysWithTempDir (lam dir.
        confirmOrExit "Tup is not initialized, would you like to initialize it?";
        -- NOTE(vipa, 2026-03-20): All this juggling is because `tup`
        -- requires a variant directory to be empty when it's
        -- initialized, but not later. We move the 'build' directory
        -- out of the way, copy back the 'tup.config' file, run 'tup
        -- read' which adds the variant, then put the 'build'
        -- directory back.
        command (join ["mv -t ", dir, " build"]);
        command "mkdir build";
        sysCopyFile (join [dir, "/build/tup.config"]) "build/tup.config";
        (if eqi 0 (command "tup init") then () else
          error "Failed to initialize 'tup'.");
        let res = sysRunCommand ["tup", "read"] "" "." in
        sysDeleteDir "build";
        command (join ["mv -t . ", dir, "/build"]);
        if eqi 0 res.returncode then () else
          error (join
            [ "Failed to initialize 'tup'. Output:\n"
            , res.stdout
            , "\nError:\n"
            , res.stderr
            ]));
      let leftoverMakeDirs = filter (lam dir. eqi 0 (command (concat "test -d build/" dir))) dirs in
      if null leftoverMakeDirs then () else
      printLn (concat "Leftover directories in 'build' from before tup initialization: " (strJoin ", " leftoverMakeDirs));
      confirmOrExit "Do you want to remove them (tup will complain otherwise)?";
      command (strJoin " " (cons "rm -r" (map (concat "build/") leftoverMakeDirs)));
      ());

    ()

  sem runTup : Bool -> [String] -> RunFlags -> Option (Set String) -> [Rule] -> Int
  sem runTup force dirs flags tags = | rules ->
    ensureTupSetup force dirs;
    let parallel = match flags.parallel with Some n
      then [concat "-j" (int2string n)]
      else [] in
    let keepGoing = if flags.keepGoing
      then ["-k"]
      else [] in
    let targets = formatTupFilter tags rules in
    if null targets
    then printLn "No tests specified, did not run tup."; 0
    else exec "tup" (join [parallel, keepGoing, targets])

  sem runStats : [Rule] -> [Rule] -> Int
  sem runStats selectedRules = | allRules ->
    let countByDir = foldl
      (lam acc. lam rule. mapInsertWith addi (dirname (head rule.outputs)) 1 acc)
      (mapEmpty cmpString) in
    let byDir = mapMerge (lam l. lam r. Some (optionGetOr 0 l, optionGetOr 0 r))
      (countByDir selectedRules)
      (countByDir allRules) in
    printLn "Directory\tEnabled\tDisabled";
    let _unused : () = mapFoldWithKey
      (lam. lam path. lam counts.
        printLn (join [path, "\t", int2string counts.0, "\t", int2string (subi counts.1 counts.0)]))
      ()
      byDir in
    let selectedRules = length selectedRules in
    let allRules = length allRules in
    printLn (join ["Found ", int2string selectedRules, " tests to run in total (", int2string (subi allRules selectedRules), " disabled due to dependencies)."]);
    0

  sem runListTargets : [Rule] -> Int
  sem runListTargets = | rules ->
    for_ rules (lam r. printLn (concat "build/" (head r.outputs)));
    0

  sem runListTags : [Rule] -> Int
  sem runListTags = | rules ->
    for_ (setToSeq (setOfSeq cmpString (map (lam rule. rule.tag) rules))) (lam tag. printLn tag);
    0

  sem runWatch : [String] -> Option {src : String, exe : String} -> Int
  sem runWatch paths = | loc ->
    (if sysCommandExists "entr" then () else
      error "Could not find 'entr' on your PATH, is it installed?");
    -- NOTE(vipa, 2026-04-10): It appears that running `mi eval` puts
    -- `mi` as argv[0] (even if the command starts with, e.g.,
    -- `build/mi eval` instead), which we detect here.
    (if eqString (head argv) "mi" then
      error "You seem to be running in interpreted mode, which is not supported with '--watch'. Please compile the test specification."
     else ());

    let printWatchList = strJoin "; "
      (map (lam path. join ["find -L ", sysShellQuote path, " -type f"]) paths) in
    let printWatchList = match loc with Some loc
      then join ["echo ", sysShellQuote loc.src, "; ", printWatchList]
      else printWatchList in
    let runEntr =
      let args = filter (lam str. not (eqString "--watch" str)) (tail argv) in
      join ["entr -rccd ", sysShellQuote (head argv), " ", strJoin " " (map sysShellQuote args)] in
    let cmd = join ["set -o pipefail; { ", printWatchList, "; } | ", runEntr] in
    recursive let work = lam.
      -- NOTE(vipa, 2026-04-10): 'entr' will exit with '2' if a new
      -- file is added to a directory under watch, in which case we
      -- want to restart the watch with the new file.
      match command cmd with 2
      then work ()
      else 0 in
    work ()

  sem resolveTupRules : Substituter -> ResolvedSubstituter
  sem resolveTupRules = | sub -> resolveSubstituter
    { subMap = mapMap
      (lam x. {actual = x.tup.actual, deps = x.tup.deps, friendly = x.friendly})
      sub.substitutions
    , subName = sub.flag
    , actual = {i = "%f", o = "%1o"}
    , postprocessOutputPath = basename
    , printPathInCommand = lam x. join ["%", int2string (addi x.outputIdx 1), "o"]
    }

  sem resolveTupFilter : Substituter -> ResolvedSubstituter
  sem resolveTupFilter = | sub -> resolveSubstituter
    { subMap = mapMap
      (lam x. {actual = x.tup.actual, deps = x.tup.deps, friendly = x.friendly})
      sub.substitutions
    , subName = sub.flag
    , actual = {i = "%f", o = "%1o"}
    , postprocessOutputPath = lam x. x
    , printPathInCommand = lam x. join ["%", int2string (addi x.outputIdx 1), "o"]
    }

  sem resolveMake : Substituter -> ResolvedSubstituter
  sem resolveMake = | sub -> resolveSubstituter
    { subMap = mapMap
      (lam x. {actual = x.make.actual, deps = x.make.deps, friendly = x.friendly})
      sub.substitutions
    , subName = sub.flag
    , actual = {i = "$^", o = "$@"}
    , postprocessOutputPath = lam x. concat "$(ROOT)/build/" x
    , printPathInCommand = lam x. x.outputPath
    }

  sem negateCommand : Rule -> Rule
  sem negateCommand = | cmd ->
    { cmd with friendlyCommand = concat "XFAIL " cmd.friendlyCommand
    , command = join ["! { ", cmd.command, "; }"]
    }

  sem captureAndPrint : (Int -> String -> {inCommand : String, inOutputs : String}) -> Rule -> (Rule, String)
  sem captureAndPrint f = | rule ->
    let out = f (length rule.outputs) "out" in
    let err = f (addi (length rule.outputs) 1) "err" in
    ( { rule with outputs = concat rule.outputs [out.inOutputs, err.inOutputs]
      , command = join
        [ "{ ", rule.command, "; } >", out.inCommand, " 2>", err.inCommand
        , " || { $(ROOT)/build/__elide-cat stdout '", out.inCommand
        , "'; $(ROOT)/build/__elide-cat stderr '", err.inCommand
        , "'; false; }"
        ]
      }
    , out.inOutputs
    )

  sem ensureElideCat : () -> ()
  sem ensureElideCat = | _ ->
    let goodFileExists =
      if sysFileExists "build/__elide-cat"
      then eqString (readFile "build/__elide-cat") _elideCatSource
      else false in
    if goodFileExists then () else
    writeFile "build/__elide-cat" _elideCatSource;
    (if eqi 0 (sysChmodExecuteFile "build/__elide-cat") then () else
      error "Could not make 'build/__elide-cat' executable")

  type ResolveConfig =
    { subMap : Map Char {actual : String, deps : [String], friendly : String}
    , subName : String
    , actual : {i : String, o : String}
    , postprocessOutputPath : String -> String
    , printPathInCommand : { outputIdx : Int, outputPath : String } -> String
    }
  sem resolveSubstituter : ResolveConfig -> ResolvedSubstituter
  sem resolveSubstituter = | conf ->
    let formatPathParts = lam parts. strJoin "." (filter (lam x. not (null x)) parts) in
    let formatOutputPath = lam input. lam tag.
      conf.postprocessOutputPath (formatPathParts [input, conf.subName, tag]) in
    let formatPrintPath = lam input. lam tag. lam idx. lam outKind.
      let path = conf.postprocessOutputPath (formatPathParts [input, conf.subName, tag, outKind]) in
      { inCommand = conf.printPathInCommand {outputIdx = idx, outputPath = path}
      , inOutputs = path
      } in
    let prepSubmap = lam source. lam uses. lam actual. lam subMap.
      let base = basename source in
      let subMap = mapInsert 'f' {actual = base, friendly = base, deps = []} subMap in
      let f = lam acc. lam x. switch x
        case GenFile x then (snoc acc.0 x, acc.1)
        case RealFile x then (acc.0, snoc acc.1 x)
        end in
      match foldl f ([], []) uses with (gens, reals) in
      let basedGens = map basename gens in
      let actual = if null gens
        then strJoin " " reals
        else join [actual.i, " ", strJoin " " reals] in
      let subMap = mapInsert 'i' {actual = actual, friendly = strJoin " " (concat basedGens reals), deps = []} subMap in
      subMap in
    let mkRule = lam source. lam uses. lam succ. lam spec.
      let subMap = prepSubmap source uses conf.actual conf.subMap in
      let output = if spec.output then Some (formatOutputPath source spec.tag) else None () in
      let subMap = match output with Some output
        then mapInsert 'o' {actual = conf.actual.o, friendly = basename output, deps = []} subMap
        else subMap in
      let res = substitute subMap spec.cmd in
      let rule : Rule =
        { inputs = mapOption (lam x. match x with GenFile x then Some x else None ()) uses
        , extraInputs = res.deps
        , outputs = optionMapOr [] (lam x. [x]) output
        , tag = spec.tag
        , command = if and (not succ) spec.output
          then join ["{ ", res.actual, "; } || { touch ", conf.actual.o, "; false; } "]
          else res.actual
        , friendlyCommand = res.friendly
        , dir = dirname source
        } in
      let rule = if succ then rule else negateCommand rule in
      match captureAndPrint (formatPrintPath source spec.tag) rule with (rule, stdout) in
      (rule, if succ then Some (GenFile (optionGetOr stdout output)) else None ()) in
    {mkRule = mkRule}

  sem checkAtRootAndUpToDate : Option {src : String, exe : String} -> ()
  sem checkAtRootAndUpToDate =
  | Some loc ->
    if eqi 0 (command (concat "test -f " (sysShellQuote loc.src))) then
      let needsCompile = neqi 0 (command (join ["test ", sysShellQuote loc.exe, " -nt ", sysShellQuote loc.src])) in
      (if needsCompile then
        printLn (join ["Compiling '", loc.src, "' to '", loc.exe, "'..."]);
        (if eqi 0 (command (join ["mkdir -p ", sysShellQuote (dirname loc.exe)])) then () else
          exit 1);
        (if sysCommandExists "mi" then () else
          error "Could not find 'mi' on your PATH, is it installed?");
        switch command (join ["mi compile ", sysShellQuote loc.src, " --output ", sysShellQuote loc.exe])
        case 0 then ()
        case code then exit code
        end
       else ());
      let needsReRun = if needsCompile then true else not (eqString (head argv) loc.exe) in
      if needsReRun then
        printLn (join ["Running compiled '", loc.exe, "'"]);
        exec loc.exe (tail argv)
      else ()
    else error (join ["Could not find '", loc.src, "'. Are you at the root of the project?"])
  | None _ ->
    if eqi 0 (command "test -d build") then () else
    error "Could not find a 'build' folder. Are you at the root of the project, and have you created 'build'?"

  sem testMain substituters paths sourceLocation = | declareTests ->
    let catInternal = "Internal commands:" in
    let catMode = "Build system flags:" in
    let catSubstituters = "Test mode flags:" in
    let catDependency = "Dependency flags:" in
    let catRun = "Running flags:" in

    let tupRules = optArg
      { optArgDefString with long = "tup-rules"
      , arg = "<root-directory>"
      , description = "Generate all commands in the current directory in the format `tup` expects."
      , category = catInternal
      } in
    let tupRules = optMap
      (lam dir.
        let focus = strTrim (sysRunCommand ["realpath", "--relative-to", dir, "."] "" ".").stdout in
        let rules = computeRules false dir paths (lam. true) (map resolveTupRules substituters) declareTests (None ()) (FocusDirectory focus) in
        match formatTupRules rules with str & !""
        then printLn str; exit 0
        else exit 0)
      tupRules in

    let makeMode = lam flags. lam debug. lam dependencyMode. lam subs. lam tags. lam focus.
      runMake flags tags (computeRules debug "." paths dependencyMode (map resolveMake subs) declareTests tags focus) in
    let tupMode = lam force. lam flags. lam debug. lam dependencyMode. lam subs. lam tags. lam focus.
      runTup force paths flags tags (computeRules debug "." paths dependencyMode (map resolveTupFilter subs) declareTests tags focus) in
    let statsMode = lam flags. lam debug. lam dependencyMode. lam subs. lam tags. lam focus.
      (if optionIsSome tags then
        printErrorLn "Warning: --stats does not take --tag into account, enabled tests may be fewer than reported."
       else ());
      runStats
        (computeRules debug "." paths dependencyMode (map resolveTupFilter subs) declareTests tags focus)
        (computeRules false "." paths (lam. true) (map resolveTupFilter subs) declareTests (None ()) focus) in
    let listTargetsMode = lam flags. lam debug. lam dependencyMode. lam subs. lam tags. lam focus.
      (if optionIsSome tags then
        printErrorLn "Warning: --targets does not take --tag into account, enabled tests may be fewer than reported."
       else ());
      runListTargets
        (computeRules debug "." paths dependencyMode (map resolveTupFilter subs) declareTests tags focus) in
    let listTagsMode = lam flags. lam debug. lam dependencyMode. lam subs. lam tags. lam focus.
      (if optionIsSome tags then
        printErrorLn "Warning: --tags does not take --tag into account, relevant tags may be fewer than reported."
       else ());
      runListTags
        (computeRules debug "." paths dependencyMode (map resolveTupFilter subs) declareTests tags focus) in
    let checkDefaultMode = lam.
      if eqi 0 (command "test -e .tup")
      then tupMode false
      else makeMode in

    let make = optNoArg
      { optNoArgDef makeMode with long = "make"
      , description = "Run tests via 'make', i.e., always run. Default if '.tup' doesn't exist."
      , category = catMode
      } in
    let tup = optNoArg
      { optNoArgDef tupMode with long = "tup"
      , description = "Run tests via 'tup', i.e., run only if something has changed. Default if '.tup' exists."
      , category = catMode
      } in
    let tup = optApply tup (optFlag
      { optFlagDef with short = "y"
      , description = "Answer all interactive questions with 'yes'."
      , category = catMode
      }) in
    let stats = optNoArg
      { optNoArgDef statsMode with long = "stats"
      , description = "Don't run tests, just print number of tests that would be run."
      , category = catMode
      } in
    let listTargets = optNoArg
      { optNoArgDef listTargetsMode with long = "targets"
      , description = "Don't run tests, just print all primary targets that would be created."
      , category = catMode
      } in
    let listTags = optNoArg
      { optNoArgDef listTagsMode with long = "tags"
      , description = "Don't run tests, just print all tags used for enabled tests."
      , category = catMode
      } in

    let substituters =
      match substituters with [substituter] then optPure [substituter] else
      let mkFlag = lam sub. optOr (optNoArg
        { optNoArgDef [sub] with long = sub.flag
        , description = sub.description
        , category = catSubstituters
        }) (optPure []) in
      let f = lam opt. lam sub.
        optMap2 concat opt (mkFlag sub) in
      optMap (lam l. if null l then [head substituters] else l) (foldl f (optPure []) substituters) in

    let debug = optFlag
      { optFlagDef with long = "debug"
      , description = "Debug the test declaration, see why tests are run. Typically used with '--stats' or '--targets' and an explicit test-origin."
      } in

    let dependencyMode =
      let noneDep = lam f. false in
      let smartDep = lam f. match f () with DepAvailable _ then true else false in
      let mostDep = lam f. match f () with !DepImpossible _ then true else false in
      let allDep = lam f. true in
      let noneF = optNoArg
        { optNoArgDef noneDep with long = "none-dep"
        , description = "Do not include any tests that have external dependencies."
        , category = catDependency
        } in
      let smartF = optNoArg
        { optNoArgDef smartDep with long = "smart-dep"
        , description = "Include tests using external dependencies that are installed. Default."
        , category = catDependency
        } in
      let mostF = optNoArg
        { optNoArgDef mostDep with long = "most-dep"
        , description = "Include tests using external dependencies that *could be* installed (e.g., required hardware present, but required software absent)."
        , category = catDependency
        } in
      let allF = optNoArg
        { optNoArgDef allDep with long = "all-dep"
        , description = "Include *all* tests using external dependencies, whether they could be installed or not."
        , category = catDependency
        } in
      foldl1 optOr [noneF, smartF, mostF, allF, optPure smartDep] in

    let tags = optOptional (optMap (setOfSeq cmpString) (optSome (optArg
      { optArgDefString with long = "tag"
      , arg = "<tag>"
      , description = "Only run tests with the given tag (and their dependencies)."
      }))) in

    let focusPaths = optPos
      { optPosDefString with arg = "<test-origin>"
      , description = "Run only tests from these files, if present, otherwise from all files."
      } in
    let focusPaths = optMap (lam xs. if null xs then FocusNone () else FocusFiles xs) (optMany focusPaths) in

    let watch : OptParser Bool = optFlag
      { optFlagDef with long = "watch"  -- NOTE(vipa, 2026-04-10): The string used here is significant, search for `--watch` for other uses
      , description = "Watch files with 'entr' and rerun tests when anything changes."
      } in

    let runFlags : OptParser RunFlags =
      let parallel = optOptional (optArg
        { optArgDefInt with short = "j", arg = "N"
        , description = "Run tests in parallel with at most N processes at once."
        , category = catRun
        }) in
      let keepGoing = optFlag
        { optFlagDef with short = "k"
        , description = "Keep going even if tests fail."
        , category = catRun
        } in
      optMap2 (lam parallel. lam keepGoing. {parallel = parallel, keepGoing = keepGoing})
        parallel keepGoing in

    let optParser = optOr tupRules
      (optApply3 (optMap5
        (lam mode. lam subs. lam debug. lam dependencyMode. lam flags. lam watch. lam tags. lam focus.
          let mode = optionGetOrElse checkDefaultMode mode in
          checkAtRootAndUpToDate sourceLocation;
          ensureElideCat ();
          if watch
          then exit (runWatch paths sourceLocation)
          else exit (mode flags debug dependencyMode subs tags focus))
        (optOptional (optOr (optOr (optOr (optOr make tup) stats) listTargets) listTags))
        substituters
        debug
        dependencyMode
        runFlags)
        watch
        tags
        focusPaths) in

    let help =
      { optParserHelpDef (head argv)
        with description = strJoin "\n"
        [ "Generate a description of tests included in a test suite."
        , ""
        , "Expects to be run from the root of the repository, and will"
        , "place all outputs under './build', in a structure mirroring"
        , "the normal repository. For example, if a test originated at"
        , "'src/test/foo.mc', then all testing results can be found at"
        , "'build/src/test/foo.mc.*' (including stdout and stderr)."
        , ""
        , "There are two primary modes of operation:"
        , "- make, which always runs all selected tests."
        , "- tup, which tracks dependencies and only runs tests with"
        , "  updates."
        ]
      } in
    printLn (optParseWithHelp help optParser (tail argv))
end
