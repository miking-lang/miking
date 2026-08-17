include "stdlib::test-spec.mc"

mexpr

use TestSpec in

let installed : Substituter =
  { flag = "installed"
  , description = "Run tests with a previously installed `mi` on `$PATH`."
  , substitutions = mapFromSeq cmpChar
    [ ( 'm'
      , { tup = {actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib mi", deps = []}
        , make = {actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib mi", deps = []}
        , friendly = "INSTALLED MI"
        }
      )
    ]
  } in
let cheated : Substituter =
  { flag = "cheat"
  , description = "Build a new `mi` using an installed `mi` in one step, then use it for tests."
  , substitutions = mapFromSeq cmpChar
    [ ( 'm'
      , { tup =
          { actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib OCAMLPATH=$(VARIANT_SRC)/lib${OCAMLPATH:+:}$OCAMLPATH %<mi-cheat>"
          , deps = ["$(ROOT)/src/<mi-cheat>", "$(ROOT)/src/<boot-lib>"]
          }
        , make =
          { actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib OCAMLPATH=$(ROOT)/build/lib$${OCAMLPATH:+:}$$OCAMLPATH $(ROOT)/build/mi-cheat"
          , deps = ["build/mi-cheat"]
          }
        , friendly = "CHEAT MI"
        }
      )
    ]
  } in
let bootstrapped : Substituter =
  { flag = "boot"
  , description = "Build a new `mi` from scratch, then use it for tests."
  , substitutions = mapFromSeq cmpChar
    [ ( 'm'
      , { tup =
          { actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib OCAMLPATH=$(ROOT)/build/src/lib${OCAMLPATH:+:}$OCAMLPATH %<mi>"
          , deps = ["$(ROOT)/src/<mi>", "$(ROOT)/src/<boot-lib>"]
          }
        , make =
          { actual = "MCORE_LIBS=stdlib=$(ROOT)/src/stdlib OCAMLPATH=$(ROOT)/build/lib$${OCAMLPATH:+:}$$OCAMLPATH $(ROOT)/build/mi"
          , deps = ["build/mi"]
          }
        , friendly = "BOOT MI"
        }
      )
    ]
  } in

let substituters =
  [ cheated
  , bootstrapped
  , installed
  ] in
let directories = ["src"] in
let location = Some
  { src = "misc/test-spec.mc"
  , exe = "misc/test"
  } in
testMain substituters directories location (lam api.
  let succ = Succ () in
  let fail = Fail () in
  let dont = Dont () in
  let and = lam l. lam r. lam x. if l x then r x else false in
  let or = lam l. lam r. lam x. if l x then true else r x in
  let elem = lam elems.
    let set = setOfSeq cmpString elems in
    lam x. setMem x set in
  let dirIs = lam dir. lam path. eqString dir (dirname path) in

  let origin = api.file (lam x. x) in

  let owl = api.dependency (lam.
    if eqi 0 (command "ocamlfind query owl >/dev/null 2>&1")
    then DepAvailable ()
    else DepUnavailable ()) in
  let sundials = api.dependency (lam.
    if eqi 0 (command "ocamlfind query sundialsml >/dev/null 2>&1")
    then DepAvailable ()
    else DepUnavailable ()) in
  let lwt = api.dependency (lam.
    if eqi 0 (command "ocamlfind query lwt >/dev/null 2>&1")
    then DepAvailable ()
    else DepUnavailable ()) in
  let toml = api.dependency (lam.
    if eqi 0 (command "ocamlfind query toml >/dev/null 2>&1")
    then DepAvailable ()
    else DepUnavailable ()) in
  let minizinc = api.dependency (lam.
    if sysCommandExists "minizinc"
    then DepAvailable ()
    else DepUnavailable ()) in
  let node = api.dependency (lam.
    if sysCommandExists "node"
    then DepAvailable ()
    else DepUnavailable ()) in
  let javac = api.dependency (lam.
    if sysCommandExists "javac"
    then DepAvailable ()
    else DepUnavailable ()) in

  -- === Basic tests of `.mc` files ===

  -- All `.mc` tests are interpreted and compiled, unless otherwise
  -- stated later
  let eval = api.endStep
    { uses = [origin]
    , tag = "eval"
    , cmd = "%m eval --disable-prune-utests --test %i"
    } in
  let compile = api.midStep
    { uses = [origin]
    , tag = "compile"
    , cmd = "%m compile --disable-prune-utests --test %i --output %o"
    } in
  let run = api.endStep
    { uses = [compile]
    , tag = "run"
    , cmd = "command %i"
    } in
  api.tests []
    (strEndsWith ".mc")
    [(eval, succ), (compile, succ), (run, succ)];

  -- The compiler itself is tested through the bootstrap process, so
  -- skip it here
  api.tests []
    (eqString "src/main/mi.mc")
    [(eval, dont), (compile, dont), (run, dont)];

  -- Python is only supported in boot
  api.tests []
    (elem ["src/stdlib/python/python.mc", "src/test/py/python.mc"])
    [(eval, fail), (compile, fail)];

  -- Inconveniently slow when interpreting, so we skip that part
  api.tests []
    (elem
      [ "src/stdlib/parser/lrk.mc"
      , "src/stdlib/parray.mc"
      , "src/stdlib/peval/compile.mc"
      , "src/stdlib/tuning/tune.mc"
      , "src/stdlib/mexpr/generate-json-serializers.mc"
      ])
    [(eval, dont)];

  -- Files that are expected to compile, but then fail
  api.tests []
    (elem
      [ "src/test/examples/utest/utest.mc"
      , "src/test/examples/utest/utest-with-onfail.mc"
      , "src/test/examples/test-prune-utests.mc"
      ])
    [(eval, fail), (run, fail)];

  -- Files using externals not available in the interpreter
  api.tests []
    (elem
      [ "src/stdlib/ext/file-ext.mc"
      , "src/stdlib/ext/array-ext.mc"
      , "src/stdlib/ext/ext-test.mc"
      , "src/stdlib/ext/local-search.mc"
      , "src/stdlib/ext/arr-ext.mc"
      , "src/stdlib/ext/reflection-ext.mc"
      , "src/test/examples/external/ext-list-map.mc"
      , "src/test/examples/external/ext-list-concat-map.mc"
      , "src/stdlib/multicore/atomic.mc"
      , "src/stdlib/multicore/atomic.mc"
      , "src/stdlib/multicore/channel.mc"
      , "src/stdlib/multicore/thread.mc"
      , "src/stdlib/multicore/thread-pool.mc"
      , "src/stdlib/multicore/cond.mc"
      , "src/stdlib/multicore/mutex.mc"
      , "src/stdlib/multicore/pseq.mc"
      , "src/stdlib/stats.mc"
      , "src/stdlib/math.mc"
      , "src/main/docgen.mc"
      , "src/stdlib/docgen/global/ext-utils.mc"
      , "src/stdlib/docgen/global/file-opener.mc"
      , "src/stdlib/docgen/scanning/docgen-ignore.mc"
      , "src/stdlib/docgen/scanning/scanner.mc"
      , "src/stdlib/docgen/parsing/parser.mc"
      , "src/stdlib/docgen/execution-context.mc"
      , "src/stdlib/docgen/docgen.mc"
      , "src/stdlib/docgen/rendering/files-opener.mc"
      , "src/stdlib/docgen/rendering/renderer.mc"
      , "src/stdlib/docgen/rendering/renderers/mdx-renderer.mc"
      , "src/stdlib/docgen/rendering/renderers/html-renderer.mc"
      , "src/stdlib/docgen/rendering/renderers/raw-renderer.mc"
      , "src/stdlib/docgen/rendering/renderers/main-renderer.mc"
      , "src/stdlib/docgen/mast-gen/file-opener.mc"
      , "src/stdlib/docgen/mast-gen/mast-generator.mc"
      , "src/stdlib/docgen/server/server.mc"
      , "src/stdlib/docgen/server/python-server.mc"
      ])
    [(eval, fail)];

  -- Files that *should* fail to compile
  api.tests []
    (elem
      [ "src/test/examples/external/ext-not-applied-parse-error.mc"
      , "src/test/examples/external/ext-not-fully-applied-parse-error.mc"
      , "src/test/examples/external/ext-parse.mc"
      , "src/test/examples/external/multiple-ext-parse-error.mc"
      ])
    [(eval, fail), (compile, fail)];

  -- TODO(vipa, 2024-11-08): Files that fail to compile, but I
  -- don't know why
  api.tests []
    (eqString "src/test/examples/external/ext-removal.mc")
    [(eval, fail), (compile, fail)];

  -- TODO(vipa, 2024-11-08): Files that fail to run, but I
  -- don't know why
  api.tests []
    (eqString "src/test/examples/peval/pow.mc")
    [(eval, fail), (run, fail)];

  -- This tests more fancy name-spacing stuff (e.g., include
  -- "test:path/in/test"), which isn't supported in this testing
  -- system
  api.tests []
    (eqString "src/test/mlang/include.mc")
    [(eval, fail), (compile, fail)];

  -- === Microbenchmark ===

  let runBench = api.endStep
    { uses = [compile]
    , tag = "bench-run"
    , cmd = "%i 1"
    } in
  -- NOTE(vipa, 2023-05-16): We arbitrarily run with argument 1,
  -- since we're just testing, not benchmarking
  -- NOTE(vipa, 2024-11-13): We skip interpretation, since many of
  -- those end up quite slow
  -- TODO(vipa, 2026-04-08): I'm not sure that *all* of these require
  -- owl, so we might be able to be a bit more specific
  api.tests [owl]
    (and (strStartsWith "src/test/microbenchmark/") (strEndsWith ".mc"))
    [(eval, dont), (run, dont), (runBench, succ)];

  api.tests []
    (eqString "src/test/examples/json/perftest-mc.mc")
    [(eval, dont), (run, dont), (runBench, dont)];

  -- === Constraint programming ===

  api.tests [minizinc]
    (and (strStartsWith "src/stdlib/cp/") (strEndsWith ".mc"))
    [(eval, succ), (compile, succ), (run, succ)];

  -- === Tuning ===

  let tuneCompile = api.midStep
    { uses = [origin]
    , tag = "tune-exe"
    , cmd = "%m tune %i --test --disable-optimizations --compile --disable-exit-early --enable-cleanup --output %o"
    } in
  let tuneRun = api.endStep
    { uses = [tuneCompile]
    , tag = "tune-run"
    , cmd = "command %i"
    } in
  api.tests []
    (and (strStartsWith "src/test/examples/tuning/") (strEndsWith ".mc"))
    [(eval, dont), (compile, dont), (tuneCompile, succ), (tuneRun, succ)];

  -- === Javascript ===

  let jsCompile = api.midStep
    { uses = [origin]
    , tag = "js"
    , cmd = "%m compile --test --disable-prune-utests --to-js --js-target node %i --output %o"
    } in
  let jsRun = api.endStep
    { uses = [jsCompile]
    , tag = "run-js"
    , cmd = "node %i"
    } in
  let jsDiff = api.endStep
    { uses = [run, jsRun]
    , tag = "diff-js"
    , cmd = "diff %i"
    } in

  -- NOTE(vipa, 2024-11-13): The tests using web APIs seem broken (and
  -- aren't run in the previous test suite), so we leave them for now
  -- NOTE(vipa, 2024-11-13): There are benchmarks also, but they
  -- output in-tree, and aren't currently run by the test suite, so we
  -- leave them
  api.tests [node]
    (and (or (strStartsWith "src/test/js/benchmarks/") (strStartsWith "src/test/js/web/")) (strEndsWith ".mc"))
    [(eval, dont), (compile, dont)];

  api.tests [node]
    (and (dirIs "src/test/js") (strEndsWith ".mc"))
    [(jsCompile, succ), (jsRun, succ), (jsDiff, succ)];

  -- === MLang pipeline ===

  let mlangCompile = api.midStep
    { uses = [origin]
    , tag = "mlang-exe"
    , cmd = "%m compile --test --mlang-pipeline %i --output %o"
    } in
  let mlangRun = api.endStep
    { uses = [mlangCompile]
    , tag = "mlang-run"
    , cmd = "command %i"
    } in

  api.tests []
    (elem
      [ "src/stdlib/bool.mc"
      , "src/stdlib/option.mc"
      , "src/stdlib/char.mc"
      , "src/stdlib/seq.mc"
      , "src/stdlib/map.mc"
      -- TODO(vipa, 2024-11-14): This one should work, it does in
      -- the original, but doesn't here for some reason
      -- , "stdlib/mexpr/symbolize.mc"
      ])
    [(mlangCompile, succ), (mlangRun, succ)];

  -- === Java ===

  -- NOTE(vipa, 2024-11-07): The `--to-jvm` flag of `mi compile` just
  -- prints a json representation of some kind (to stdout), testing is
  -- currently not using that path at all, but rather manual code in
  -- the corresponding compile.mc file. Presumably rectified in #710.

  -- NOTE(vipa, 2024-11-14): The Java tests (specifically compile.mc)
  -- work in a fixed temporary directory, i.e., it cannot be run in
  -- parallel with itself, i.e., we skip interpretation, so it's just
  -- one such test that runs. This is definitely something we want to
  -- fix.
  api.tests [javac]
    (and (strStartsWith "src/stdlib/jvm/") (strEndsWith ".mc"))
    [(eval, dont), (compile, succ), (run, succ)];

  -- === Constructor types ===

  let constructorTypesCompile = api.midStep
    { uses = [origin]
    , tag = "constructor-types-compile"
    , cmd = "%m compile --test --enable-constant-fold --disable-prune-utests --enable-constructor-types %i --output %o"
    } in
  let constructorTypesRun = api.endStep
    { uses = [constructorTypesCompile]
    , tag = "constructor-types-run"
    , cmd = "command %i"
    } in

  -- NOTE(vipa, 2024-11-08): This file contains constructor types
  -- syntax, thus we exclude it from normal testing
  api.tests []
    (eqString "src/test/mexpr/types.mc")
    [(eval, dont), (compile, dont)];

  api.tests []
    (and
      (or (dirIs "src/stdlib") (dirIs "src/test/mexpr"))
      (strEndsWith ".mc"))
    [(constructorTypesCompile, succ), (constructorTypesRun, succ)];
  api.tests []
    (elem
      [ "src/stdlib/effect.mc"
      , "src/test/mexpr/pprint-eval.mc"
      , "src/stdlib/optparse-applicative.mc"
      ])
    [(constructorTypesCompile, fail)];

  -- === Prerun ===

  api.tests []
    (and (strStartsWith "src/test/meta/") (strEndsWith ".mc"))
    [(eval, fail), (compile, fail)];
  api.tests []
    (eqString "src/test/meta/recursive-let.mc")
    [(eval, fail), (compile, succ), (run, succ)];

  -- === Sundials ===

  api.tests [sundials]
    (and (strStartsWith "src/stdlib/sundials/") (strEndsWith ".mc"))
    [(eval, succ), (compile, succ), (run, succ)];
  api.tests [sundials]
    (elem
      [ "src/stdlib/sundials/cvode.mc"
      , "src/stdlib/sundials/ida.mc"
      , "src/stdlib/sundials/kinsol.mc"
      ])
    [(eval, fail)];

  -- === lwt ===

  api.tests [lwt]
    (eqString "src/stdlib/ext/async-ext.mc")
    [(eval, fail), (compile, succ), (run, succ)];

  -- NOTE(vipa, 2024-11-25): This doesn't terminate in a reasonable
  -- amount of time
  api.tests [lwt]
    (eqString "src/test/examples/async/tick.mc")
    [(eval, dont), (compile, succ), (run, dont)];

  -- === Owl ===

  api.tests [owl]
    (elem
      [ "src/stdlib/ext/math-ext.mc"
      , "src/stdlib/ext/matrix-ext.mc"
      , "src/stdlib/ext/dist-ext.mc"
      , "src/stdlib/ext/cblas-ext.mc"
      , "src/stdlib/ext/mat-ext.mc"
      , "src/stdlib/ext/vec-ext.mc"
      ])
    [(eval, fail), (compile, succ), (run, succ)];

  -- === toml ===

  api.tests [toml]
    (elem
      [ "src/stdlib/ext/toml-ext.mc"
      , "src/stdlib/tuning/tune-options.mc"
      ])
    [(eval, fail), (compile, succ), (run, succ)];

  -- === LR(k) ===

  let lrkCompile = api.midStep
    { uses = [origin]
    , tag = "lrk-compile"
    , cmd = "%m compile %i --output %o"
    } in
  let lrkGen = api.midStep
    { uses = [lrkCompile]
    , tag = "lrk-gen"
    , cmd = "%i %o"
    } in
  let lrkGenCompile = api.midStep
    { uses = [lrkGen]
    , tag = "lrk-gen-compile"
    , cmd = "%m compile %i --output %o"
    } in
  -- let lrkGenRun = api.endStep
  --   { uses = [lrkGenCompile, api.file (withExtension ".input")]
  --   , tag = "lrk-gen-run"
  --   , cmd = "%i "
  --   } in

  api.tests []
    (and (strStartsWith "src/test/examples/parser/") (strEndsWith ".mc"))
    [(eval, dont), (compile, dont), (lrkCompile, succ), (lrkGen, succ), (lrkGenCompile, succ)];

  ()
);

()


-- NOTE(vipa, 2024-11-13): Workaround for overeager dead code
-- elimination, putting this here puts the above call to testMain
-- along the spine of the program, which means things in its argument
-- will not be DCEd. See https://github.com/miking-lang/miking/issues/875
; ()
