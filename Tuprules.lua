if #tup.glob('.gitignore') == 0 then
  -- Only automatically generate a .gitignore if there isn't one in
  -- the cwd already. We assume that a pre-existing .gitignore already
  -- covers what tup would generate. This is to avoid spurious edits
  -- to .gitignores.
  tup.creategitignore()
end

if root then
  -- root is already defined, this means that we're in a copy of this
  -- file, presumably created by a previous 'dune build'
  -- command. When this happens we just stub out 'definerule', which
  -- means that no build rules are generated in directories below the
  -- current one
  tup.definerule = function() end
end

tup.export("OPAM_SWITCH_PREFIX")
tup.export("CAML_LD_LIBRARY_PATH")
tup.export("OCAML_TOPLEVEL_PATH")

root = tup.getcwd()
miGroup = root..'/<mi>'
miCheatGroup = root..'/<mi-cheat>'
local cwd = tup.getrelativedir(root)
setStdlib = 'MCORE_LIBS=stdlib='..root..'/stdlib '

local builtKind = 'built'
local builtMi = root..'/build/mi '
local addBuiltDep = function(sources)
  sources.extra_inputs = {miGroup}
  return sources
end
local installedKind = 'installed'
local installedMi = 'mi '
local addInstalledDep = function(sources)
  return sources
end

modes = {
  built = {
    kind = 'built',
    mi = root..'/build/mi ',
    addMiDep = function(sources)
      sources.extra_inputs = {miGroup}
      return sources
    end,
  },
  installed = {
    kind = 'installed',
    mi = 'mi ',
    addMiDep = function(x) return x end,
  },
  cheated = {
    kind = 'cheated',
    mi = root..'/build/mi-cheat ',
    addMiDep = function(sources)
      sources.extra_inputs = {miCheatGroup}
      return sources
    end,
  }
}
mode = modes.built

function withMiKind(kind, f)
  local old = mode
  mode = modes[kind]
  local res = f()
  mode = old
  return res
end

-- Set up exception lists
local compileShouldFail = {}
local runShouldFail = {}
local evalShouldFail = {}
local noRun = {}
local noEval = {}

function populateTable(table, items)
  for _, v in ipairs(items) do
    table[v] = true
  end
end

populateTable(compileShouldFail, {
  -- Missing include
  'test/js/web/document.mc',

  -- Old, parse error now
  'test/examples/lang-sem.mc',
  'test/examples/lang-syn.mc',

  -- Old, type-error now
  'stdlib/parser/breakable-helper.mc',
  'test/mlang/nestedpatterns.mc',

  -- Old, uses Dyn
  'test/mlang/mlang.mc',
  'test/mlang/catchall.mc',

  -- Old, fails symbolize in types
  'test/mexpr/nestedpatterns.mc',
  'test/examples/external/ext-list-concat-map.mc',
  'test/examples/external/ext-list-map.mc',

  -- Uses python
  'stdlib/python/python.mc',
  'test/py/python.mc',

  -- Intentional error
  'test/examples/external/multiple-ext-parse-error.mc',
  'test/examples/external/ext-not-applied-parse-error.mc',
  'test/examples/external/ext-not-fully-applied-parse-error.mc',
  -- NOTE(vipa, 2023-01-09): I'm not sure this is actually intentionally failing
  'test/examples/external/ext-removal.mc',

  -- Missing external
  'test/examples/external/ext-parse.mc',

  -- Uses 'Domain', which is fine on 5.0, thus they're commented out here
  -- 'test/microbenchmark/pmap_list.mc',
  -- 'test/microbenchmark/pmap_list_sequential.mc',
  -- 'test/microbenchmark/pmap_rope.mc',
  -- 'test/microbenchmark/pmap_rope_sequential.mc',
  -- 'stdlib/multicore/thread-pool.mc',
  -- 'stdlib/multicore/thread.mc',
  -- 'stdlib/multicore/cond.mc',
  -- 'stdlib/multicore/mutex.mc',
  -- 'stdlib/multicore/channel.mc',
  -- 'stdlib/multicore/pseq.mc',
})

populateTable(runShouldFail, {
  -- Utest failures (this is weird)
  'test/examples/test-prune-utests.mc',

  -- Seems to non-deterministically fail?
  'test/examples/accelerate/mixed.mc',

  -- Out of bounds in microbenchmarks
  'test/microbenchmark/factorial.mc',
  'test/microbenchmark/fold_list.mc',
  'test/microbenchmark/fold_native_list.mc',
  'test/microbenchmark/fold_native_rope.mc',
  'test/microbenchmark/fold_rope.mc',
  'test/microbenchmark/iter_list.mc',
  'test/microbenchmark/iter_rope.mc',
  'test/microbenchmark/mapReverse_list.mc',
  'test/microbenchmark/map_list.mc',
  'test/microbenchmark/map_native_list.mc',
  'test/microbenchmark/map_native_rope.mc',
  'test/microbenchmark/map_rope.mc',
  'test/microbenchmark/rand_sample_gauss.mc',
  'test/microbenchmark/split_list.mc',
  'test/microbenchmark/split_rope.mc',
  'test/microbenchmark/tree.mc',
  'test/microbenchmark/pmap_rope.mc',
  'test/microbenchmark/pmap_rope_sequential.mc',
  'test/microbenchmark/pmap_list_sequential.mc',
  'test/microbenchmark/pmap_list.mc',

  -- Needs a command-line argument when run
  'test/js/benchmarks/factorial.mc',
  'test/js/benchmarks/factorial_fast.mc',
  'test/js/benchmarks/fold_list.mc',
  'test/js/benchmarks/tree.mc',

  -- Intentional error, but maybe wrong error (stack overflow)?
  'test/examples/accelerate/errors/illformed-futhark.mc',

  -- Intentionally fails utests
  'test/examples/utest.mc',

  -- Out of bounds in json benchmark
  'test/examples/json/perftest-mc.mc',
})

populateTable(noRun, {
  -- Doesn't terminate, maybe just slow?
  'test/examples/async/tick.mc',
})

populateTable(evalShouldFail, {
  -- Unknown variable in accelerate
  -- NOTE(vipa, 2023-01-09): expected, interpreter doesn't support accelerate
  'test/examples/accelerate/foldl.mc',
  'test/examples/accelerate/cond.mc',
  'test/examples/accelerate/external.mc',
  'test/examples/accelerate/map.mc',
  'test/examples/accelerate/indirect-map.mc',
  'test/examples/accelerate/futhark-ext.mc',
  'test/examples/accelerate/first.mc',
  'test/examples/accelerate/fold-tensors.mc',
  'test/examples/accelerate/fold-capture.mc',
  'test/examples/accelerate/mixed.mc',
  'test/examples/accelerate/mutual-reclet.mc',
  'test/examples/accelerate/rec-tensor.mc',
  'test/examples/accelerate/matmul.mc',
  'test/examples/accelerate/reclet.mc',
  'test/examples/accelerate/print-float.mc',
  'test/examples/accelerate/sequences.mc',
  'test/examples/accelerate/tensor-aliasing.mc',
  'test/examples/accelerate/seq-tensor.mc',
  'test/examples/accelerate/records.mc',
  'test/examples/accelerate/tensor-add.mc',
  'test/examples/accelerate/errors/function-arg.mc',
  'test/examples/accelerate/wrap-records.mc',
  'test/examples/accelerate/tensor-loop.mc',
  'test/examples/accelerate/zip.mc',
  'test/examples/accelerate/errors/illformed-cuda.mc',
  'test/examples/accelerate/errors/irregular-seq.mc',
  'test/examples/accelerate/errors/indirect-nesting.mc',
  'test/examples/accelerate/errors/reclet-nested-accelerate.mc',
  'test/examples/accelerate/errors/illformed-futhark.mc',
  'test/examples/accelerate/errors/let-nested-accelerate.mc',
  'test/examples/accelerate/errors/seq-nested-accelerate.mc',

  -- Unknown variable
  -- NOTE(vipa, 2023-01-09): expected, missing asyncPrint
  'test/examples/async/tick.mc',

  -- Unknown variable in tuning
  -- NOTE(vipa, 2023-01-09): expected, interpreter doesn't support holes
  'test/examples/tuning/tune-context.mc',
  'test/examples/tuning/tune-sleep.mc',

  -- Uses multicore
  'test/microbenchmark/pmap_rope.mc',
  'test/microbenchmark/pmap_rope_sequential.mc',
  'test/microbenchmark/pmap_list_sequential.mc',
  'test/microbenchmark/pmap_list.mc',
})

populateTable(noEval, {
  -- Seems annoyingly slow, but should work
  'stdlib/tuning/tune.mc',
})

-- Functions that work on individual commands, things that are passed to sh

function expectFail(cmd, msg)
  local cond = 'if '..cmd..' 1>/dev/null 2>&1'
  local success = '; then echo "'..msg..'"; return 1'
  local failure = '; else return 0'
  local fi = '; fi'
  return cond..success..failure..fi
end

function formatFailOutput(cmd, head, tail)
  local tmp = 'ooof=`mktemp`'
  local cond = '; if '..cmd..' >$ooof 2>&1'
  local rm = 'rm -f $ooof'
  head = head or 6
  tail = (tail or 6) - 1
  local awk = '\'FNR <= '..head..' || FNR >= \'`wc -l < $ooof`\'-'..tail..' {print FNR ":\t" $0; next} !el {print "...elided..."; el=1}\''
  local onSuccess = '; then '..rm..'; return 0'
  local onFailure = '; else ooofrv=$?; awk '..awk..' $ooof; '..rm..'; return $ooofrv'
  local fi = '; fi'
  return tmp..cond..onSuccess..onFailure..fi
end


-- Functions that produce Tup rules, i.e., the actual point of this file

-- Compile a given .mc file to an executable
function miCompile(source, destination, options)
  local inputs = mode.addMiDep{source}
  local transient = options.transient and '^t ' or '^ '
  local test = options.test and ' --test' or ''
  local display = transient..'('..mode.kind..') COMPILE'..test..' %f > %o^ '
  local compile = setStdlib..mode.mi..'compile %f --output %o'..test
  return tup.rule(inputs, display..formatFailOutput(compile, 10, 10), destination)
end

function miCompileExpectFail(source)
  local inputs = mode.addMiDep{source}
  local display = '^ ('..mode.kind..') COMPILE-EXPECT-FAIL --test %f^ '
  local compile = setStdlib..mode.mi..'compile --test %f --output /dev/null'
  local msg = 'Expected compilation to fail, but it succeeded.'
  return tup.rule(inputs, display..expectFail(compile, msg), {})
end

function runExec(executable, expectSuccess)
  local display = '^ ('..mode.kind..') RUN'..(expectSuccess and '' or '-EXPECT-FAIL')..' %f^ '
  local msg = 'Expected running to fail, but it succeeded.'
  local run = setStdlib..'./%f'
  local run = expectSuccess and formatFailOutput(run) or expectFail(run, msg)
  return tup.rule(executable, display..run, {})
end

function miEvalTest(source, expectSuccess)
  local display = '^ ('..mode.kind..') EVAL'..(expectSuccess and '' or '-EXPECT-FAIL')..' --test %f^ '
  local msg = 'Expected evaluating to fail, but it succeeded.'
  local run = setStdlib..mode.mi..'eval --test %f'
  run = expectSuccess and formatFailOutput(run) or expectFail(run, msg)
  local inputs = mode.addMiDep{source}
  return tup.rule(inputs, display..run, {})
end

function getBoolOpt(opt, default)
  local conf = tup.getconfig(opt)
  if conf == "y" then
    return true
  elseif conf == "n" then
    return false
  elseif conf == "" then
    return default
  else
    print("Unknown option for "..opt..", expected 'y' or 'n'.")
    exit(1)
  end
end

USE_INSTALLED = getBoolOpt("USE_INSTALLED_MI", false)
USE_BUILT = getBoolOpt("USE_BUILT_MI", true)
USE_CHEATED = getBoolOpt("USE_CHEATED_MI", false)

function testsFor(source)
  local realSource = cwd..'/'..source
  local f = function()
    if compileShouldFail[realSource] then
      miCompileExpectFail(source)
    else
      local executable = miCompile(source, '%B-test-'..mode.kind..'.exe', {test = true, transient = true})

      if noRun[realSource] then
        return
      end

      runExec(executable, not runShouldFail[realSource])

      if noEval[realSource] then
        return
      end

      miEvalTest(source, not (runShouldFail[realSource] or evalShouldFail[realSource]))
    end
  end
  if USE_BUILT then
    withMiKind('built', f)
  end
  if USE_INSTALLED then
    withMiKind('installed', f)
  end
  if USE_CHEATED then
    withMiKind('cheated', f)
  end
end
