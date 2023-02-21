-- Bootstrapping, build boot.
do

  -- NOTE(vipa, 2023-01-30): Dune copies the *entire* repo into its
  -- build directory (_build by default), which means two things:
  -- 1. Tup thinks the command depends on *every* file in the repo.
  -- 2. Some of the files copied (Tupfile.lua, Tuprules.lua, etc.)
  --    will trigger more builds in these directories next time we
  --    run tup.

  -- We work around point 2 by using a temporary bulid directory
  -- somewhere else, that's `mktemp -d` below. We must make sure to
  -- remove this directory after, whether the build succeeded or not.

  local display = "^ dune build^"
  local mkdir = 'tmp=`mktemp -d`'
  local dune = '&& if dune build --build-dir $tmp'
  local cp = '; then cp $tmp/install/default/bin/boot build/boot'
  local rm = '; rm -rf $tmp; else rm -rf $tmp; fi'

  -- As for point 1, we can circumvent Tups dependency detection by
  -- telling it to ignore some files. Unfortunately, this must be as
  -- one (or more) regexes that match paths to ignore, and what we
  -- *want* to do is list things to track.

  -- We expect these files to potentially be relevant:
  local keep = {
    -- Negative look-behind pattern; tup uses PCRE
    'src/boot/.+(?<!/.gitignore)$',
    'boot.opam$',
    'dune-project$',
    -- The output is also relevant
    'build/boot$',
  }
  -- We can now 'or' these regexes together and put them in a negative
  -- look-ahead pattern, to match a path that matches none of the
  -- paths above.
  local ignore = '(?!'..table.concat(keep, '|')..')'

  -- Unfortunately, a regex like '(?!foo)' *does* match 'foo', just
  -- not at the beginning. Ideally we could just require that the
  -- match is at the beginning of the path (with '^'), but Tup matches
  -- against the complete, absolute path, for some reason (I assume to
  -- have the same behavior when full-deps tracking is turned on). The
  -- only path we have access to is tup.getdirectory(), which is just
  -- the name of the current directory. Presently this is ok, there is
  -- no subdirectory anywhere in the repo named 'miking' (which is the
  -- default name of the repo itself), thus we can just prepend
  -- '/miking/' to the regex and get something that does what we want
  -- it to.
  ignore = '/'..tup.getdirectory()..'/'..ignore

  -- Finally, we put the command together, and put a '^' at the
  -- beginning of the regex, since that signals to Tup that this is a
  -- regex for paths to ignore.
  tup.rule({}, display..mkdir..dune..cp..rm, {'build/boot', extra_outputs = {'^'..ignore}})
end

if USE_BUILT then
  -- Bootstrapping, interpret mi-lite on itself
  do
    local compile = 'build/boot eval %f -- 0 %f %o'
    local display = '^o '..compile..'^ '
    local inputs = {'src/main/mi-lite.mc', extra_inputs = {'build/boot'}}
    tup.rule(inputs, display..setStdlib..compile, 'build/mi-lite')
  end

  -- Bootstrapping, use compiled mi-lite to build mi
  do
    local compile = 'build/mi-lite 1 %f %o'
    local display = '^o '..compile..'^ '
    local inputs = {'src/main/mi.mc', extra_inputs = {'build/mi-lite'}}
    tup.rule(inputs, display..setStdlib..compile, 'build/mi1')
  end

  -- Bootstrapping, use compiled mi to compile itself
  do
    local compile = 'build/mi1 compile %f --output %o'
    local display = '^o '..compile..'^ '
    local inputs = {'src/main/mi.mc', extra_inputs = {'build/mi1'}}
    tup.rule(inputs, display..setStdlib..compile, {'build/mi', miGroup})
  end
end

if USE_CHEATED then
  -- Cheatstrapping, use installed mi to compile a new mi
  do
    local compile = 'mi compile %f --output %o'
    local display = '^o '..compile..'^ '
    local inputs = {'src/main/mi.mc'}
    tup.rule(inputs, display..setStdlib..compile, {'build/mi-cheat', miCheatGroup})
  end
end
