# All relevant source files to include in the tests (plus Java tests)
src_files_all_tmp =\
	$(wildcard stdlib/*.mc)\
	$(wildcard stdlib/**/*.mc)\
	$(wildcard test/mexpr/*.mc)\
	$(wildcard test/mlang/*.mc)\
	$(wildcard test/py/*.mc)

# These are special, special cases since the python externals are implemented
# differently from other externals and can therefore not be compiled.
python_files += stdlib/python/python.mc
python_files += $(wildcard test/py/*.mc)

# These test cases should eventually include all mcore files.
# However, since the pipeline is still slow this would add an unacceptable
# amount of runtime to the tests. Furthermore, the current version still
# has some issues when compiling certain files.
mlang_pipeline_files = $(wildcard stdlib/bool.mc)
mlang_pipeline_files += stdlib/option.mc
mlang_pipeline_files += stdlib/char.mc
mlang_pipeline_files += stdlib/seq.mc
mlang_pipeline_files += stdlib/map.mc
mlang_pipeline_files += stdlib/mexpr/symbolize.mc

# Exclude the tests in the JVM directory, as they depend on Java being
# installed.
# NOTE(larshum, 2023-11-14): Also temporarily exclude the Python boot tests
# since the workflow on MacOS fails because of them.
jvm_files = $(wildcard stdlib/jvm/*.mc)
src_files_all =\
	$(filter-out $(jvm_files) $(python_files), $(src_files_all_tmp))

# These programs has special external dependencies which might be tedious to
# install or are mutually exclusive with other dependencies.
sundials_files = $(wildcard stdlib/sundials/*.mc)
ipopt_files = $(wildcard stdlib/ipopt/*.mc)
accelerate_files = $(wildcard test/accelerate/*.mc)

special_dependencies_files +=\
	$(sundials_files)\
	$(ipopt_files)\
	$(accelerate_files)

# Test programs for the JavaScript backend. These should be compiled with mi
# and runned with node.js, the result being compared to the original program
# being runned with the Miking compiler. All Miking test programs should have
# the same output as the compiled JavaScript programs for all files.
js_files += $(wildcard test/js/*.mc)
# js_web_files += $(wildcard test/js/web/*.mc) # Disabled until web FFI is implemented


# Programs that we currently cannot typecheck. These are programs written
# before the typechecker was implemented. It is forbidden to add to this list of
# programs but removing from it is very welcome.
typecheck_files_exclude += stdlib/parser/breakable-helper.mc
typecheck_files_exclude += test/mexpr/nestedpatterns.mc
typecheck_files_exclude += test/mlang/nestedpatterns.mc
typecheck_files_exclude += test/mlang/mlang.mc
typecheck_files_exclude += test/mlang/catchall.mc

# Programs that we currently cannot typecheck with constructor type
# checking enabled. These are programs written before the typechecker
# was extended with exhaustiveness checks. It is forbidden to add to
# this list of programs but removing from it is very welcome.
constrtype_files_exclude =\
	test/mexpr/pprint-eval.mc\
	test/mlang/subsumption.mc\
	stdlib/effect.mc\
	$(wildcard stdlib/c/*.mc)\
	$(wildcard stdlib/cp/*.mc)\
	$(wildcard stdlib/cuda/*.mc)\
	$(wildcard stdlib/ext/*.mc)\
	$(wildcard stdlib/futhark/*.mc)\
	$(wildcard stdlib/ipopt/*.mc)\
	$(wildcard stdlib/javascript/*.mc)\
	$(wildcard stdlib/jvm/*.mc)\
	$(wildcard stdlib/mexpr/*.mc)\
	$(wildcard stdlib/mlang/*.mc)\
	$(wildcard stdlib/multicore/*.mc)\
	$(wildcard stdlib/ocaml/*.mc)\
	$(wildcard stdlib/parser/*.mc)\
	$(wildcard stdlib/peval/*.mc)\
	$(wildcard stdlib/pmexpr/*.mc)\
	$(wildcard stdlib/sundials/*.mc)\
	$(wildcard stdlib/tuning/*.mc)

# Programs that we currently cannot compile/test. These are programs written
# before the compiler was implemented. It is forbidden to add to this list of
# programs but removing from it is very welcome.
compile_files_exclude += stdlib/parser-combinators.mc
compile_files_exclude += stdlib/regex.mc
compile_files_exclude += test/mexpr/nestedpatterns.mc
compile_files_exclude += test/mlang/also_includes_lib.mc
compile_files_exclude += test/mlang/mlang.mc
compile_files_exclude += test/mlang/nestedpatterns.mc
compile_files_exclude += test/mlang/catchall.mc


# Programs that we currently cannot interpret/test. These are programs written
# before the compiler was implemented. It is forbidden to add to this list of
# programs but removing from it is very welcome.
run_files_exclude += stdlib/regex.mc
run_files_exclude += stdlib/parser-combinators.mc
run_files_exclude += test/mlang/catchall.mc
run_files_exclude += test/mlang/mlang.mc

# Programs that we currently cannot interpret/test since externals cannot be tested by interpreter currently.
external_files_exclude += stdlib/ext/file-ext.mc

# Programs that we should be able to compile/test if we prune utests.
compile_files_prune =\
	$(filter-out $(python_files) $(typecheck_files_exclude) $(compile_files_exclude), $(src_files_all))

# Programs that we should be able to compile/test, even without utest pruning,
# if all, except the special, external dependencies are met.
compile_files =\
	$(filter-out $(special_dependencies_files),\
		$(compile_files_prune))

# Programs that we should be able to interpret/test with the interpreter.
run_files =\
	$(filter-out $(python_files) $(run_files_exclude) $(typecheck_files_exclude) $(external_files_exclude),\
		$(src_files_all))


# Programs that we should be able to interpret/test with boot.
boot_files = $(filter-out $(python_files), $(src_files_all))
