# All relevant source files to include in the tests (plus Java tests)
src_files_all_tmp =\
	$(wildcard stdlib/*.mc)\
	$(wildcard stdlib/**/*.mc)\
	$(wildcard test/mexpr/*.mc)\
	$(wildcard test/mlang/*.mc)\
	$(wildcard test/py/*.mc)

# Exclude the tests in the JVM directory, as they depend on Java being
# installed.
jvm_files = $(wildcard stdlib/jvm/*.mc)
src_files_all =\
	$(filter-out $(jvm_files), $(src_files_all_tmp))

# These programs has special external dependencies which might be tedious to
# install or are mutually exclusive with other dependencies.
sundials_files = $(wildcard stdlib/sundials/*.mc)
ipopt_files = $(wildcard stdlib/ipopt/*.mc)
accelerate_files = $(wildcard test/examples/accelerate/*.mc)
cuda_files = $(wildcard test/examples/accelerate/cuda/*.mc)
futhark_files = $(wildcard test/examples/accelerate/futhark/*.mc)

special_dependencies_files +=\
	$(sundials_files)\
	$(ipopt_files)\
	$(accelerate_files)


# These are special, special cases since the python externals are implemented
# differently from other externals and can therefore not be compiled.
python_files += stdlib/python/python.mc
python_files += $(wildcard test/py/*.mc)


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

# Programs that we should be able to compile/test if we prune utests.
compile_files_prune =\
	$(filter-out $(python_files) $(compile_files_exclude), $(src_files_all))

# Programs that we should be able to compile/test, even without utest pruning,
# if all, except the special, external dependencies are met.
compile_files =\
	$(filter-out $(special_dependencies_files) $(typecheck_files_exclude),\
		$(compile_files_prune))


# Programs the we should be able to interpret/test with the interpreter.
run_files =\
	$(filter-out $(python_files) $(run_files_exclude) $(typecheck_files_exclude),\
		$(src_files_all))


# Programs that we should be able to interpret/test with boot.
boot_files = $(filter-out $(python_files), $(src_files_all))
