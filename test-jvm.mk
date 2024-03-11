include test-files.mk

.PHONY: all $(compile_files)

all: $(compile_files)

# Exclude some files for the JVM backend. 

# Output differences
jvm_test_exclude = stdlib/arg.mc
jvm_test_exclude += stdlib/csv.mc
jvm_test_exclude += test/mexpr/effects.mc
jvm_test_exclude += test/mexpr/float-test.mc
jvm_test_exclude += test/mexpr/seq-test.mc

# Uses unsupported language features in the JVM backend
jvm_test_exclude += stdlib/math.mc
jvm_test_exclude += stdlib/matrix.mc
jvm_test_exclude += stdlib/maxmatch-tensor.mc
jvm_test_exclude += stdlib/result.mc
jvm_test_exclude += stdlib/stats.mc
jvm_test_exclude += stdlib/tensor.mc
jvm_test_exclude += $(wildcard stdlib/ad/*.mc)
jvm_test_exclude += $(wildcard stdlib/cuda/*.mc)
jvm_test_exclude += $(wildcard stdlib/ext/*.mc)
jvm_test_exclude += $(wildcard stdlib/futhark/*.mc)
jvm_test_exclude += $(wildcard stdlib/ipopt/*.mc)
jvm_test_exclude += $(wildcard stdlib/mexpr/*.mc)
jvm_test_exclude += $(wildcard stdlib/multicore/*.mc)
jvm_test_exclude += $(wildcard stdlib/ocaml/*.mc)
jvm_test_exclude += $(wildcard stdlib/peval/*.mc)
jvm_test_exclude += $(wildcard stdlib/pmexpr/*.mc)
jvm_test_exclude += $(wildcard stdlib/sundials/*.mc)
jvm_test_exclude += $(wildcard stdlib/tuning/*.mc)
jvm_test_exclude += test/mexpr/tensor.mc
jvm_test_exclude += test/py/python.mc

# Other bugs
jvm_test_exclude += stdlib/json.mc
jvm_test_exclude += stdlib/c/compile.mc
jvm_test_exclude += stdlib/cp/solve.mc
jvm_test_exclude += stdlib/mexpr/call-graph.mc
jvm_test_exclude += stdlib/parser/breakable-helper.mc
jvm_test_exclude += $(wildcard stdlib/parser/*.mc)

jvm_test_files = $(filter-out $(jvm_test_exclude), $(compile_files))

$(jvm_test_files):
	@ ./make.sh compile-and-run-jvm-test $@ 
