###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  all scripts are done in OCaml instead of being
#  dependent on make. If make is installed on
#  the system, we just run the batch make file.
###################################################

.PHONY : all test test-all install lint fix clean old files compile-all

all:
	@./make

test:
	@./make test

test-all:
	@./make test-all

install:
	@./make install

lint:
	@./make lint

fix:
	@./make fix

clean:
	@./make clean

old:
	@./make old

compile_files =
compile_files += test/mexpr/letlamif.mc
compile_files += test/mexpr/fix.mc
compile_files += test/mexpr/ident-test.mc
compile_files += test/mexpr/map.mc
#compile_files += test/mexpr/tensor.mc
compile_files += test/mexpr/match.mc
compile_files += test/mexpr/reclets.mc
compile_files += test/mexpr/comments.mc
compile_files += test/mexpr/seq-test.mc
compile_files += test/mexpr/bool-test.mc
compile_files += test/mexpr/tuples.mc
#compile_files += test/mexpr/references.mc
compile_files += test/mexpr/string-test.mc
compile_files += test/mexpr/time.mc
compile_files += test/mexpr/effects.mc
compile_files += test/mexpr/symbs.mc
compile_files += test/mexpr/random-test.mc
compile_files += test/mexpr/types.mc
compile_files += test/mexpr/float-test.mc
compile_files += test/mexpr/nestedpatterns.mc
compile_files += test/mexpr/int-test.mc
compile_files += test/mexpr/records.mc
compile_files += test/mexpr/stringops.mc
#compile_files += test/mlang/catchall.mc
#compile_files += test/mlang/subsumption.mc
compile_files += test/mlang/subfolder/inclib.mc
compile_files += test/mlang/utest.mc
#compile_files += test/mlang/include.mc
#compile_files += test/mlang/strformat.mc
compile_files += test/mlang/deplib.mc
#compile_files += test/mlang/sharedcons.mc
#compile_files += test/mlang/mlang.mc
#compile_files += test/mlang/simple.mc
compile_files += test/mlang/lib.mc
compile_files += test/mlang/dep.mc
compile_files += test/mlang/also_includes_lib.mc
#compile_files += test/mlang/top.mc
#compile_files += test/mlang/nestedpatterns.mc
compile_files += stdlib/mexpr/boot-parser.mc
compile_files += stdlib/mexpr/type-lift.mc
compile_files += stdlib/mexpr/ast.mc
compile_files += stdlib/mexpr/pprint.mc
compile_files += stdlib/mexpr/parser.mc
compile_files += stdlib/mexpr/cps.mc
compile_files += stdlib/mexpr/decision-points.mc
compile_files += stdlib/mexpr/lamlift.mc
compile_files += stdlib/mexpr/utesttrans.mc
compile_files += stdlib/mexpr/eval.mc
compile_files += stdlib/mexpr/symbolize.mc
compile_files += stdlib/mexpr/builtin.mc
compile_files += stdlib/mexpr/info.mc
compile_files += stdlib/mexpr/anf.mc
compile_files += stdlib/mexpr/type-annot.mc
compile_files += stdlib/mexpr/mexpr.mc
compile_files += stdlib/mexpr/infix.mc
compile_files += stdlib/mexpr/ast-builder.mc
compile_files += stdlib/mexpr/eq.mc
compile_files += stdlib/mexpr/ast-smap-sfold-tests.mc
compile_files += stdlib/mexpr/keyword-maker.mc
compile_files += stdlib/mexpr/const-types.mc
#compile_files += stdlib/c/ast.mc
#compile_files += stdlib/c/pprint.mc
#compile_files += stdlib/c/compile.mc
#compile_files += stdlib/ad/dualnum-arith.mc
#compile_files += stdlib/ad/ad.mc
#compile_files += stdlib/ad/dualnum-ext.mc
#compile_files += stdlib/ad/dualnum-helpers.mc
#compile_files += stdlib/ad/dualnum-bool.mc
#compile_files += stdlib/ad/dualnum.mc
#compile_files += stdlib/ad/dualnum-symb.mc
#compile_files += stdlib/ad/dualnum-tree.mc
#compile_files += stdlib/ext/math.mc
#compile_files += stdlib/parser/lexer.mc
#compile_files += stdlib/parser/generator.mc
#compile_files += stdlib/parser/breakable.mc
#compile_files += stdlib/parser/semantic.mc
#compile_files += stdlib/parser/ll1.mc
#compile_files += stdlib/parser/gen-ast.mc
#compile_files += stdlib/ref.mc
compile_files += stdlib/common.mc
#compile_files += stdlib/dfa.mc
compile_files += stdlib/map.mc
#compile_files += stdlib/symtable.mc
#compile_files += stdlib/tensor.mc
compile_files += stdlib/assoc.mc
#compile_files += stdlib/regex.mc
#compile_files += stdlib/json.mc
compile_files += stdlib/eq-paths.mc
compile_files += stdlib/hashmap.mc
compile_files += stdlib/seq.mc
#compile_files += stdlib/nfa.mc
compile_files += stdlib/digraph.mc
compile_files += stdlib/string.mc
compile_files += stdlib/math.mc
#compile_files += stdlib/eqset.mc
#compile_files += stdlib/maxmatch.mc
compile_files += stdlib/name.mc
compile_files += stdlib/assoc-seq.mc
compile_files += stdlib/option.mc
#compile_files += stdlib/local-search.mc
#compile_files += stdlib/parser-combinators.mc
#compile_files += stdlib/matrix.mc
compile_files += stdlib/either.mc
#compile_files += stdlib/vec.mc
compile_files += stdlib/bool.mc
#compile_files += stdlib/stringid.mc
#compile_files += stdlib/graph.mc
compile_files += stdlib/char.mc
compile_files += stdlib/set.mc
#compile_files += test/multicore/multicore.mc
#compile_files += stdlib/multicore/pprint.mc
#compile_files += stdlib/multicore/mexprpar.mc
#compile_files += stdlib/multicore/eval.mc
#compile_files += stdlib/multicore/atomic.mc
#compile_files += stdlib/multicore/ast.mc
#compile_files += test/py/python.mc
compile_files += stdlib/ocaml/symbolize.mc
compile_files += stdlib/ocaml/sys.mc
compile_files += stdlib/ocaml/pprint.mc
compile_files += stdlib/ocaml/generate.mc
compile_files += stdlib/ocaml/compile.mc
compile_files += stdlib/ocaml/ast.mc
compile_files += stdlib/ocaml/intrinsics-ops.mc
compile_files += stdlib/ocaml/external-includes.mc
compile_files += stdlib/ocaml/external.mc
#compile_files += stdlib/python/python.mc
#compile_files += test/sundials/sundials.mc
#compile_files += stdlib/sundials/sundials.mc
compile_files += src/main/mi.mc
compile_files += src/main/compile.mc
compile_files += src/main/run.mc
compile_files += stdlib/ext/math-ext.mc

run_files =
run_files += test/mexpr/letlamif.mc
run_files += test/mexpr/fix.mc
run_files += test/mexpr/ident-test.mc
# run_files += test/mexpr/map.mc
# run_files += test/mexpr/tensor.mc
# run_files += test/mexpr/match.mc
run_files += test/mexpr/reclets.mc
run_files += test/mexpr/comments.mc
# run_files += test/mexpr/seq-test.mc
run_files += test/mexpr/bool-test.mc
run_files += test/mexpr/tuples.mc
run_files += test/mexpr/references.mc
# run_files += test/mexpr/string-test.mc
run_files += test/mexpr/time.mc
# run_files += test/mexpr/effects.mc
run_files += test/mexpr/symbs.mc
# run_files += test/mexpr/random-test.mc
# run_files += test/mexpr/types.mc
run_files += test/mexpr/float-test.mc
run_files += test/mexpr/nestedpatterns.mc
run_files += test/mexpr/int-test.mc
run_files += test/mexpr/records.mc
# run_files += test/mexpr/stringops.mc
# run_files += test/mlang/catchall.mc
# run_files += test/mlang/subsumption.mc
run_files += test/mlang/subfolder/inclib.mc
run_files += test/mlang/utest.mc
run_files += test/mlang/include.mc
run_files += test/mlang/strformat.mc
run_files += test/mlang/deplib.mc
run_files += test/mlang/sharedcons.mc
# run_files += test/mlang/mlang.mc
run_files += test/mlang/simple.mc
run_files += test/mlang/lib.mc
run_files += test/mlang/dep.mc
run_files += test/mlang/also_includes_lib.mc
# run_files += test/mlang/top.mc
# run_files += test/mlang/nestedpatterns.mc
# run_files += stdlib/mexpr/boot-parser.mc
# run_files += stdlib/mexpr/type-lift.mc
# run_files += stdlib/mexpr/ast.mc
# run_files += stdlib/mexpr/pprint.mc
# run_files += stdlib/mexpr/parser.mc
# run_files += stdlib/mexpr/cps.mc
# run_files += stdlib/mexpr/decision-points.mc
# run_files += stdlib/mexpr/lamlift.mc
# run_files += stdlib/mexpr/utesttrans.mc
# run_files += stdlib/mexpr/eval.mc
# run_files += stdlib/mexpr/symbolize.mc
# run_files += stdlib/mexpr/builtin.mc
# run_files += stdlib/mexpr/info.mc
# run_files += stdlib/mexpr/anf.mc
# run_files += stdlib/mexpr/type-annot.mc
# run_files += stdlib/mexpr/mexpr.mc
# run_files += stdlib/mexpr/infix.mc
# run_files += stdlib/mexpr/ast-builder.mc
# run_files += stdlib/mexpr/eq.mc
# run_files += stdlib/mexpr/ast-smap-sfold-tests.mc
# run_files += stdlib/mexpr/keyword-maker.mc
# run_files += stdlib/mexpr/const-types.mc
# run_files += stdlib/c/ast.mc
# run_files += stdlib/c/pprint.mc
# run_files += stdlib/c/compile.mc
# run_files += stdlib/ad/dualnum-arith.mc
# run_files += stdlib/ad/ad.mc
# run_files += stdlib/ad/dualnum-ext.mc
# run_files += stdlib/ad/dualnum-helpers.mc
# run_files += stdlib/ad/dualnum-bool.mc
# run_files += stdlib/ad/dualnum.mc
# run_files += stdlib/ad/dualnum-symb.mc
# run_files += stdlib/ad/dualnum-tree.mc
# run_files += stdlib/ext/math.mc
# run_files += stdlib/parser/lexer.mc
# run_files += stdlib/parser/generator.mc
# run_files += stdlib/parser/breakable.mc
# run_files += stdlib/parser/semantic.mc
# run_files += stdlib/parser/ll1.mc
# run_files += stdlib/parser/gen-ast.mc
# run_files += stdlib/ref.mc
run_files += stdlib/common.mc
# run_files += stdlib/dfa.mc
# run_files += stdlib/map.mc
# run_files += stdlib/symtable.mc
# run_files += stdlib/tensor.mc
run_files += stdlib/assoc.mc
# run_files += stdlib/regex.mc
# run_files += stdlib/json.mc
# run_files += stdlib/eq-paths.mc
run_files += stdlib/hashmap.mc
run_files += stdlib/seq.mc
# run_files += stdlib/nfa.mc
# run_files += stdlib/digraph.mc
run_files += stdlib/string.mc
# run_files += stdlib/math.mc
# run_files += stdlib/eqset.mc
# run_files += stdlib/maxmatch.mc
# run_files += stdlib/name.mc
run_files += stdlib/assoc-seq.mc
run_files += stdlib/option.mc
# run_files += stdlib/local-search.mc
# run_files += stdlib/parser-combinators.mc
# run_files += stdlib/matrix.mc
run_files += stdlib/either.mc
# run_files += stdlib/vec.mc
run_files += stdlib/bool.mc
# run_files += stdlib/stringid.mc
# run_files += stdlib/graph.mc
run_files += stdlib/char.mc
# run_files += stdlib/set.mc
# run_files += test/multicore/multicore.mc
# run_files += stdlib/multicore/pprint.mc
# run_files += stdlib/multicore/mexprpar.mc
# run_files += stdlib/multicore/eval.mc
# run_files += stdlib/multicore/atomic.mc
# run_files += stdlib/multicore/ast.mc
# run_files += test/py/python.mc
# run_files += stdlib/ocaml/symbolize.mc
# run_files += stdlib/ocaml/sys.mc
# run_files += stdlib/ocaml/pprint.mc
# run_files += stdlib/ocaml/generate.mc
# run_files += stdlib/ocaml/compile.mc
# run_files += stdlib/ocaml/ast.mc
# run_files += stdlib/ocaml/intrinsics-ops.mc
# run_files += stdlib/ocaml/external-includes.mc
# run_files += stdlib/ocaml/external.mc
# run_files += stdlib/python/python.mc
# run_files += test/sundials/sundials.mc
# run_files += stdlib/sundials/sundials.mc
# run_files += src/main/mi.mc
# run_files += src/main/compile.mc
# run_files += src/main/run.mc

test-bootstrap: ${compile_files} ${run_files}

testt: stdlib/common.mc stdlib/common.mc

${compile_files}::
	@./make compile-test $@ "build/boot eval src/main/mi.mc -- compile --test --disable-optimizations"

${compile_files}::
	@./make compile-test $@ "build/mi compile --test --disable-optimizations"

${run_files}::
	@./make run-test $@



