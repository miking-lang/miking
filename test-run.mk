
run_files =
run_files += test/mexpr/letlamif.mc
run_files += test/mexpr/fix.mc
run_files += test/mexpr/ident-test.mc
# run_files += test/mexpr/map.mc
run_files += test/mexpr/tensor.mc
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
# run_files += stdlib/mexpr/cmp.mc
# run_files += stdlib/mexpr/ast.mc
# run_files += stdlib/mexpr/pprint.mc
# run_files += stdlib/mexpr/parser.mc
# run_files += stdlib/mexpr/cps.mc
# run_files += stdlib/mexpr/tuning/decision-points.mc
# run_files += stdlib/mexpr/tuning/tune.mc
# run_files += stdlib/mexpr/tuning/tune-options.mc
# run_files += stdlib/mexpr/tuning/eq-paths.mc
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
run_files += stdlib/ad/dualnum-helpers.mc
run_files += stdlib/ad/dualnum-lift.mc
run_files += stdlib/ad/dualnum.mc
run_files += stdlib/ad/dualnum-tree.mc
# run_files += stdlib/ext/ad/dualnum-ext.mc
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
# run_files += src/main/mi.mc
# run_files += src/main/compile.mc
# run_files += src/main/run.mc
run_files += stdlib/futhark/ast.mc
#run_files += stdlib/futhark/ast-builder.mc
#run_files += stdlib/futhark/generate.mc
#run_files += stdlib/futhark/pprint.mc

all: ${run_files}

${run_files}::
	-@./make run-test $@
