
compile_files =
compile_files += test/mexpr/letlamif.mc
compile_files += test/mexpr/fix.mc
compile_files += test/mexpr/ident-test.mc
compile_files += test/mexpr/map.mc
compile_files += test/mexpr/tensor.mc
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
compile_files += stdlib/mexpr/cmp.mc
compile_files += stdlib/mexpr/ast.mc
compile_files += stdlib/mexpr/pprint.mc
compile_files += stdlib/mexpr/parser.mc
compile_files += stdlib/mexpr/cps.mc
compile_files += stdlib/mexpr/tuning/decision-points.mc
compile_files += stdlib/mexpr/tuning/tune.mc
compile_files += stdlib/mexpr/tuning/tune-options.mc
compile_files += stdlib/mexpr/tuning/eq-paths.mc
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
compile_files += stdlib/c/ast.mc
compile_files += stdlib/c/pprint.mc
#compile_files += stdlib/c/compile.mc
compile_files += stdlib/ad/dualnum-helpers.mc
compile_files += stdlib/ad/dualnum-lift.mc
compile_files += stdlib/ad/dualnum.mc
compile_files += stdlib/ad/dualnum-tree.mc
compile_files += stdlib/ext/ad/dualnum-ext.mc
compile_files += stdlib/parser/lexer.mc
compile_files += stdlib/parser/generator.mc
compile_files += stdlib/parser/breakable.mc
compile_files += stdlib/parser/semantic.mc
compile_files += stdlib/parser/ll1.mc
compile_files += stdlib/parser/gen-ast.mc
#compile_files += stdlib/ref.mc
compile_files += stdlib/common.mc
#compile_files += stdlib/dfa.mc
compile_files += stdlib/map.mc
#compile_files += stdlib/symtable.mc
#compile_files += stdlib/tensor.mc
compile_files += stdlib/assoc.mc
#compile_files += stdlib/regex.mc
#compile_files += stdlib/json.mc
compile_files += stdlib/hashmap.mc
compile_files += stdlib/seq.mc
#compile_files += stdlib/nfa.mc
compile_files += stdlib/digraph.mc
compile_files += stdlib/string.mc
compile_files += stdlib/math.mc
#compile_files += stdlib/eqset.mc
compile_files += stdlib/maxmatch.mc
compile_files += stdlib/maxmatch-tensor.mc
compile_files += stdlib/name.mc
compile_files += stdlib/assoc-seq.mc
compile_files += stdlib/option.mc
#compile_files += stdlib/local-search.mc
#compile_files += stdlib/parser-combinators.mc
compile_files += stdlib/either.mc
compile_files += stdlib/bool.mc
#compile_files += stdlib/stringid.mc
#compile_files += stdlib/graph.mc
compile_files += stdlib/char.mc
compile_files += stdlib/set.mc
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
# compile_files += stdlib/python/python.mc
compile_files += src/main/mi.mc
compile_files += src/main/compile.mc
compile_files += src/main/run.mc
compile_files += stdlib/ext/math-ext.mc
compile_files += stdlib/ext/ext-test.mc

all: ${compile_files}

${compile_files}::
	-@./make compile-test $@ "build/mi compile --test --disable-optimizations"
