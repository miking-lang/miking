#!/bin/sh
###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
###################################################

# Compile and run a file
compile() {
    echo $1
    build/mi src/main/mi.mc -- compile --test $1
    if [ $? -eq 0 ]
    then
        binary=$(basename "$1" .mc)
        ./$binary
        rm $binary
        echo ""
    fi
}

files=""
files="${files} test/mexpr/letlamif.mc"
# files="${files} test/mexpr/fix.mc"
files="${files} test/mexpr/ident-test.mc"
files="${files} test/mexpr/map.mc"
# files="${files} test/mexpr/tensor.mc"
files="${files} test/mexpr/match.mc"
files="${files} test/mexpr/reclets.mc"
files="${files} test/mexpr/comments.mc"
files="${files} test/mexpr/seq-test.mc"
files="${files} test/mexpr/bool-test.mc"
files="${files} test/mexpr/tuples.mc"
# files="${files} test/mexpr/references.mc"
files="${files} test/mexpr/string-test.mc"
files="${files} test/mexpr/time.mc"
# files="${files} test/mexpr/effects.mc"
files="${files} test/mexpr/symbs.mc"
# files="${files} test/mexpr/random-test.mc"
# files="${files} test/mexpr/types.mc"
files="${files} test/mexpr/float-test.mc"
# files="${files} test/mexpr/nestedpatterns.mc"
files="${files} test/mexpr/int-test.mc"
files="${files} test/mexpr/records.mc"
# files="${files} test/mexpr/stringops.mc"
# files="${files} test/mlang/catchall.mc"
files="${files} test/mlang/subfolder/inclib.mc"
files="${files} test/mlang/utest.mc"
# files="${files} test/mlang/include.mc"
# files="${files} test/mlang/strformat.mc"
files="${files} test/mlang/deplib.mc"
# files="${files} test/mlang/sharedcons.mc"
# files="${files} test/mlang/mlang.mc"
# files="${files} test/mlang/simple.mc"
files="${files} test/mlang/lib.mc"
files="${files} test/mlang/dep.mc"
files="${files} test/mlang/also_includes_lib.mc"
# files="${files} test/mlang/top.mc"
# files="${files} test/mlang/nestedpatterns.mc"
# files="${files} stdlib/mexpr/boot-parser.mc"
# files="${files} stdlib/mexpr/type-lift.mc"
# files="${files} stdlib/mexpr/ast.mc"
# files="${files} stdlib/mexpr/pprint.mc"
# files="${files} stdlib/mexpr/parser.mc"
# files="${files} stdlib/mexpr/cps.mc"
# files="${files} stdlib/mexpr/decision-points.mc"
files="${files} stdlib/mexpr/lamlift.mc"
# files="${files} stdlib/mexpr/utesttrans.mc"
# files="${files} stdlib/mexpr/eval.mc"
# files="${files} stdlib/mexpr/symbolize.mc"
# files="${files} stdlib/mexpr/builtin.mc"
# files="${files} stdlib/mexpr/info.mc"
# files="${files} stdlib/mexpr/anf.mc"
# files="${files} stdlib/mexpr/type-annot.mc"
# files="${files} stdlib/mexpr/mexpr.mc"
# files="${files} stdlib/mexpr/infix.mc"
# files="${files} stdlib/mexpr/ast-builder.mc"
# files="${files} stdlib/mexpr/eq.mc"
# files="${files} stdlib/mexpr/ast-smap-sfold-tests.mc"
# files="${files} stdlib/c/ast.mc"
# files="${files} stdlib/c/pprint.mc"
# files="${files} stdlib/ad/dualnum-arith.mc"
# files="${files} stdlib/ad/ad.mc"
# files="${files} stdlib/ad/dualnum-ext.mc"
# files="${files} stdlib/ad/dualnum-helpers.mc"
# files="${files} stdlib/ad/dualnum-bool.mc"
# files="${files} stdlib/ad/dualnum.mc"
# files="${files} stdlib/ad/dualnum-symb.mc"
# files="${files} stdlib/ad/dualnum-tree.mc"
# files="${files} stdlib/ext/math.mc"
# files="${files} stdlib/parser/lexer.mc"
# files="${files} stdlib/parser/generator.mc"
# files="${files} stdlib/parser/breakable.mc"
# files="${files} stdlib/parser/semantic.mc"
# files="${files} stdlib/parser/ll1.mc"
# files="${files} stdlib/parser/gen-ast.mc"
# files="${files} stdlib/ref.mc"
# files="${files} stdlib/prelude.mc"
files="${files} stdlib/common.mc"
# files="${files} stdlib/dfa.mc"
# files="${files} stdlib/map.mc"
# files="${files} stdlib/symtable.mc"
# files="${files} stdlib/tensor.mc"
files="${files} stdlib/assoc.mc"
# files="${files} stdlib/regex.mc"
# files="${files} stdlib/json.mc"
# files="${files} stdlib/eq-paths.mc"
# files="${files} stdlib/hashmap.mc"
files="${files} stdlib/seq.mc"
# files="${files} stdlib/nfa.mc"
# files="${files} stdlib/digraph.mc"
files="${files} stdlib/string.mc"
files="${files} stdlib/math.mc"
# files="${files} stdlib/set.mc"
# files="${files} stdlib/maxmatch.mc"
# files="${files} stdlib/name.mc"
files="${files} stdlib/assoc-seq.mc"
files="${files} stdlib/option.mc"
# files="${files} stdlib/local-search.mc"
# files="${files} stdlib/parser-combinators.mc"
# files="${files} stdlib/matrix.mc"
files="${files} stdlib/either.mc"
# files="${files} stdlib/vec.mc"
files="${files} stdlib/bool.mc"
# files="${files} stdlib/stringid.mc"
# files="${files} stdlib/graph.mc"
files="${files} stdlib/char.mc"
# files="${files} test/multicore/multicore.mc"
# files="${files} stdlib/multicore/pprint.mc"
# files="${files} stdlib/multicore/mexprpar.mc"
# files="${files} stdlib/multicore/eval.mc"
# files="${files} stdlib/multicore/atomic.mc"
# files="${files} stdlib/multicore/ast.mc"
# files="${files} test/py/python.mc"
# files="${files} stdlib/ocaml/symbolize.mc"
# files="${files} stdlib/ocaml/process-helpers.mc"
# files="${files} stdlib/ocaml/pprint.mc"
# files="${files} stdlib/ocaml/generate.mc"
# files="${files} stdlib/ocaml/compile.mc"
# files="${files} stdlib/ocaml/ast.mc"
# files="${files} stdlib/python/python.mc"
# files="${files} test/sundials/sundials.mc"
# files="${files} stdlib/sundials/sundials.mc"
# files="${files} src/main/mi.mc"
# files="${files} src/main/compile.mc"
# files="${files} src/main/run.mc"

export MCORE_STDLIB='stdlib'
for f in $files; do
    compile "$f"
done
