#!/bin/bash
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

files=(
# "test/mexpr/letlamif.mc"
"test/mexpr/fix.mc"
# "test/mexpr/ident-test.mc"
# "test/mexpr/map.mc"
# "test/mexpr/tensor.mc"
# "test/mexpr/match.mc"
# "test/mexpr/reclets.mc"
# "test/mexpr/comments.mc"
# "test/mexpr/seq-test.mc"
# "test/mexpr/bool-test.mc"
# "test/mexpr/tuples.mc"
# "test/mexpr/references.mc"
# "test/mexpr/string-test.mc"
# "test/mexpr/time.mc"
# "test/mexpr/effects.mc"
# "test/mexpr/symbs.mc"
# "test/mexpr/random-test.mc"
# "test/mexpr/types.mc"
# "test/mexpr/float-test.mc"
# "test/mexpr/nestedpatterns.mc"
# "test/mexpr/int-test.mc"
# "test/mexpr/records.mc"
# "test/mexpr/stringops.mc"
# "test/mlang/catchall.mc"
# "test/mlang/subfolder/inclib.mc"
# "test/mlang/utest.mc"
# "test/mlang/include.mc"
# "test/mlang/strformat.mc"
# "test/mlang/deplib.mc"
# "test/mlang/sharedcons.mc"
# "test/mlang/mlang.mc"
# "test/mlang/simple.mc"
# "test/mlang/lib.mc"
# "test/mlang/dep.mc"
# "test/mlang/also_includes_lib.mc"
# "test/mlang/top.mc"
# "test/mlang/nestedpatterns.mc"
# "stdlib/mexpr/boot-parser.mc"
# "stdlib/mexpr/type-lift.mc"
# "stdlib/mexpr/ast.mc"
# "stdlib/mexpr/pprint.mc"
# "stdlib/mexpr/parser.mc"
# "stdlib/mexpr/cps.mc"
# "stdlib/mexpr/decision-points.mc"
# "stdlib/mexpr/lamlift.mc"
# "stdlib/mexpr/utesttrans.mc"
# "stdlib/mexpr/eval.mc"
# "stdlib/mexpr/symbolize.mc"
# "stdlib/mexpr/builtin.mc"
# "stdlib/mexpr/info.mc"
# "stdlib/mexpr/anf.mc"
# "stdlib/mexpr/type-annot.mc"
# "stdlib/mexpr/mexpr.mc"
# "stdlib/mexpr/infix.mc"
# "stdlib/mexpr/ast-builder.mc"
# "stdlib/mexpr/eq.mc"
# "stdlib/mexpr/ast-smap-sfold-tests.mc"
# "stdlib/c/ast.mc"
# "stdlib/c/pprint.mc"
# "stdlib/ad/dualnum-arith.mc"
# "stdlib/ad/ad.mc"
# "stdlib/ad/dualnum-ext.mc"
# "stdlib/ad/dualnum-helpers.mc"
# "stdlib/ad/dualnum-bool.mc"
# "stdlib/ad/dualnum.mc"
# "stdlib/ad/dualnum-symb.mc"
# "stdlib/ad/dualnum-tree.mc"
# "stdlib/ext/math.mc"
# "stdlib/parser/lexer.mc"
# "stdlib/parser/generator.mc"
# "stdlib/parser/breakable.mc"
# "stdlib/parser/semantic.mc"
# "stdlib/parser/ll1.mc"
# "stdlib/parser/gen-ast.mc"
# "stdlib/ref.mc"
# "stdlib/prelude.mc"
# "stdlib/dfa.mc"
# "stdlib/map.mc"
# "stdlib/symtable.mc"
# "stdlib/tensor.mc"
# "stdlib/assoc.mc"
# "stdlib/regex.mc"
# "stdlib/json.mc"
# "stdlib/eq-paths.mc"
# "stdlib/hashmap.mc"
# "stdlib/seq.mc"
# "stdlib/nfa.mc"
# "stdlib/digraph.mc"
# "stdlib/string.mc"
# "stdlib/math.mc"
# "stdlib/set.mc"
# "stdlib/maxmatch.mc"
# "stdlib/name.mc"
# "stdlib/assoc-seq.mc"
# "stdlib/option.mc"
# "stdlib/local-search.mc"
# "stdlib/parser-combinators.mc"
# "stdlib/matrix.mc"
# "stdlib/either.mc"
# "stdlib/vec.mc"
  # "stdlib/bool.mc"
# "stdlib/stringid.mc"
# "stdlib/graph.mc"
# "stdlib/char.mc"
# "test/multicore/multicore.mc"
# "stdlib/multicore/pprint.mc"
# "stdlib/multicore/mexprpar.mc"
# "stdlib/multicore/eval.mc"
# "stdlib/multicore/atomic.mc"
# "stdlib/multicore/ast.mc"
# "test/py/python.mc"
# "stdlib/ocaml/symbolize.mc"
# "stdlib/ocaml/process-helpers.mc"
# "stdlib/ocaml/pprint.mc"
# "stdlib/ocaml/generate.mc"
# "stdlib/ocaml/compile.mc"
# "stdlib/ocaml/ast.mc"
# "stdlib/python/python.mc"
# "test/sundials/sundials.mc"
# "stdlib/sundials/sundials.mc"
# "src/main/mi.mc"
# "src/main/compile.mc"
# "src/main/run.mc"
)

for i in "${files[@]}"; do
    compile "$i"
done
