

include "map.mc"
include "ocaml/ast.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalBinomialLogPmf", [
      { ident = "Owl_stats.binomial_logpdf",
        ty = tyarrows_ [tyint_, otylabel_ "p" tyfloat_, otylabel_ "n" tyint_, tyfloat_],
        libraries = ["owl"]
      }
    ])
  ]
