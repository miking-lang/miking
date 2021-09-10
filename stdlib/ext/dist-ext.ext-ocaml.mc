

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
    ]),
    ("externalBinomialSample", [
      { ident = "Owl_stats.binomial_rvs",
        ty = tyarrows_ [otylabel_ "p" tyfloat_, otylabel_ "n" tyint_, tyint_],
        libraries = ["owl"]
      }
    ]),
    ("externalBetaLogPdf", [
      { ident = "Owl_stats.beta_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "a" tyfloat_, otylabel_ "b" tyfloat_, tyfloat_],
        libraries = ["owl"]
      }
    ]),
    ("externalBetaSample", [
      { ident = "Owl_stats.beta_rvs",
        ty = tyarrows_ [otylabel_ "a" tyfloat_, otylabel_ "b" tyfloat_, tyfloat_],
        libraries = ["owl"]
      }
    ])
  ]
