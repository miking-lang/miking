

include "map.mc"
include "ocaml/ast.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("myExternalExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ , libraries = [] }
    ]),
    ("externalBinomialLogPmf", [
      { ident = "Owl_stats.binomial_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "p" tyfloat_, otylabel_ "n" tyint_, tyfloat_],
        libraries = ["owl"]
      }
    ])

-- external externalBinomialLogPmf : Float -> Float -> Int -> Float

-- let bernoulli_pmf x p = Owl_stats.binomial_logpdf x ~p:p ~n:1

  ]
