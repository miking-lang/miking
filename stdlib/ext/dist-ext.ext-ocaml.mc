

include "map.mc"
include "ocaml/ast.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalBinomialLogPmf", [
      { expr = "Owl_stats.binomial_logpdf",
        ty = tyarrows_ [tyint_, otylabel_ "p" tyfloat_, otylabel_ "n" tyint_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalBinomialSample", [
      { expr = "Owl_stats.binomial_rvs",
        ty = tyarrows_ [otylabel_ "p" tyfloat_, otylabel_ "n" tyint_, tyint_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalBetaLogPdf", [
      { expr = "Owl_stats.beta_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "a" tyfloat_, otylabel_ "b" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalBetaSample", [
      { expr = "Owl_stats.beta_rvs",
        ty = tyarrows_ [otylabel_ "a" tyfloat_, otylabel_ "b" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalGaussianLogPdf", [
      { expr = "Owl_stats.gaussian_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "mu" tyfloat_, otylabel_ "sigma" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalGaussianSample", [
      { expr = "Owl_stats.gaussian_rvs",
        ty = tyarrows_ [otylabel_ "mu" tyfloat_, otylabel_ "sigma" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("uniformSample", [
      { expr = "Owl_stats.std_uniform_rvs",
        ty = tyarrows_ [tyunit_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalRandomSample", [
      { expr = "Owl_stats.uniform_int_rvs",
        ty = tyarrows_ [tyint_, tyint_, tyint_],
        libraries = ["owl"],
        cLibraries = []
      }
    ])
  ]
