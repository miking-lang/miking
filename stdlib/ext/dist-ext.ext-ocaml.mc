

include "map.mc"
include "ocaml/ast.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalExponentialSample", [
      { expr = "Owl_stats.exponential_rvs",
        ty = tyarrows_ [otylabel_ "lambda" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalGammaLogPdf", [
      { expr = "Owl_stats.gamma_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "shape" tyfloat_, otylabel_ "scale" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalGammaSample", [
      { expr = "Owl_stats.gamma_rvs",
        ty = tyarrows_ [otylabel_ "shape" tyfloat_, otylabel_ "scale" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
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
    ("externalMultinomialLogPmf", [
      { expr = "Owl_stats.multinomial_logpdf ",
        ty = tyarrows_ [otyarray_ tyint_, otylabel_ "p" (otyarray_ tyfloat_), tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalMultinomialSample", [
      { expr = "Owl_stats.multinomial_rvs ",
        ty = tyarrows_ [tyint_, otylabel_ "p" (otyarray_ tyfloat_), otyarray_ tyint_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalCategoricalSample", [
      { expr = "Owl_stats.categorical_rvs ",
        ty = tyarrows_ [otyarray_ tyfloat_, tyint_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalDirichletLogPdf", [
      { expr = "Owl_stats.dirichlet_logpdf ",
        ty = tyarrows_ [otyarray_ tyfloat_, otylabel_ "alpha" (otyarray_ tyfloat_), tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalDirichletSample", [
      { expr = "Owl_stats.dirichlet_rvs ",
        ty = tyarrows_ [otylabel_ "alpha" (otyarray_ tyfloat_), otyarray_ tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalUniformContinuousSample", [
      { expr = "Owl_stats.uniform_rvs",
        ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalUniformDiscreteSample", [
      { expr = "Owl_stats.uniform_int_rvs",
        ty = tyarrows_ [tyint_, tyint_, tyint_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalLomaxSample", [
      { expr = "Owl_stats.lomax_rvs",
        ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalLomaxLogPdf", [
      { expr = "Owl_stats.lomax_logpdf",
        ty = tyarrows_ [tyfloat_, otylabel_ "shape" tyfloat_, otylabel_ "scale" tyfloat_, tyfloat_],
        libraries = ["owl"],
        cLibraries = []
      }
    ]),
    ("externalSetSeed", [
      { expr = "
        fun seed -> (
          Random.init seed;
          Owl_base_stats_prng.init seed;
          Owl_stats_prng.sfmt_seed seed;
          Owl_stats_prng.ziggurat_init ()
        )",
        ty = tyarrows_ [tyint_, otyunit_],
        libraries = ["owl"],
        cLibraries = []
      }
    ])
  ]
