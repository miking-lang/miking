

include "map.mc"
include "ocaml/ast.mc"
include "string.mc"
include "mexpr/ast-builder.mc"

let distExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
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
