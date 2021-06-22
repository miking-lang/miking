include "ocaml/ast.mc"
include "ext/ext-test-batteries.ext-ocaml.mc" -- For testing
include "ext/ext-test.ext-ocaml.mc"           -- For testing
include "ext/math-ext.ext-ocaml.mc"
include "sundials/sundials.ext-ocaml.mc"
include "multicore/atomic.ext-ocaml.mc"
include "multicore/thread.ext-ocaml.mc"

type ExternalImpl = { ident : String, ty : Type, libraries : [String] }

-- NOTE(oerikss, 2021-04-30) Add your external maps here. This is a temporary
-- solution. In the end we want to provide these definitions outside the
-- compiler (which will require some parsing).
let globalExternalImplsMap : Map String [ExternalImpl] =
  foldl1 mapUnion
    [
      extTestBatteriesMap,      -- For testing purposes
      extTestMap,               -- For testing purposes
      mathExtMap,
      sundialsExtMap,
      atomicExtMap,
      threadExtMap
    ]
