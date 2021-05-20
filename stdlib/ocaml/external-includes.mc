include "ocaml/ast.mc"
include "ext/ext-test-batteries.ext-ocaml.mc" -- For testing
include "ext/ext-test.ext-ocaml.mc"           -- For testing
include "ext/math-ext.ext-ocaml.mc"
include "ext/solver.ext-ocaml.mc"

type ExternalImplDef = {ident : String, ty : Type, libraries : [String]}

type ExternalImpl =
  {name : Name, extIdent : String, extTy : Type, libraries : [String]}

type ExternalImplsMap = Map String [ExternalImpl]

-- NOTE(oerikss, 2021-04-30) Add your external maps here. This is a temporary
-- solution. In the end we want to provide these definitions outside the
-- compiler (which will require some parsing).
let globalExternalImplsMap : ExternalImplsMap =
  mapMapWithKey
  (lam id : String.
    map (lam imp : ExternalImplDef.
          {name = nameSym id,
           extIdent = imp.ident,
           extTy = imp.ty,
           libraries = imp.libraries}))
  (foldl1 mapUnion
    [
      extTestBatteriesMap,      -- For testing purposes
      extTestMap,               -- For testing purposes
      mathExtMap,
      solverExtMap
    ])
