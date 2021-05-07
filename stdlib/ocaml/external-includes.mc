include "ext/math-ext.ext-ocaml.mc"

type ExternalImplDef = {ident : String, ty : Type, libraries : [String]}

type ExternalImpl =
  {name : Name, extIdent : String, extTy : Type, libraries : [String]}

type ExternalMap = Map String [ExternalImpl]

let _testExternals =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("testZero", [
      { ident = "Float.zero", ty = tyfloat_, libraries = [] }
    ]),
    ("testExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("testListMap", [
      { ident = "List.map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                        tylist_ (tyvar_ "a"),
                        tylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("testListConcatMap", [
      { ident = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tylist_ (tyvar_ "b")),
                        tylist_ (tyvar_ "a"),
                        tylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("testNonExistant", [
      { ident = "none", ty = tyint_, libraries = ["no-lib"] }
    ]),
    ("testBatZero", [
      { ident = "BatInt.zero", ty = tyint_, libraries = ["batteries"] }
    ])
  ]

-- NOTE(oerikss, 2021-04-30) Add your external maps here. This is a temporary
-- solution. In the end we want to provide these definitions outside the
-- compiler (which will require some parsing).
let globalExternalMap : ExternalMap =
  mapMapWithKey
  (lam id : String.
    map (lam imp : ExternalImplDef.
          {name = nameSym id,
           extIdent = imp.ident,
           extTy = imp.ty,
           libraries = imp.libraries}))
  (foldl1 mapUnion
    [
      _testExternals, -- For testing purposes
      mathExtMap
    ])
