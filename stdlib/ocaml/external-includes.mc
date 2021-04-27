include "ext/math-ext.ext-ocaml.mc"

type ExternalImpl = {name : Name, extIdent : String, extTy : Type}

let _testExternals =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("testExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("testListMap", [
      { ident = "List.map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                        tylist_ (tyvar_ "a"),
                        tylist_ (tyvar_ "b")] }
    ])
  ]

let externalMap =
  mapMapWithKey
  (lam id : String.
    map (lam imp : ExternalImpl.
          {name = nameSym id, extIdent = imp.ident, extTy = imp.ty}))
  (foldl1 mapUnion
    [
      _testExternals, -- For testing purposes
      mathExtMap
    ])
