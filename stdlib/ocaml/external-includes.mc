include "ext/math-ext.ext-ocaml.mc"

type ExternalImpl = {name : Name, extIdent : String, extTy : Type}

let _testExternals =
  use OCamlTypeAst in
  mapFromList cmpString
  [
    ("testZero", [
      { ident = "Float.zero", ty = tyfloat_ }
    ]),
    ("testExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("testListMap", [
      { ident = "List.map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                        tylist_ (tyvar_ "a"),
                        tylist_ (tyvar_ "b")] }
    ]),
    ("testListConcatMap", [
      { ident = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tylist_ (tyvar_ "b")),
                        tylist_ (tyvar_ "a"),
                        tylist_ (tyvar_ "b")] }
    ])
  ]

-- NOTE(oerikss, 2021-04-30) Add your external maps here. This is a temporary
-- solution. In the end we want to provide these definitions outside the
-- compiler (which will require some parsing).
let externalMap =
  mapMapWithKey
  (lam id : String.
    map (lam imp : {ident : String, ty : Type}.
          {name = nameSym id, extIdent = imp.ident, extTy = imp.ty}))
  (foldl1 mapUnion
    [
      _testExternals, -- For testing purposes
      mathExtMap
    ])
