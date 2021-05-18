include "ext/batteries.ext-ocaml.mc" -- For testing
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
                        otylist_ (tyvar_ "a"),
                        otylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("testListConcatMap", [
      { ident = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (otylist_ (tyvar_ "b")),
                        otylist_ (tyvar_ "a"),
                        otylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("testNonExistant", [
      { ident = "none", ty = tyint_, libraries = ["no-lib"] }
    ]),
    ("testGenarrIntNumDims", [
      { ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutint_ tyint_,
        libraries = [] }
    ]),
    ("testGenarrFloatNumDims", [
      { ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutfloat_ tyint_,
        libraries = [] }
    ]),
    ("testGenarrIntSliceLeft", [
      { ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutint_,
                        otyarray_ tyint_,
                        otygenarrayclayoutint_],
        libraries = [] }
    ]),
    ("testGenarrFloatSliceLeft", [
      { ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutfloat_,
                        otyarray_ tyint_,
                        otygenarrayclayoutfloat_],
        libraries = [] }
    ]),
    ("testIdUnit", [
      { ident = "Fun.id", ty = tyarrow_ otyunit_ otyunit_, libraries = [] }
    ]),
    ("testIdArrayInt", [
      { ident = "Fun.id",
        ty = tyarrow_ (otyarray_ tyint_) (otyarray_ tyint_),
        libraries = [] }
    ]),
    ("testIdTupleInt", [
      { ident = "Fun.id",
        ty = tyarrow_ (otytuple_ [tyint_, tyint_]) (otytuple_ [tyint_, tyint_]),
        libraries = [] }
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
      batteries,      -- For testing purposes
      mathExtMap
    ])
