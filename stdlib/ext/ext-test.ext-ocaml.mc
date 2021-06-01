include "map.mc"
include "ocaml/ast.mc"

let extTestMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("extTestListOfLists", [
      {
        ident = "Boot.Exttest.list_of_lists",
        ty = otylist_ (otylist_ tyint_),
        libraries = []
      }
    ]),
    ("extTestListHeadHead", [
      {
        ident = "Boot.Exttest.list_hd_hd",
        ty = tyarrow_ (otylist_ (otylist_ (otyparam_ "a"))) (otyparam_ "a"),
        libraries = []
      }
    ]),
    ("extTestArrayOfArrays", [
      {
        ident = "Boot.Exttest.array_of_arrays",
        ty = otyarray_ (otyarray_ tyint_),
        libraries = []
      }
    ]),
    ("extTestArrayHeadHead", [
      {
        ident = "Boot.Exttest.array_hd_hd",
        ty = tyarrow_ (otyarray_ (otyarray_ (otyparam_ "a"))) (otyparam_ "a"),
        libraries = []
      }
    ]),
    ("extTestFlip", [
      {
        ident = "Fun.flip",
        ty = tyarrows_ [tyarrows_ [(otyparam_ "a"),
                                   (otyparam_ "b"),
                                   (otyparam_ "c")],
                        (otyparam_ "b"),
                        (otyparam_ "a"),
                        (otyparam_ "c")
                       ],
        libraries = []
      }
    ]),
    ("extTestUnit1", [
      {
        ident = "Boot.Exttest.unit1",
        ty = tyarrow_ tyint_ (otytuple_ []),
        libraries = []
      }
    ]),
    ("extTestUnit2", [
      {
        ident = "Boot.Exttest.unit2",
        ty = tyarrow_ (otytuple_ []) tyint_,
        libraries = []
      }
    ]),
    ("extTestTuple1", [
      {
        ident = "Boot.Exttest.tuple1",
        ty = otytuple_ [tyint_, tyfloat_],
        libraries = []
      }
    ]),
    ("extTestTuple2", [
      {
        ident = "Boot.Exttest.tuple2",
        ty = otytuple_ [otylist_ tyint_, tyint_],
        libraries = []
      }
    ]),
    ("extTestTuple10th", [
      {
        ident = "Boot.Exttest.tuple1_0th",
        ty = tyarrow_ (otytuple_ [tyint_, tyfloat_]) tyint_,
        libraries = []
      }
    ]),
    ("extTestTuple20th", [
      {
        ident = "Boot.Exttest.tuple2_0th",
        ty = tyarrow_ (otytuple_ [otylist_ tyint_, tyint_]) (otylist_ tyint_),
        libraries = []
      }
    ]),
    ("extTestRecord1", [
      {
        ident = "Boot.Exttest.myrec1",
        ty = otyrecord_
              (otyvarext_ "Boot.Exttest.myrec1_t" [])
              [("a", tyint_), ("b", tyfloat_)],
        libraries = []
      }
    ]),
    ("extTestRecord1A", [
      {
        ident = "Boot.Exttest.myrec1_a",
        ty = tyarrow_ (otyrecord_
                        (otyvarext_ "Boot.Exttest.myrec1_t" [])
                        [("a", tyint_), ("b", tyfloat_)])
                      tyint_,
        libraries = []
      }
    ]),
    ("extTestRecord2", [
      {
        ident = "Boot.Exttest.myrec2",
        ty = otyrecord_
              (otyvarext_ "Boot.Exttest.myrec2_t" [])
              [("a", otylist_ tyint_), ("b", tyint_)],
        libraries = []
      }
    ]),
    ("extTestRecord2A", [
      {
        ident = "Boot.Exttest.myrec2_a",
        ty = tyarrow_ (otyrecord_
                        (otyvarext_ "Boot.Exttest.myrec2_t" [])
                        [("a", otylist_ tyint_), ("b", tyint_)])
                      (otylist_ tyint_),
        libraries = []
      }
    ]),
    ("extTestArgLabel", [
      {
        ident = "Boot.Exttest.arg_label",
        ty = tyarrows_ [otylabel_ "b" tyint_, otylabel_ "a" tyint_, tyint_],
        libraries = []
      }
    ]),
    ("extTestGenarrIntNumDims", [
      { ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutint_ tyint_,
        libraries = [] }
    ]),
    ("extTestGenarrFloatNumDims", [
      { ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutfloat_ tyint_,
        libraries = [] }
    ]),
    ("extTestGenarrIntSliceLeft", [
      { ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutint_,
                        otyarray_ tyint_,
                        otygenarrayclayoutint_],
        libraries = [] }
    ]),
    ("extTestGenarrFloatSliceLeft", [
      { ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutfloat_,
                        otyarray_ tyint_,
                        otygenarrayclayoutfloat_],
        libraries = [] }
    ]),
    ("extTestArray2IntSliceLeft", [
      { ident = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutint_ 2,
                         tyint_,
                         otybaarrayclayoutint_ 1],
        libraries = [] }
    ]),
    ("extTestArray2FloatSliceLeft", [
      { ident = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutfloat_ 2,
                        tyint_,
                        otybaarrayclayoutfloat_ 1],
        libraries = [] }
    ]),
    ("extTestArray2IntOfGenarr", [
      { ident = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutint_ (otybaarrayclayoutint_ 2) ,
        libraries = [] }
    ]),
    ("extTestArray2FloatOfGenarr", [
      { ident = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutfloat_ (otybaarrayclayoutfloat_ 2) ,
        libraries = [] }
    ]),
    ("extTestZero", [
      { ident = "Float.zero", ty = tyfloat_, libraries = [] }
    ]),
    ("extTestExp", [
      { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_, libraries = [] }
    ]),
    ("extTestListMap", [
      { ident = "List.map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                        otylist_ (tyvar_ "a"),
                        otylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("extTestListConcatMap", [
      { ident = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (tyvar_ "a") (otylist_ (tyvar_ "b")),
                        otylist_ (tyvar_ "a"),
                        otylist_ (tyvar_ "b")],
        libraries = [] }
    ]),
    ("extTestNonExistant", [
      { ident = "none", ty = tyint_, libraries = ["no-lib"] }
    ])
  ]
