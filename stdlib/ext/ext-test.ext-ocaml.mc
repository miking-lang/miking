include "map.mc"
include "ocaml/ast.mc"

let implWithLibs = lam arg : { ident : String, ty : Type, libraries : [String] }.
  { ident = arg.ident, ty = arg.ty, libraries = arg.libraries, cLibraries = [] }

let impl = lam arg : { ident : String, ty : Type }.
  implWithLibs { ident = arg.ident, ty = arg.ty, libraries = [] }

let extTestMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("extTestListOfLists", [
      impl
      {
        ident = "Boot.Exttest.list_of_lists",
        ty = otylist_ (otylist_ tyint_)
      }
    ]),
    ("extTestListHeadHead", [
      impl
      {
        ident = "Boot.Exttest.list_hd_hd",
        ty = tyarrow_ (otylist_ (otylist_ (otyparam_ "a"))) (otyparam_ "a")
      }
    ]),
    ("extTestArrayOfArrays", [
      impl
      {
        ident = "Boot.Exttest.array_of_arrays",
        ty = otyarray_ (otyarray_ tyint_)
      }
    ]),
    ("extTestArrayHeadHead", [
      impl
      {
        ident = "Boot.Exttest.array_hd_hd",
        ty = tyarrow_ (otyarray_ (otyarray_ (otyparam_ "a"))) (otyparam_ "a")
      }
    ]),
    ("extTestFlip", [
      impl
      {
        ident = "Fun.flip",
        ty = tyarrows_ [tyarrows_ [(otyparam_ "a"),
                                   (otyparam_ "b"),
                                   (otyparam_ "c")],
                        (otyparam_ "b"),
                        (otyparam_ "a"),
                        (otyparam_ "c")
                       ]
      }
    ]),
    ("extTestUnit1", [
      impl
      {
        ident = "Boot.Exttest.unit1",
        ty = tyarrow_ tyint_ (otytuple_ [])
      }
    ]),
    ("extTestUnit2", [
      impl
      {
        ident = "Boot.Exttest.unit2",
        ty = tyarrow_ (otytuple_ []) tyint_
      }
    ]),
    ("extTestTuple1", [
      impl
      {
        ident = "Boot.Exttest.tuple1",
        ty = otytuple_ [tyint_, tyfloat_]
      }
    ]),
    ("extTestTuple2", [
      impl
      {
        ident = "Boot.Exttest.tuple2",
        ty = otytuple_ [otylist_ tyint_, tyint_]
      }
    ]),
    ("extTestTuple10th", [
      impl
      {
        ident = "Boot.Exttest.tuple1_0th",
        ty = tyarrow_ (otytuple_ [tyint_, tyfloat_]) tyint_
      }
    ]),
    ("extTestTuple20th", [
      impl
      {
        ident = "Boot.Exttest.tuple2_0th",
        ty = tyarrow_ (otytuple_ [otylist_ tyint_, tyint_]) (otylist_ tyint_)
      }
    ]),
    ("extTestRecord1", [
      impl
      {
        ident = "Boot.Exttest.myrec1",
        ty = otyrecord_
              (otyvarext_ "Boot.Exttest.myrec1_t" [])
              [("a", tyint_), ("b", tyfloat_)]
      }
    ]),
    ("extTestRecord1A", [
      impl
      {
        ident = "Boot.Exttest.myrec1_a",
        ty = tyarrow_ (otyrecord_
                        (otyvarext_ "Boot.Exttest.myrec1_t" [])
                        [("a", tyint_), ("b", tyfloat_)])
                      tyint_
      }
    ]),
    ("extTestRecord2", [
      impl
      {
        ident = "Boot.Exttest.myrec2",
        ty = otyrecord_
              (otyvarext_ "Boot.Exttest.myrec2_t" [])
              [("a", otylist_ tyint_), ("b", tyint_)]
      }
    ]),
    ("extTestRecord2A", [
      impl
      {
        ident = "Boot.Exttest.myrec2_a",
        ty = tyarrow_ (otyrecord_
                        (otyvarext_ "Boot.Exttest.myrec2_t" [])
                        [("a", otylist_ tyint_), ("b", tyint_)])
                      (otylist_ tyint_)
      }
    ]),
    ("extTestRecord3", [
      impl
      {
        ident = "Boot.Exttest.myrec3",
        ty = otyrecord_
              (otyvarext_ "Boot.Exttest.myrec3_t" [])
              [
                ("a"
                ,otyrecord_
                  (otyvarext_ "Boot.Exttest.myrec1_t" [])
                  [("a", tyint_), ("b", tyfloat_)]),
                ("b"
                ,otyrecord_
                  (otyvarext_ "Boot.Exttest.myrec2_t" [])
                  [("a", otylist_ tyint_), ("b", tyint_)])
              ]
      }
    ]),
    ("extTestRecord3BA", [
      impl
      {
        ident = "Boot.Exttest.myrec3_b_a",
        ty =
          tyarrow_
            (otyrecord_
              (otyvarext_ "Boot.Exttest.myrec3_t" [])
              [
                ("a"
                ,otyrecord_
                  (otyvarext_ "Boot.Exttest.myrec1_t" [])
                  [("a", tyint_), ("b", tyfloat_)]),
                ("b"
                ,otyrecord_
                  (otyvarext_ "Boot.Exttest.myrec2_t" [])
                  [("a", otylist_ tyint_), ("b", tyint_)])
              ])
            (otylist_ tyint_)
      }
    ]),
    ("extTestArgLabel", [
      impl
      {
        ident = "Boot.Exttest.arg_label",
        ty = tyarrows_ [otylabel_ "b" tyint_, otylabel_ "a" tyint_, tyint_]
      }
    ]),
    ("extTestGenarrIntNumDims", [
      impl
      {
        ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutint_ tyint_
      }
    ]),
    ("extTestGenarrFloatNumDims", [
      impl
      {
        ident = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutfloat_ tyint_
      }
    ]),
    ("extTestGenarrIntSliceLeft", [
      impl
      {
        ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutint_,
                        otyarray_ tyint_,
                        otygenarrayclayoutint_]
      }
    ]),
    ("extTestGenarrFloatSliceLeft", [
      impl
      {
        ident = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutfloat_,
                        otyarray_ tyint_,
                        otygenarrayclayoutfloat_]
      }
    ]),
    ("extTestArray2IntSliceLeft", [
      impl
      {
        ident = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutint_ 2,
                         tyint_,
                         otybaarrayclayoutint_ 1]
      }
    ]),
    ("extTestArray2FloatSliceLeft", [
      impl
      {
        ident = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutfloat_ 2,
                        tyint_,
                        otybaarrayclayoutfloat_ 1]
      }
    ]),
    ("extTestArray2IntOfGenarr", [
      impl
      {
        ident = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutint_ (otybaarrayclayoutint_ 2)
      }
    ]),
    ("extTestArray2FloatOfGenarr", [
      impl
      {
        ident = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutfloat_ (otybaarrayclayoutfloat_ 2)
      }
    ]),
    ("extTestZero", [
      impl { ident = "Float.zero", ty = tyfloat_ }
    ]),
    ("extTestExp", [
      impl { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("extTestListMap", [
      impl
      {
        ident = "List.map",
        ty = tyarrows_ [tyarrow_ (tycon_ "a") (tycon_ "b"),
                        otylist_ (tycon_ "a"),
                        otylist_ (tycon_ "b")]
      }
    ]),
    ("extTestListConcatMap", [
      impl
      {
        ident = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (tycon_ "a") (otylist_ (tycon_ "b")),
                        otylist_ (tycon_ "a"),
                        otylist_ (tycon_ "b")]
      }
    ]),
    ("extTestNonExistant", [
      implWithLibs { ident = "none", ty = tyint_, libraries = ["no-lib"] }
    ])
  ]
