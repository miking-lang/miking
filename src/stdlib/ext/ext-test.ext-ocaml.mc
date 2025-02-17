include "map.mc"
include "ocaml/ast.mc"

let implWithLibs =
  lam arg : { expr : String, ty : use Ast in Type, libraries : [String] }.
    { expr = arg.expr, ty = arg.ty, libraries = arg.libraries, cLibraries = [] }

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  implWithLibs { expr = arg.expr, ty = arg.ty, libraries = [] }

let myrecty1 = otyrecordext_
  (otyvarext_ "Boot.Exttest.myrec1_t" [])
  [
    { label = "a", asLabel = "c", ty = tyint_ },
    { label = "b", asLabel = "d", ty = tyfloat_ }
  ]

let myrecty2 = otyrecordext_
  (otyvarext_ "Boot.Exttest.myrec2_t" [])
  [
    { label = "b", asLabel = "d", ty = tyint_ },
    { label = "a", asLabel = "c", ty = otylist_ tyint_ }
  ]

let myrecty3 = otyrecordext_
  (otyvarext_ "Boot.Exttest.myrec3_t" [])
  [
    {
      label = "a",
      asLabel = "c",
      ty = myrecty1
    },
    {
      label = "b",
      asLabel = "d",
      ty = myrecty2
    }
  ]

let extTestMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("extTestListOfLists", [
      impl
      {
        expr = "Boot.Exttest.list_of_lists",
        ty = otylist_ (otylist_ tyint_)
      }
    ]),
    ("extTestListHeadHead", [
      impl
      {
        expr = "Boot.Exttest.list_hd_hd",
        ty = tyarrow_ (otylist_ (otylist_ (otyparam_ "a"))) (otyparam_ "a")
      }
    ]),
    ("extTestArrayOfArrays", [
      impl
      {
        expr = "Boot.Exttest.array_of_arrays",
        ty = otyarray_ (otyarray_ tyint_)
      }
    ]),
    ("extTestArrayHeadHead", [
      impl
      {
        expr = "Boot.Exttest.array_hd_hd",
        ty = tyarrow_ (otyarray_ (otyarray_ (otyparam_ "a"))) (otyparam_ "a")
      }
    ]),
    ("extTestFlip", [
      impl
      {
        expr = "Fun.flip",
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
        expr = "Boot.Exttest.unit1",
        ty = tyarrow_ tyint_ (otytuple_ [])
      }
    ]),
    ("extTestUnit2", [
      impl
      {
        expr = "Boot.Exttest.unit2",
        ty = tyarrow_ (otytuple_ []) tyint_
      }
    ]),
    ("extTestTuple1", [
      impl
      {
        expr = "Boot.Exttest.tuple1",
        ty = otytuple_ [tyint_, tyfloat_]
      }
    ]),
    ("extTestTuple2", [
      impl
      {
        expr = "Boot.Exttest.tuple2",
        ty = otytuple_ [otylist_ tyint_, tyint_]
      }
    ]),
    ("extTestTuple10th", [
      impl
      {
        expr = "Boot.Exttest.tuple1_0th",
        ty = tyarrow_ (otytuple_ [tyint_, tyfloat_]) tyint_
      }
    ]),
    ("extTestTuple20th", [
      impl
      {
        expr = "Boot.Exttest.tuple2_0th",
        ty = tyarrow_ (otytuple_ [otylist_ tyint_, tyint_]) (otylist_ tyint_)
      }
    ]),
    ("extTestRecord1", [
      impl
      {
        expr = "Boot.Exttest.myrec1",
        ty = myrecty1
      }
    ]),
    ("extTestRecord1A", [
      impl
      {
        expr = "Boot.Exttest.myrec1_a",
        ty = tyarrow_ myrecty1 tyint_
      }
    ]),
    ("extTestRecord2", [
      impl
      {
        expr = "Boot.Exttest.myrec2",
        ty = myrecty2
      }
    ]),
    ("extTestRecord2A", [
      impl
      {
        expr = "Boot.Exttest.myrec2_a",
        ty = tyarrow_ myrecty2 (otylist_ tyint_)
      }
    ]),
    ("extTestRecord3", [
      impl
      {
        expr = "Boot.Exttest.myrec3",
        ty = myrecty3
      }
    ]),
    ("extTestRecord3BA", [
      impl
      {
        expr = "Boot.Exttest.myrec3_b_a",
        ty = tyarrow_ myrecty3 (otylist_ tyint_)
      }
    ]),
    ("extTestArgLabel", [
      impl
      {
        expr = "Boot.Exttest.arg_label",
        ty = tyarrows_ [otylabel_ "b" tyint_, otylabel_ "a" tyint_, tyint_]
      }
    ]),
    ("extTestGenarrIntNumDims", [
      impl
      {
        expr = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutint_ tyint_
      }
    ]),
    ("extTestGenarrFloatNumDims", [
      impl
      {
        expr = "Bigarray.Genarray.num_dims",
        ty = tyarrow_ otygenarrayclayoutfloat_ tyint_
      }
    ]),
    ("extTestGenarrIntSliceLeft", [
      impl
      {
        expr = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutint_,
                        otyarray_ tyint_,
                        otygenarrayclayoutint_]
      }
    ]),
    ("extTestGenarrFloatSliceLeft", [
      impl
      {
        expr = "Bigarray.Genarray.slice_left",
        ty = tyarrows_ [otygenarrayclayoutfloat_,
                        otyarray_ tyint_,
                        otygenarrayclayoutfloat_]
      }
    ]),
    ("extTestArray2IntSliceLeft", [
      impl
      {
        expr = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutint_ 2,
                         tyint_,
                         otybaarrayclayoutint_ 1]
      }
    ]),
    ("extTestArray2FloatSliceLeft", [
      impl
      {
        expr = "Bigarray.Array2.slice_left",
        ty = tyarrows_ [otybaarrayclayoutfloat_ 2,
                        tyint_,
                        otybaarrayclayoutfloat_ 1]
      }
    ]),
    ("extTestArray2IntOfGenarr", [
      impl
      {
        expr = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutint_ (otybaarrayclayoutint_ 2)
      }
    ]),
    ("extTestArray2FloatOfGenarr", [
      impl
      {
        expr = "Bigarray.array2_of_genarray",
        ty = tyarrow_ otygenarrayclayoutfloat_ (otybaarrayclayoutfloat_ 2)
      }
    ]),
    ("extTestZero", [
      impl { expr = "Float.zero", ty = tyfloat_ }
    ]),
    ("extTestExp", [
      impl { expr = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("extTestListMap", [
      impl
      {
        expr = "List.map",
        ty = tyarrows_ [tyarrow_ (otyparam_ "a") (otyparam_ "b"),
                        otylist_ (otyparam_ "a"),
                        otylist_ (otyparam_ "b")]
      }
    ]),
    ("extTestListConcatMap", [
      impl
      {
        expr = "List.concat_map",
        ty = tyarrows_ [tyarrow_ (otyparam_ "a") (otylist_ (otyparam_ "b")),
                        otylist_ (otyparam_ "a"),
                        otylist_ (otyparam_ "b")]
      }
    ]),
    ("extTestNonExistant", [
      implWithLibs { expr = "none", ty = tyint_, libraries = ["no-lib"] }
    ])
  ]
