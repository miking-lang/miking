include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["boot"], cLibraries = [] }

let arrayExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("arrayCreateFloat", [
      impl {
        expr = "Array.create_float",
        ty = tyarrow_ tyint_ otyopaque_
      }
    ]),
    ("arrayLength", [
      impl {
        expr = "Array.length",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("arrayGet", [
      impl {
        expr = "Array.get",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_]
      }
    ]),
    ("arraySet", [
      impl {
        expr = "Array.set",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_, otyunit_]
      }
    ]),
    ("cArray1CreateFloat", [
      impl {
        expr = "Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout",
        ty = tyarrow_ tyint_ otyopaque_
      }
    ]),
    ("cArray1Dim", [
      impl {
        expr = "Bigarray.Array1.dim",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("cArray1Get", [
      impl {
        expr = "Bigarray.Array1.get",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_]
      }
    ]),
    ("cArray1Set", [
      impl {
        expr = "Bigarray.Array1.set",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_, otyunit_]
      }
    ])
  ]
