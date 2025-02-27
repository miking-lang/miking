include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let arrExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("externalArrMake", [
      impl {
        expr = "Array.make",
        ty = tyarrows_ [tyint_, otyopaque_, otyopaque_]
      }
    ]),
    ("externalArrMakeUninitFloat", [
      impl {
        expr = "Array.create_float",
        ty = tyarrow_ tyint_ otyopaque_
      }
    ]),
    ("externalArrLength", [
      impl {
        expr = "Array.length",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("externalArrGet", [
      impl {
        expr = "Array.get",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_]
      }
    ]),
    ("externalArrSet", [
      impl {
        expr = "Array.set",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_, otyunit_]
      }
    ]),
    ("externalArrSub", [
      impl {
        expr = "Array.sub",
        ty = tyarrows_ [otyopaque_, tyint_, tyint_, otyopaque_]
      }
    ]),
    ("extArrKindFloat32", [
      impl {
        expr = "Bigarray.float32",
        ty = otyopaque_
      }
    ]),
    ("extArrKindFloat64", [
      impl {
        expr = "Bigarray.float64",
        ty = otyopaque_
      }
    ]),
    ("externalExtArrKind", [
      impl {
        expr = "Bigarray.Array1.kind",
        ty = tyarrow_ otyopaque_ otyopaque_
      }
    ]),
    ("externalExtArrMakeUninit", [
      impl {
        expr = "(fun kind -> Bigarray.Array1.create kind Bigarray.c_layout)",
        ty = tyarrows_ [ otyopaque_, tyint_, otyopaque_]
      }
    ]),
    ("externalExtArrLength", [
      impl {
        expr = "Bigarray.Array1.dim",
        ty = tyarrow_ otyopaque_ tyint_
      }
    ]),
    ("externalExtArrGet", [
      impl {
        expr = "Bigarray.Array1.get",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_]
      }
    ]),
    ("externalExtArrSet", [
      impl {
        expr = "Bigarray.Array1.set",
        ty = tyarrows_ [otyopaque_, tyint_, otyopaque_, otyunit_]
      }
    ]),
    ("externalExtArrCopy", [
      impl {
        expr = "(fun a -> let b = Bigarray.Array1.create (Bigarray.Array1.kind a) Bigarray.c_layout (Bigarray.Array1.dim a) in Bigarray.Array1.blit a b; b)",
        ty = tyarrows_ [otyopaque_, otyopaque_]
      }
    ]),
    ("externalExtArrFill", [
      impl {
        expr = "Bigarray.Array1.fill",
        ty = tyall_ "a" (tyarrows_ [otyopaque_, tyvar_ "a", otyunit_])
      }
    ])
  ]
