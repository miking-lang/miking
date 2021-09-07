include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { ident : String, ty : Type }.
  { ident = arg.ident, ty = arg.ty, libraries = [], cLibraries = [] }

let mathExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("externalExp", [
      impl { ident = "Float.exp", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("externalLog", [
      impl { ident = "Float.log", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("externalAtan", [
      impl { ident = "Float.atan", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("externalSin", [
      impl { ident = "Float.sin", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("externalCos", [
      impl { ident = "Float.cos", ty = tyarrow_ tyfloat_ tyfloat_ }
    ]),
    ("externalAtan2", [
      impl { ident = "Float.atan2", ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_] }
    ]),
    ("externalPow", [
      impl { ident = "Float.pow", ty = tyarrows_ [tyfloat_, tyfloat_, tyfloat_] }
    ]),
    ("externalSqrt", [
      impl { ident = "Float.sqrt", ty = tyarrow_ tyfloat_ tyfloat_ }
    ])
  ]
