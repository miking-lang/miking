include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let reflectionMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("isfloat", [
      impl {
        expr = "(fun x -> Obj.tag (Obj.repr x) = Obj.double_tag)",
        ty = tyarrows_ [tyfloat_, tybool_]
      }
    ])
  ]
