include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["owl"], cLibraries = [] }

let owlDenseMatrixGenericInplaceUnop = lam name. lam shape1. lam shape2.
  join [
    "(fun m n a b -> Owl_dense_matrix.Generic.",
    name,
    " ~out:(Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 b) ",
    shape2,
    ")) (Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 a) ",
    shape1,
    ")))"]

let owlDenseMatrixGenericInplaceUnopTy = tyarrows_ [
  tyint_, tyint_, otyopaque_, otyopaque_, otyunit_]

let owlDenseMatrixGenericInplaceBinop = lam name.
  join [
    "(fun m n a b c -> Owl_dense_matrix.Generic.",
    name,
    " ~out:(Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 c) m n)) (Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 a) m n)) (Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 b) m n)))"]

let owlDenseMatrixGenericInplaceBinopTy = tyarrows_ [
  tyint_, tyint_, otyopaque_, otyopaque_, otyopaque_, otyunit_]

let matExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("externalMatTranspose", [
      impl {
        expr = owlDenseMatrixGenericInplaceUnop "transpose_" "m n" "n m",
        ty = owlDenseMatrixGenericInplaceUnopTy
      }
    ]),
    ("externalMatElemExp", [
      impl {
        expr = owlDenseMatrixGenericInplaceUnop "exp_" "m n" "m n",
        ty = owlDenseMatrixGenericInplaceUnopTy
      }
    ]),
    ("externalMatElemLog", [
      impl {
        expr = owlDenseMatrixGenericInplaceUnop "log_" "m n" "m n",
        ty = owlDenseMatrixGenericInplaceUnopTy
      }
    ]),
    ("externalMatElemMul", [
      impl {
        expr = owlDenseMatrixGenericInplaceBinop "mul_",
        ty = owlDenseMatrixGenericInplaceBinopTy
      }
    ]),
    ("externalMatExp", [
      impl {
        expr = "(fun m n a -> Bigarray.reshape_1 (Owl_linalg_generic.expm (Bigarray.genarray_of_array2 (Bigarray.reshape_2 (Bigarray.genarray_of_array1 a) m n))) (m * n))",
        ty = tyarrows_ [tyint_,  tyint_, otyopaque_, otyopaque_]
      }
    ])
  ]
