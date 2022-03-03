include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

-- Translates constant applications to an expression node which contains the
-- applied arguments.
lang CudaConstantApp = CudaPMExprAst
  -- NOTE(larshum, 2022-03-02): At this point, we have applied the
  -- well-formedness check, which guarantees that the constants are fully
  -- applied (otherwise the result would be an arrow-type, which is not
  -- allowed).
  sem toConstantExpr (args : [Expr]) =
  | CMap _ -> Some (seqMap_ (get args 0) (get args 1))
  | CFoldl _ -> Some (seqFoldl_ (get args 0) (get args 1) (get args 2))
  | CTensorSliceExn _ -> Some (tensorSliceExn_ (get args 0) (get args 1))
  | CTensorSubExn _ -> Some (tensorSubExn_ (get args 0) (get args 1) (get args 2))
  | _ -> None ()

  sem constantAppToExpr =
  | TmApp t ->
    match collectAppArguments (TmApp t) with (TmConst {val = c}, args) then
      match toConstantExpr args c with Some expr then
        withInfo t.info (withType t.ty expr)
      else TmApp t
    else TmApp t
  | t -> smap_Expr_Expr constantAppToExpr t
end
