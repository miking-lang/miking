-- Replaces all TmAccelerate terms with a function call referring to an
-- external function (which is added to the generated OCaml code). The function
-- result, and all its arguments, are wrapped in calls to convertAccelerateParameters to ensure
-- they have a valid OCaml type.

include "mexpr/rewrite/extract.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"
include "ocaml/external.mc"

lang PMExprReplaceAccelerate = MExprParallelKeywordMaker + OCamlGenerateExternal
  sem _mexprToOCamlType =
  | TySeq t -> OTyArray {info = t.info, ty = _mexprToOCamlType t.ty}
  | t -> t

  sem wrapInConvertData =
  | t ->
    let ty = ty t in
    let ocamlTy = _mexprToOCamlType ty in
    match convertData (infoTm t) emptyGenerateEnv t ty ocamlTy with (_, e) then
      e
    else never

  sem convertAccelerateParametersH =
  | TmApp t ->
    let lhs = convertAccelerateParametersH t.lhs in
    let rhs = wrapInConvertData t.rhs in
    TmApp {{t with lhs = lhs} with rhs = rhs}
  | t -> t

  sem convertAccelerateParameters =
  | ast ->
    let ast = convertAccelerateParametersH ast in
    let ty = ty ast in
    let ocamlTy = _mexprToOCamlType ty in
    match convertData (infoTm ast) emptyGenerateEnv ast ocamlTy ty
    with (_, ast) then
      ast
    else never

  -- We replace the auxilliary acceleration terms in the AST, by removing any
  -- let-expressions involving an accelerate term and updates calls to such
  -- terms to properly convert types of parameters and the return value.
  sem replaceAccelerate (accelerated : Map Name AccelerateData) =
  | t & (TmApp {lhs = lhs, ty = appTy}) ->
    let appArgs = collectAppArguments t in
    match appArgs with (TmVar {ident = id}, args) then
      if mapMem id accelerated then
        -- NOTE(larshum, 2021-09-17): Remove the dummy parameter if it is not
        -- the only parameter.
        match args with _ ++ [TmConst {val = CInt {val = 0}}] then
          let lhs = withType appTy lhs in
          convertAccelerateParameters lhs
        else convertAccelerateParameters t
      else t
    else t
  | TmLet t ->
    if mapMem t.ident accelerated then
      replaceAccelerate accelerated t.inexpr
    else TmLet {{t with body = replaceAccelerate accelerated t.body}
                   with inexpr = replaceAccelerate accelerated t.inexpr}
  | t -> smap_Expr_Expr (replaceAccelerate accelerated) t
end
