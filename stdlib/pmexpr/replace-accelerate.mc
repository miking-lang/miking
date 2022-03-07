-- Replaces all TmAccelerate terms with a function call referring to an
-- external function (which is added to the generated OCaml code). The function
-- result, and all its arguments, are wrapped in calls to convertAccelerateParameters to ensure
-- they have a valid OCaml type.

include "ocaml/external.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"
include "pmexpr/utils.mc"

lang PMExprReplaceAccelerate = PMExprAst + OCamlGenerateExternal
  sem _mexprToOCamlType =
  | TyRecord {labels = [], info = info} -> OTyTuple {info = info, tys = []}
  | TySeq {ty = ty, info = info} ->
    OTyArray {info = info, ty = _mexprToOCamlType ty}
  | TyTensor {ty = ty & (TyInt _ | TyFloat _), info = info} ->
    let layout = OTyBigarrayClayout {info = info} in
    let elemType =
      match ty with TyInt _ then OTyBigarrayIntElt {info = info}
      else OTyBigarrayFloat64Elt {info = info} in
    OTyBigarrayGenarray {info = info, tys = [ty, elemType, layout]}
  | t -> t

  sem wrapInConvertData =
  | t ->
    let ty = tyTm t in
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
    let ty = tyTm ast in
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
