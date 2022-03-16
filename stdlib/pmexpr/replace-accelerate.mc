-- Replaces all TmAccelerate terms with a function call referring to an
-- external function (which is added to the generated OCaml code). The function
-- result, and all its arguments, are wrapped in calls to convertAccelerateParameters to ensure
-- they have a valid OCaml type.

include "mexpr/type-lift.mc"
include "ocaml/external.mc"
include "ocaml/generate.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"
include "pmexpr/utils.mc"

lang PMExprReplaceAccelerate = PMExprAst + OCamlGenerateExternal + MExprTypeLift
  sem _tensorToOCamlType =
  | TyTensor {ty = ty & (TyInt _ | TyFloat _), info = info} ->
    let layout = OTyBigarrayClayout {info = info} in
    let elemType =
      match ty with TyInt _ then OTyBigarrayIntElt {info = info}
      else OTyBigarrayFloat64Elt {info = info} in
    OTyBigarrayGenarray {info = info, tys = [ty, elemType, layout]}
  | TyTensor t ->
    infoErrorExit t.info "Cannot convert tensor of unsupported type"

  sem _mexprToOCamlType (env : GenerateEnv) =
  | ty & (TyCon _) ->
    let unwrapType = lam ty.
      let ty = typeUnwrapAlias env.aliases ty in
      match ty with TyCon {ident = ident} then
        match mapLookup ident env.constrs with Some ty then
         ty
        else ty
      else ty
    in
    let uty = unwrapType ty in
    match uty with TyRecord {labels = labels, fields = fields, info = info} then
      let ocamlTypedFields =
        map
          (lam p : (SID, Type).
            match p with (sid, ty) in
            (sidToString sid, _mexprToOCamlType env ty))
          (mapBindings fields) in
      OTyRecord {info = info, fields = ocamlTypedFields, tyident = ty}
    else match uty with TySeq {ty = ty, info = info} then
      OTyArray {info = info, ty = _mexprToOCamlType uty}
    else match uty with TyTensor _ then
      _tensorToOCamlType uty
    else uty
  -- NOTE(larshum, 2022-03-16): Empty record types are not type-lifted.
  | TyRecord {info = info, labels = []} -> OTyTuple {info = info, tys = []}
  | ty & (TyTensor _) -> _tensorToOCamlType ty
  | ty -> ty

  sem wrapInConvertData (env : GenerateEnv) =
  | t ->
    let ty = tyTm t in
    let ocamlTy = _mexprToOCamlType env ty in
    match convertData (infoTm t) env t ty ocamlTy with (_, e) in
    e

  sem convertAccelerateParametersH (env : GenerateEnv) =
  | TmApp t ->
    let lhs = convertAccelerateParametersH env t.lhs in
    let rhs = wrapInConvertData env t.rhs in
    TmApp {{t with lhs = lhs} with rhs = rhs}
  | t -> t

  sem convertAccelerateParameters (env : GenerateEnv) =
  | ast ->
    let ast = convertAccelerateParametersH env ast in
    let ty = tyTm ast in
    let ocamlTy = _mexprToOCamlType env ty in
    match convertData (infoTm ast) env ast ocamlTy ty
    with (_, ast) in
    ast

  -- We replace the auxilliary acceleration terms in the AST, by removing any
  -- let-expressions involving an accelerate term and updates calls to such
  -- terms to properly convert types of parameters and the return value.
  sem replaceAccelerate (accelerated : Map Name AccelerateData)
                        (env : GenerateEnv) =
  | t & (TmApp {lhs = lhs, ty = appTy}) ->
    let appArgs = collectAppArguments t in
    match appArgs with (TmVar {ident = id}, args) then
      if mapMem id accelerated then
        -- NOTE(larshum, 2021-09-17): Remove the dummy parameter if it is not
        -- the only parameter.
        match args with _ ++ [TmConst {val = CInt {val = 0}}] then
          let lhs = withType appTy lhs in
          convertAccelerateParameters env lhs
        else convertAccelerateParameters env t
      else t
    else t
  | TmLet t ->
    if mapMem t.ident accelerated then
      replaceAccelerate accelerated env t.inexpr
    else TmLet {{t with body = replaceAccelerate accelerated env t.body}
                   with inexpr = replaceAccelerate accelerated env t.inexpr}
  | t -> smap_Expr_Expr (replaceAccelerate accelerated env) t
end
