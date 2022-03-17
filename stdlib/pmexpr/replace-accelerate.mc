-- Replaces all TmAccelerate terms with a function call referring to an
-- external function (which is added to the generated OCaml code). The function
-- result, and all its arguments, are wrapped in calls to convertAccelerateParameters to ensure
-- they have a valid OCaml type.

include "mexpr/type-lift.mc"
include "ocaml/ast.mc"
include "ocaml/external.mc"
include "ocaml/generate.mc"
include "ocaml/pprint.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"
include "pmexpr/utils.mc"

lang PMExprReplaceAccelerate =
  PMExprAst + OCamlGenerateExternal + OCamlTopAst + OCamlPrettyPrint

  sem _tensorToOCamlType =
  | TyTensor {ty = ty & (TyInt _ | TyFloat _), info = info} ->
    let layout = OTyBigarrayClayout {info = info} in
    let elemType =
      match ty with TyInt _ then OTyBigarrayIntElt {info = info}
      else OTyBigarrayFloat64Elt {info = info} in
    OTyBigarrayGenarray {info = info, tys = [ty, elemType, layout]}
  | TyTensor t ->
    infoErrorExit t.info "Cannot convert tensor of unsupported type"

  sem _mexprToOCamlType (env : GenerateEnv) (acc : [Top]) =
  | ty & (TyCon {info = info, ident = ident}) ->
    let unwrapType = lam ty.
      let ty = typeUnwrapAlias env.aliases ty in
      match ty with TyCon {ident = ident} then
        match mapLookup ident env.constrs with Some ty then
         ty
        else ty
      else ty
    in
    _mexprToOCamlType env acc (unwrapType ty)
  | ty & (TyRecord {info = info, labels = labels, fields = fields}) ->
    match record2tuple fields with Some tys then
      (acc, OTyTuple {info = info, tys = tys})
    else
      match
        mapAccumL
          (lam acc. lam p : (SID, Type).
            match p with (sid, ty) in
            match _mexprToOCamlType env acc ty with (acc, ty) in
            -- NOTE(larshum, 2022-03-17): We explicitly use the label escaping
            -- of the OCaml pretty-printer to ensure the labels of the fields
            -- match.
            let str = pprintLabelString (sidToString sid) in
            (acc, (str, ty)))
          acc (mapBindings fields)
      with (acc, ocamlTypedFields) in
      -- NOTE(larshum, 2022-03-17): Add a type definition for the OCaml record
      -- and use it as the target for conversion.
      let recTyId = nameSym "record" in
      let tyident = OTyVar {info = info, ident = recTyId} in
      let recTy = OTyRecord {
        info = info, fields = ocamlTypedFields, tyident = tyident} in
      let recTyDecl = OTopTypeDecl {ident = recTyId, ty = ty} in
      (snoc acc recTyDecl, recTy)
  | TySeq {info = info, ty = ty} ->
    (acc, OTyArray {info = info, ty = _mexprToOCamlType ty})
  | ty & (TyTensor _) -> (acc, _tensorToOCamlType ty)
  | ty -> (acc, ty)

  sem wrapInConvertData (env : GenerateEnv) (acc : [Top]) =
  | t ->
    let ty = tyTm t in
    match _mexprToOCamlType env acc ty with (acc, ocamlTy) in
    match convertData (infoTm t) env t ty ocamlTy with (_, e) in
    (acc, e)

  sem convertAccelerateParametersH (env : GenerateEnv) (acc : [Top]) =
  | TmApp t ->
    match convertAccelerateParametersH env acc t.lhs with (acc, lhs) in
    match wrapInConvertData env acc t.rhs with (acc, rhs) in
    (acc, TmApp {{t with lhs = lhs} with rhs = rhs})
  | t -> (acc, t)

  sem convertAccelerateParameters (env : GenerateEnv) (acc : [Top]) =
  | ast ->
    match convertAccelerateParametersH env acc ast with (acc, ast) in
    let ty = tyTm ast in
    match _mexprToOCamlType env acc ty with (acc, ocamlTy) in
    match convertData (infoTm ast) env ast ocamlTy ty with (_, ast) in
    (acc, ast)

  -- We replace the auxilliary acceleration terms in the AST, by removing any
  -- let-expressions involving an accelerate term and updates calls to such
  -- terms to properly convert types of parameters and the return value.
  --
  -- The result is a list of OCaml record definitions, needed to handle the
  -- data conversion of record types, and an AST.
  sem replaceAccelerate (accelerated : Map Name AccelerateData)
                        (env : GenerateEnv) =
  | t -> replaceAccelerateH accelerated env [] t

  sem replaceAccelerateH (accelerated : Map Name AccelerateData)
                         (env : GenerateEnv)
                         (acc : [Top]) =
  | t & (TmApp {lhs = lhs, ty = appTy}) ->
    let appArgs = collectAppArguments t in
    match appArgs with (TmVar {ident = id}, args) then
      if mapMem id accelerated then
        -- NOTE(larshum, 2021-09-17): Remove the dummy parameter if it is not
        -- the only parameter.
        match args with _ ++ [TmConst {val = CInt {val = 0}}] then
          let lhs = withType appTy lhs in
          convertAccelerateParameters env acc lhs
        else convertAccelerateParameters env acc t
      else (acc, t)
    else (acc, t)
  | TmLet t ->
    if mapMem t.ident accelerated then
      replaceAccelerateH accelerated env acc t.inexpr
    else
      match replaceAccelerateH accelerated env acc t.body with (acc, body) in
      match replaceAccelerateH accelerated env acc t.inexpr with (acc, inexpr) in
      (acc, TmLet {{t with body = body} with inexpr = inexpr})
  | t ->
    smapAccumL_Expr_Expr (replaceAccelerateH accelerated env) acc t
end
