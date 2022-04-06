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

lang PMExprReplaceAccelerateBase =
  PMExprAst + OCamlTopAst + OCamlPrettyPrint

  type ReplaceAccelerateEnv = {
    typeLiftEnv : AssocSeq Name Type,
    generateEnv : GenerateEnv
  }
end

lang PMExprConvertMExprToOCaml = PMExprReplaceAccelerateBase
  sem _mexprToOCaml : ReplaceAccelerateEnv -> Option Name -> Expr -> Type -> Expr
  sem _mexprToOCaml env id expr =
  | TyCon {info = info, ident = ident} ->
    let env : ReplaceAccelerateEnv = env in
    match assocSeqLookup {eq=nameEq} ident env.typeLiftEnv with Some ty then
      _mexprToOCaml env (Some ident) expr ty
    else infoErrorExit info "CUDA compiler failed to convert MExpr type"
  | tyrec & (TyRecord {info = info, labels = labels, fields = fields}) ->
    if null labels then expr
    else
      let id =
        match id with Some id then id
        else infoErrorExit info "Found improperly wrapped record type" in
      let tys =
        map
          (lam sid.
            match mapLookup sid fields with Some ty then
              ty
            else infoErrorExit info "Record type has inconsistent labels/fields")
          labels in
      let ns = create (length tys) (lam. nameSym "t") in
      let pvars =
        mapi
          (lam i. lam n.
            PatNamed {ident = PName n, info = info, ty = get tys i})
          ns in
      let pat = OPatTuple {pats = pvars} in
      let tms =
        mapi
          (lam i. lam ident : Name.
            let sid = get labels i in
            let ty = get tys i in
            let var = TmVar {
              ident = ident,
              ty = ty,
              info = info,
              frozen = false
            } in
            _mexprToOCaml env (None ()) (objMagic var) ty)
          ns in
      let rec = TmRecord {
        bindings = mapFromSeq cmpSID (zip labels tms),
        ty = TyCon {ident = id, info = info}, info = info
      } in
      OTmMatch {target = objMagic expr, arms = [(pat, rec)]}
  | TySeq {info = info, ty = ty} ->
    let op = OTmVarExt {ident = intrinsicOpSeq "Helpers.to_array_copy"} in
    let mapop = OTmVarExt {ident = intrinsicOpSeq "map"} in
    let ident = nameSym "x" in
    let var = TmVar {
      ident = ident,
      ty = TyUnknown {info = info},
      info = info,
      frozen = false} in
    let body = _mexprToOCaml env (None ()) var ty in
    TmApp {
      lhs = op,
      rhs = TmApp {
        lhs = TmApp {
          lhs = mapop,
          rhs = TmLam {
            ident = ident,
            tyIdent = TyUnknown {info = info},
            body = body,
            ty = TyUnknown {info = info},
            info = info},
          ty = TyUnknown {info = info},
          info = info},
        rhs = expr,
        ty = TyUnknown {info = info},
        info = info},
      ty = TyUnknown {info = info},
      info = info}
  | ty & (TyTensor {info = info, ty = TyInt _ | TyFloat _}) ->
    let lhs = OTmVarExt {ident = intrinsicOpTensor "Helpers.to_genarray_clayout"} in
    TmApp {lhs = lhs, rhs = expr, ty = ty, info = info}
  | TyTensor {info = info, ty = _} ->
    infoErrorExit info "CUDA compiler can only convert tensors of ints or floats"
  | TyVariant {info = info, constrs = constrs} ->
    infoErrorExit info "Conversion not implemented yet"
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> expr
  | ty -> infoErrorExit (infoTy ty) "CUDA compiler cannot convert MExpr type"
end

lang PMExprConvertOCamlToMExpr = PMExprReplaceAccelerateBase
  sem _ocamlToMExpr : ReplaceAccelerateEnv -> Option Name -> Expr -> Type -> Expr
  sem _ocamlToMExpr env id expr =
  | TyCon {info = info, ident = ident} ->
    let env : ReplaceAccelerateEnv = env in
    match assocSeqLookup {eq=nameEq} ident env.typeLiftEnv with Some ty then
      _ocamlToMExpr env (Some ident) expr ty
    else infoErrorExit info "CUDA compiler failed to convert MExpr type"
  | ty & (TyRecord {info = info, labels = labels, fields = fields}) ->
    if null labels then expr
    else
      let id =
        match id with Some id then id
        else infoErrorExit info "Found improperly wrapped record type" in
      let tys =
        map
          (lam sid.
            match mapLookup sid fields with Some ty then
              ty
            else infoErrorExit info "Record type has inconsistent labels/fields")
          labels in
      let ns = create (length tys) (lam. nameSym "t") in
      let pvars =
        mapi
          (lam i. lam n.
            PatNamed { ident = PName n, info = info, ty = get tys i})
          ns in
      let tpat = OPatTuple { pats = pvars } in
      let binds =
        mapi
          (lam i. lam n : (Name, Type).
            match n with (ident, ty) in
            let sid = stringToSid (int2string i) in
            let ty = get tys i in
            let var = TmVar {
              ident = ident,
              ty = ty,
              info = info,
              frozen = false} in
            (sid, _ocamlToMExpr env (None ()) var ty))
          (zip ns tys) in
      let record = TmRecord {
        bindings = mapFromSeq cmpSID binds,
        ty = ty,
        info = info} in
      let t = OTmConApp {ident = id, args = [record]} in
      OTmMatch {target = expr, arms = [(tpat, t)]}
  | TySeq {info = info, ty = ty} ->
    let op = OTmVarExt {ident = intrinsicOpSeq "Helpers.of_array_copy"} in
    let mapop = OTmVarExt {ident = "Array.map"} in
    let ident = nameSym "x" in
    let var = TmVar {
      ident = ident,
      ty = TyUnknown {info = info},
      info = info,
      frozen = false} in
    let body = _ocamlToMExpr env (None ()) var ty in
    TmApp {
      lhs = op,
      rhs = TmApp {
        lhs = TmApp {
          lhs = mapop,
          rhs = TmLam {
            ident = ident,
            tyIdent = TyUnknown {info = info},
            body = body,
            ty = TyUnknown {info = info},
            info = info},
          ty = TyUnknown {info = info},
          info = info},
        rhs = expr,
        ty = TyUnknown {info = info},
        info = info},
      ty = TyUnknown {info = info},
      info = info}
  | ty & (TyTensor {info = info, ty = TyInt _ | TyFloat _}) ->
    let lhs = OTmVarExt {ident = intrinsicOpTensor "Helpers.of_genarray_clayout"} in
    TmApp {lhs = lhs, rhs = expr, ty = ty, info = info}
  | TyTensor {info = info, ty = _} ->
    infoErrorExit info "CUDA compiler can only convert tensors of ints or floats"
  | TyVariant {info = info, constrs = constrs} ->
    infoErrorExit info "Conversion not implemented yet"
  | TyInt _ | TyFloat _ | TyChar _ | TyBool _ -> expr
  | ty -> infoErrorExit (infoTy ty) "CUDA compiler cannot convert MExpr type"
end

lang PMExprReplaceAccelerate =
  PMExprConvertMExprToOCaml + PMExprConvertOCamlToMExpr

  sem _constructReplaceAccelerateEnv : AssocSeq Name Type -> GenerateEnv
                                    -> ReplaceAccelerateEnv
  sem _constructReplaceAccelerateEnv typeLiftEnv =
  | generateEnv -> {typeLiftEnv = typeLiftEnv, generateEnv = generateEnv}

  sem _tensorToOCamlType =
  | TyTensor {ty = ty & (TyInt _ | TyFloat _), info = info} ->
    let layout = OTyBigarrayClayout {info = info} in
    let elemType =
      match ty with TyInt _ then OTyBigarrayIntElt {info = info}
      else OTyBigarrayFloat64Elt {info = info} in
    OTyBigarrayGenarray {info = info, tys = [ty, elemType, layout]}
  | TyTensor t ->
    infoErrorExit t.info "Cannot convert tensor of unsupported type"

  sem wrapInConvertData : ReplaceAccelerateEnv -> Expr -> Expr
  sem wrapInConvertData env =
  | t ->
    let ty = tyTm t in
    _mexprToOCaml env (None ()) t ty

  sem convertAccelerateParameters : ReplaceAccelerateEnv -> Expr -> Expr
  sem convertAccelerateParameters env =
  | TmApp t ->
    let lhs = convertAccelerateParameters env t.lhs in
    let rhs = wrapInConvertData env t.rhs in
    TmApp {{t with lhs = convertAccelerateParameters env t.lhs} 
              with rhs = wrapInConvertData env t.rhs}
  | t -> t

  sem convertAccelerate : ReplaceAccelerateEnv -> Expr -> Expr
  sem convertAccelerate env =
  | expr ->
    let expr = convertAccelerateParameters env expr in
    let ty = tyTm expr in
    let expr = _ocamlToMExpr env (None ()) expr ty in
    expr

  sem replaceAccelerateH : Map Name AccelerateData -> ReplaceAccelerateEnv
                        -> Expr -> Expr
  sem replaceAccelerateH accelerated env =
  | t & (TmApp {lhs = lhs, ty = appTy}) ->
    let appArgs = collectAppArguments t in
    match appArgs with (TmVar {ident = id}, args) then
      if mapMem id accelerated then
        -- NOTE(larshum, 2021-09-17): Remove the dummy parameter if it is not
        -- the only parameter.
        match args with _ ++ [TmConst {val = CInt {val = 0}}] then
          let lhs = withType appTy lhs in
          convertAccelerate env lhs
        else convertAccelerate env t
      else t
    else t
  | TmLet t ->
    if mapMem t.ident accelerated then
      replaceAccelerateH accelerated env t.inexpr
    else
      TmLet {{t with body = replaceAccelerateH accelerated env t.body}
                with inexpr = replaceAccelerateH accelerated env t.inexpr}
  | TmRecLets t ->
    let replaceAccelerateBindings : RecLetBinding -> Option RecLetBinding =
      lam bind.
      if mapMem bind.ident accelerated then None ()
      else Some {bind with body = replaceAccelerateH accelerated env bind.body}
    in
    let bindings = mapOption replaceAccelerateBindings t.bindings in
    TmRecLets {{t with bindings = mapOption replaceAccelerateBindings t.bindings}
                  with inexpr = replaceAccelerateH accelerated env t.inexpr}
  | t -> smap_Expr_Expr (replaceAccelerateH accelerated env) t

  -- We replace the auxilliary acceleration terms in the AST, by removing any
  -- let-expressions involving an accelerate term and updates calls to such
  -- terms to properly convert types of parameters and the return value.
  --
  -- The result is a list of OCaml record definitions, needed to handle the
  -- data conversion of record types, and an AST.
  sem replaceAccelerate : Map Name AccelerateData -> AssocSeq Name Type
                       -> GenerateEnv -> Expr -> Expr
  sem replaceAccelerate accelerated typeLiftEnv generateEnv =
  | t ->
    let env = _constructReplaceAccelerateEnv typeLiftEnv generateEnv in
    replaceAccelerateH accelerated env t
end
