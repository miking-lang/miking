-- Annotates AST nodes in an MExpr program with types. When the exact type of
-- a term cannot be determined, for example when the then- and else-branch of a
-- match have different (known) types, the AST node is annotated with
-- `TyUnknown` instead of resulting in an error. When the actual type is found
-- to be incompatible with an annotated type, an error is reported.
--
-- Intrinsic functions are annotated with as much detail as possible given the
-- existing type AST nodes.
--
-- Requires that the types of constructors are included in the `tyIdent` field.
include "assoc-seq.mc"
include "ast.mc"
include "const-types.mc"
include "eq.mc"
include "pprint.mc"
include "builtin.mc"
include "type.mc"

type TypeEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  tyEnv : Map Name Type
}

let _typeEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyEnv  = mapFromSeq nameCmp (
    map (lam t : (String, [String]). (nameNoSym t.0, tyvariant_ [])) builtinTypes
  )
}

let _pprintType = use MExprPrettyPrint in
  lam ty.
  match getTypeStringCode 0 pprintEnvEmpty ty with (_,tyStr) then
    tyStr
  else never

------------------------
-- TYPE COMPATIBILITY --
------------------------

lang CompatibleType =

  -- NOTE(dlunde,2021-05-05): Part of below hack
  AppTypeAst

  -- Given two types that are possibly unknown, this function attempts to find
  -- a type that is compatible with both given types in the given type
  -- environment.  It is equivalent to type equality, except that unknown types
  -- are considered compatible with any other type. If no compatible type can
  -- be found, `None` is returned.
  sem compatibleType (tyEnv : Map Name Type) (ty1: Type) =
  | ty2 ->
    let ty1 = reduceTyVar ty1 in
    let ty2 = reduceTyVar ty2 in
    match compatibleTypeBase tyEnv (ty1, ty2) with Some ty then Some ty

    -- NOTE(dlunde,2021-05-05): Temporary hack to make sure that tyapps are
    -- reduced before tyvars. Not sure why this is needed, but it should not
    -- matter in the end when we have a proper type system.
    else match ty1 with TyApp t1 then
      compatibleType tyEnv t1.lhs ty2
    else match ty2 with TyApp t2 then
      compatibleType tyEnv ty1 t2.lhs
    --------

    else match reduceType tyEnv ty1 with Some ty1 then
      compatibleType tyEnv ty1 ty2
    else match reduceType tyEnv ty2 with Some ty2 then
      compatibleType tyEnv ty1 ty2
    else None ()

  sem compatibleTypeBase (tyEnv: Map Name Type) =
  | _ -> None () -- Types are not compatible by default

  sem reduceType (tyEnv: Map Name Type) =
  | _ -> None () -- Types cannot be reduced by default

  -- NOTE(aathn,2021-10-27): We convert type variables to TyUnknown using this
  -- semantic function as a temporary solution to enable typeCheck and typeAnnot
  -- to be used in tandem.
  sem reduceTyVar =
  | ty -> ty
end

lang UnknownCompatibleType = CompatibleType + UnknownTypeAst

  sem compatibleTypeBase (tyEnv: Map Name Type) =
  | (TyUnknown _ & ty1, TyUnknown _) -> Some ty1
  | (TyUnknown _, ! TyUnknown _ & ty2) -> Some ty2
  | (! TyUnknown _ & ty1, TyUnknown _) -> Some ty1

end

lang ConCompatibleType = CompatibleType + ConTypeAst

  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyCon t1 & ty1, TyCon t2) ->
    if nameEq t1.ident t2.ident then Some ty1 else None ()

  sem reduceType (tyEnv : Map Name Type) =
  | TyCon {info = info, ident = id} ->
    match mapLookup id tyEnv with Some ty then Some ty else
      errorSingle [info] (concat "Unbound TyCon in reduceType: " (nameGetStr id))

end

lang VarCompatibleType = CompatibleType + VarTypeAst + UnknownTypeAst
  sem reduceTyVar =
  | TyVar {info = i} -> TyUnknown {info = i}
end

lang AllCompatibleType = CompatibleType + AllTypeAst
  sem reduceType (tyEnv : Map Name Type) =
  | TyAll t -> Some t.ty
end

lang AppCompatibleType = CompatibleType + AppTypeAst

  sem compatibleTypeBase (tyEnv : Map Name Type) =
  -- TODO(dlunde,2021-05-05): Left out for now for compatibility with original
  -- compatibleTypes

  -- NOTE(dlunde,2021-05-05): This is NOT how we want to handle TmApp in the
  -- end. We are now just discarding the RHS of all applications
  sem reduceType (tyEnv : Map Name Type) =
  | TyApp t -> Some t.lhs

end

lang BoolCompatibleType = CompatibleType + BoolTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyBool _ & t1, TyBool _) -> Some t1
end

lang IntCompatibleType = CompatibleType + IntTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyInt _ & t1, TyInt _) -> Some t1
end

lang FloatCompatibleType = CompatibleType + FloatTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyFloat _ & t1, TyFloat _) -> Some t1
end

lang CharCompatibleType = CompatibleType + CharTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyChar _ & t1, TyChar _) -> Some t1
end

lang FunCompatibleType = CompatibleType + FunTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyArrow t1, TyArrow t2) ->
    match compatibleType tyEnv t1.from t2.from with Some a then
      match compatibleType tyEnv t1.to t2.to with Some b then
        Some (TyArrow {{t1 with from = a} with to = b})
      else None ()
    else None ()
end

lang SeqCompatibleType = CompatibleType + SeqTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TySeq t1, TySeq t2) ->
    match compatibleType tyEnv t1.ty t2.ty with Some t then
      Some (TySeq {t1 with ty = t})
    else None ()
end

lang TensorCompatibleType = CompatibleType + TensorTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyTensor t1, TyTensor t2) ->
    match compatibleType tyEnv t1.ty t2.ty with Some t then
      Some (TyTensor {t1 with ty = t})
    else None ()
end

lang RecordCompatibleType = CompatibleType + RecordTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyRecord t1, TyRecord t2) ->
    let f = lam acc. lam p.
      match p with (k, ty1) then
        match mapLookup k t2.fields with Some ty2 then
          match compatibleType tyEnv ty1 ty2 with Some ty then
            Some (mapInsert k ty acc)
          else None ()
        else None ()
      else never
    in
    match optionFoldlM f (mapEmpty cmpSID) (mapBindings t1.fields)
    with Some fields then Some (TyRecord {t1 with fields = fields})
    else None ()
end

lang VariantCompatibleType = CompatibleType + VariantTypeAst
  sem compatibleTypeBase (tyEnv : Map Name Type) =
  | (TyVariant t1, TyVariant t2) ->
    let constrsOpt = mapFoldlOption (lam acc. lam ident. lam ty1.
      match mapLookup ident t2.constrs with Some ty2 then
        match compatibleType tyEnv ty1 ty2 with Some ty then
          Some (mapInsert ident ty acc)
        else None ()
      else None ()
    ) (mapEmpty (mapGetCmpFun t1.constrs)) t1.constrs
    in
    optionMap (lam constrs. TyVariant {t1 with constrs = constrs}) constrsOpt

end


-------------------
-- TYPE ANNOTATE --
-------------------

lang TypeAnnot = CompatibleType
  sem typeAnnotExpr (env : TypeEnv) =
  -- Intentionally left blank

  sem typeAnnot =
  | expr ->
    let env = _typeEnvEmpty in
    typeAnnotExpr env expr
end

lang VarTypeAnnot = TypeAnnot + VarAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmVar t ->
    let ty =
      match env with {varEnv = varEnv, tyEnv = tyEnv} then
        match mapLookup t.ident varEnv with Some ty then
          match compatibleType tyEnv t.ty ty with Some ty then
            ty
          else
            let msg = join [
              "Type of variable is inconsistent with environment\n",
              "Variable annotated with type: ", _pprintType t.ty, "\n",
              "Type in variable environment: ", _pprintType ty
            ] in
            errorSingle [t.info] msg
        else t.ty
      else never
    in
    TmVar {t with ty = ty}

end

lang AppTypeAnnot = TypeAnnot + AppAst + FunTypeAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmApp t ->
    let lhs = typeAnnotExpr env t.lhs in
    let rhs = typeAnnotExpr env t.rhs in
    let ty =
      match (tyTm lhs, tyTm rhs) with (TyArrow {from = from, to = to}, ty) then
        match compatibleType env.tyEnv from ty with Some _ then
          to
        else (ityunknown_ t.info)
      else (ityunknown_ t.info)
    in
    TmApp {{{t with lhs = lhs}
               with rhs = rhs}
               with ty = ty}
end

lang LamTypeAnnot = TypeAnnot + LamAst + FunTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmLam t ->
    match env with {varEnv = varEnv} then
      let env = {env with varEnv = mapInsert t.ident t.tyAnnot varEnv} in
      let body = typeAnnotExpr env t.body in
      let ty = ityarrow_ t.info t.tyAnnot (tyTm body) in
      TmLam {{t with body = body}
                with ty = ty}
    else never
end

lang TypePropagation = TypeAnnot
  sem propagateExpectedType (tyEnv : Map Name Type) =
  | (_, t) -> t
end

lang LetTypeAnnot = TypeAnnot + TypePropagation + LetAst +  UnknownTypeAst + AllTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmLet t ->
    match env with {varEnv = varEnv, tyEnv = tyEnv} then
      let body = match t.tyAnnot with TyUnknown _ then t.body else
        match stripTyAll t.tyAnnot with (_, tyAnnot) in
        propagateExpectedType tyEnv (tyAnnot, t.body) in
      let body = typeAnnotExpr env body in
      match compatibleType tyEnv t.tyAnnot (tyTm body) with Some tyBody then
        let env = {env with varEnv = mapInsert t.ident tyBody varEnv} in
        let inexpr = typeAnnotExpr env t.inexpr in
        TmLet {t with tyAnnot = tyBody,
                      tyBody = tyBody,
                      body = withType tyBody body,
                      inexpr = inexpr,
                      ty = tyTm inexpr}
      else
        let msg = join [
          "Inconsistent type annotation of let-expression\n",
          "Expected type: ", _pprintType (tyTm body), "\n",
          "Annotated type: ", _pprintType t.tyAnnot
        ] in
        errorSingle [t.info] msg
    else never
end

lang PropagateLetType = TypePropagation + LetAst
  sem propagateExpectedType (tyEnv : Map Name Type) =
  | (ty, TmLet t) -> TmLet {t with inexpr = propagateExpectedType tyEnv (ty, t.inexpr)}
end

lang PropagateRecLetsType = TypePropagation + RecLetsAst
  sem propagateExpectedType (tyEnv : Map Name Type) =
  | (ty, TmRecLets t) -> TmRecLets {t with inexpr = propagateExpectedType tyEnv (ty, t.inexpr)}
end

lang PropagateArrowLambda = TypePropagation + FunTypeAst + LamAst
  sem propagateExpectedType (tyEnv : Map Name Type) =
  | (TyArrow {from = from, to = to}, TmLam t) ->
    match compatibleType tyEnv from t.tyAnnot with Some ty then
      TmLam {t with tyAnnot = ty,
                    tyIdent = ty,
                    body = propagateExpectedType tyEnv (to, t.body)}
    else
      let msg = join [
        "Inconsistent type annotation of let-expression and lambda\n",
        "Type from let: ", _pprintType from, "\n",
        "Type from lambda: ", _pprintType t.tyAnnot
      ] in
      errorSingle [t.info] msg
end

lang ExpTypeAnnot = TypeAnnot + ExtAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmExt t ->
    match env with {varEnv = varEnv, tyEnv = tyEnv} then
      let env = {env with varEnv = mapInsert t.ident t.tyIdent varEnv} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmExt {{t with inexpr = inexpr}
                with ty = tyTm inexpr}
    else never
end

lang RecLetsTypeAnnot = TypeAnnot + TypePropagation + RecLetsAst + LamAst + UnknownTypeAst + AllTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecLets t ->
    -- Add mapping from binding identifier to annotated type before doing type
    -- annotations of the bindings. This is to make annotations work for
    -- mutually recursive functions, given correct type annotations.
    let foldBindingInit = lam acc. lam binding : RecLetBinding.
      mapInsert binding.ident binding.tyAnnot acc
    in
    -- Add mapping from binding identifier to the inferred type.
    let foldBindingAfter = lam acc. lam binding : RecLetBinding.
      mapInsert binding.ident binding.tyAnnot acc
    in
    let annotBinding = lam env : TypeEnv. lam binding : RecLetBinding.
      let body = match binding.tyAnnot with TyUnknown _ then binding.body else
        match stripTyAll binding.tyAnnot with (_, tyAnnot) in
        propagateExpectedType env.tyEnv (tyAnnot, binding.body) in
      let body = typeAnnotExpr env body in
      match env with {tyEnv = tyEnv} then
        let tyBody =
          match compatibleType tyEnv binding.tyAnnot (tyTm body) with Some tyBody then
            tyBody
          else
            let msg = join [
              "Inconsistent type annotation of recursive let-expression\n",
              "Expected type: ", _pprintType (tyTm body), "\n",
              "Annotated type: ", _pprintType binding.tyAnnot
            ] in
            errorSingle [t.info] msg
        in
        {binding with body = body,
                      tyAnnot = tyBody,
                      tyBody = tyBody}
      else never
    in
    match env with {varEnv = varEnv} then
      let env = {env with varEnv = foldl foldBindingInit varEnv t.bindings} in
      let bindings = map (annotBinding env) t.bindings in
      let env = {env with varEnv = foldl foldBindingAfter varEnv bindings} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmRecLets {{{t with bindings = bindings}
                     with inexpr = inexpr}
                     with ty = tyTm inexpr}
    else never
end

lang ConstTypeAnnot = TypeAnnot + MExprConstType + AllTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    match stripTyAll (f (tyConst t.val)) with (_, ty) then
      TmConst {t with ty = ty}
    else never
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let tms = map (typeAnnotExpr env) t.tms in
    let elemTy =
      if eqi (length tms) 0 then ityunknown_ t.info
      else
        let types = map (lam term. tyTm term) tms in
        match optionFoldlM (compatibleType env.tyEnv) (ityunknown_ t.info) types
        with Some ty then
          ty
        else (ityunknown_ t.info)
    in
    TmSeq {{t with tms = tms}
              with ty = ityseq_ t.info elemTy}
end

lang RecordTypeAnnot = TypeAnnot + RecordAst + RecordTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecord t ->
    let bindings = mapMap (typeAnnotExpr env) t.bindings in
    let bindingTypes = mapMap tyTm bindings in
    let ty = TyRecord {fields = bindingTypes, info = t.info} in
    TmRecord {{t with bindings = bindings}
                 with ty = ty}
  | TmRecordUpdate t ->
    let rec = typeAnnotExpr env t.rec in
    let value = typeAnnotExpr env t.value in
    TmRecordUpdate {{{t with rec = rec}
                        with value = value}
                        with ty = tyTm rec}
end

lang TypeTypeAnnot = TypeAnnot + TypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmType t ->
    let tyEnv = mapInsert t.ident t.tyIdent env.tyEnv in
    let inexpr = typeAnnotExpr {env with tyEnv = tyEnv} t.inexpr in
    TmType {{t with inexpr = inexpr}
               with ty = tyTm inexpr}
end

lang DataTypeAnnot = TypeAnnot + DataAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmConDef t ->
    match env with {conEnv = conEnv} then
      let env = {env with conEnv = mapInsert t.ident t.tyIdent conEnv} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmConDef {{t with inexpr = inexpr}
                   with ty = tyTm inexpr}
    else never
  | TmConApp t ->
    let body = typeAnnotExpr env t.body in
    match env with {conEnv = conEnv, tyEnv = tyEnv} then
      let ty =
        match mapLookup t.ident conEnv with Some lty then
          match stripTyAll lty with (_, TyArrow {from = from, to = to}) then
            recursive let tyvar = lam ty.
              match ty with TyCon _ then ty
              else match ty with TyApp t then tyvar t.lhs
              else (ityunknown_ t.info)
            in
            match compatibleType tyEnv (tyTm body) from with Some _ then
              tyvar to
            else
              let msg = join [
                "Inconsistent types of constructor application. ",
                "Constructor expected argument of type ", _pprintType from,
                ", but the actual type was ", _pprintType (tyTm body)
              ] in
              errorSingle [t.info] msg
          else (ityunknown_ t.info)
        else
          let msg = join ["Application of untyped constructor: ",
                          nameGetStr t.ident] in
          errorSingle [t.info] msg
      in
      TmConApp {{t with body = body}
                   with ty = ty}
    else never
end

lang MatchTypeAnnot = TypeAnnot + MatchAst + MExprEq
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  -- Intentionally left blank

  sem typeAnnotExpr (env : TypeEnv) =
  | TmMatch t ->
    let target = typeAnnotExpr env t.target in
    match typeAnnotPat env (tyTm target) t.pat with (thnEnv, pat) then
      let thn = typeAnnotExpr thnEnv t.thn in
      let els = typeAnnotExpr env t.els in
      let ty =
        match compatibleType env.tyEnv (tyTm thn) (tyTm els) with Some ty
        then ty
        else (ityunknown_ t.info) in
      TmMatch {{{{{t with target = target}
                     with thn = thn}
                     with els = els}
                     with ty = ty}
                     with pat = pat}
    else never
end

lang UtestTypeAnnot = TypeAnnot + UtestAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmUtest t ->
    let test = typeAnnotExpr env t.test in
    let expected = typeAnnotExpr env t.expected in
    let next = typeAnnotExpr env t.next in
    let tusing = optionMap (typeAnnotExpr env) t.tusing in
    match tusing with Some tu then
      match tyTm tu with
        TyArrow (ta1 & {from = lty,
                        to = TyArrow (ta2 & {from = rty, to = TyBool _})}) then
        match compatibleType env.tyEnv (tyTm test) lty with Some lty then
          match compatibleType env.tyEnv (tyTm expected) rty with Some rty then
            let arrowTy = TyArrow {{ta1 with from = lty}
                                        with to = TyArrow {ta2 with from = rty}} in
            TmUtest {{{{{t with test = withType lty test}
                           with expected = withType rty expected}
                           with next = next}
                           with tusing = Some (withType arrowTy tu)}
                           with ty = tyTm next}
          else
            let msg = join [
              "Custom equality function expected right-hand side of type ",
              _pprintType rty, ", got argument of incompatible type ",
              _pprintType (tyTm expected)
            ] in
            errorSingle [t.info] msg
        else
          let msg = join [
            "Custom equality function expected left-hand side of type ",
            _pprintType lty, ", got argument of incompatible type ",
            _pprintType (tyTm test)
          ] in
          errorSingle [t.info] msg
      else
        let msg = join [
          "Equality function was found to have incorrect type.\n",
          "Type was inferred to be ", _pprintType (tyTm tu)
        ] in
        errorSingle [t.info] msg
    else match compatibleType env.tyEnv (tyTm test) (tyTm expected) with Some eTy then
      TmUtest {{{{t with test = withType eTy test}
                    with expected = withType eTy expected}
                    with next = next}
                    with ty = tyTm next}
    else
      let msg = join [
        "Arguments to utest have incompatible types\n",
        "LHS: ", _pprintType (tyTm test), "\nRHS: ", _pprintType (tyTm expected)
      ] in
      errorSingle [t.info] msg
end

lang NeverTypeAnnot = TypeAnnot + NeverAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmNever t -> TmNever {t with ty = (ityunknown_ t.info)}
end


---------------------------
-- PATTERN TYPE ANNOTATE --
---------------------------

lang NamedPatTypeAnnot = TypeAnnot + NamedPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatNamed t ->
    let env =
      match t.ident with PName n then
        {env with varEnv = mapInsert n expectedTy env.varEnv}
      else env in
    (env, PatNamed {t with ty = expectedTy})
end

lang SeqTotPatTypeAnnot = TypeAnnot + SeqTotPat + UnknownTypeAst + SeqTypeAst
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatSeqTot t ->
    let elemTy =
      match expectedTy with TySeq {ty = elemTy} then elemTy
      else ityunknown_ t.info
    in
    match mapAccumL (lam acc. lam pat. typeAnnotPat acc elemTy pat) env t.pats with (env, pats) then
      (env, PatSeqTot {{t with pats = pats} with ty = tyseq_ elemTy})
    else never
end

lang SeqEdgePatTypeAnnot = TypeAnnot + SeqEdgePat + UnknownTypeAst + SeqTypeAst
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatSeqEdge t ->
    let elemTy =
      match expectedTy with TySeq {ty = elemTy} then elemTy
      else ityunknown_ t.info in
    let expectedTy = match expectedTy with TySeq _
      then expectedTy
      else tyseq_ elemTy in
    match mapAccumL (lam acc. lam pat. typeAnnotPat acc elemTy pat) env t.prefix with (env, prefix) then
      let env: TypeEnv = env in
      let env: TypeEnv =
        match t.middle with PName n then
          {env with varEnv = mapInsert n expectedTy env.varEnv}
        else env
      in
      match mapAccumL (lam acc. lam pat. typeAnnotPat acc elemTy pat) env t.postfix with (env, postfix) then
        (env, PatSeqEdge {{{t with prefix = prefix} with postfix = postfix} with ty = expectedTy})
      else never
    else never
end

lang RecordPatTypeAnnot = TypeAnnot + RecordPat + UnknownTypeAst + RecordTypeAst
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatRecord t ->
    let expectedTy = typeUnwrapAlias env.tyEnv expectedTy in
    let expectedTy = match expectedTy with TyUnknown _ | TyApp {lhs = TyUnknown _} then t.ty else expectedTy in
    let expectedTy = match expectedTy with TyRecord _ then expectedTy else
      match (record2tuple t.bindings, mapLength t.bindings) with (Some _, length & !1) then
        -- NOTE(vipa, 2021-05-26): This looks like a tuple pattern, so
        -- we assume that the type is exactly that tuple type. This is
        -- technically a hack, and so has some cases where it breaks
        -- things, but in the common case it is fine. Once we have
        -- exact record patterns, and tuple patterns desugar to that,
        -- this can be removed.
        tytuple_ (make length tyunknown_)
      else expectedTy
    in
    let lookup =
      match expectedTy with TyRecord {fields = fields} then
        lam field. optionGetOr (ityunknown_ t.info) (mapLookup field fields)
      else
        lam. ityunknown_ t.info
    in
    let annotField = lam env. lam field. lam pat.
      typeAnnotPat env (lookup field) pat in
    match mapMapAccum annotField env t.bindings with (env, bindings) then
      (env, PatRecord {{t with bindings = bindings} with ty = expectedTy})
    else never
end

lang DataPatTypeAnnot = TypeAnnot + DataPat + VariantTypeAst + ConTypeAst +
                        FunTypeAst + AllTypeAst
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatCon t ->
    match optionMap stripTyAll (mapLookup t.ident env.conEnv)
    with Some (_, TyArrow {from = argTy, to = to}) then
      match typeAnnotPat env argTy t.subpat with (env, subpat) then
        (env, PatCon {{t with subpat = subpat} with ty = to})
      else never
    else (env, PatCon t)
end

lang IntPatTypeAnnot = TypeAnnot + IntPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatInt r -> (env, PatInt {r with ty = tyint_})
end

lang CharPatTypeAnnot = TypeAnnot + CharPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatChar r -> (env, PatChar {r with ty = tychar_})
end

lang BoolPatTypeAnnot = TypeAnnot + BoolPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatBool r -> (env, PatBool {r with ty = tybool_})
end

lang AndPatTypeAnnot = TypeAnnot + AndPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatAnd t ->
    match typeAnnotPat env expectedTy t.lpat with (env, lpat) then
      match typeAnnotPat env expectedTy t.rpat with (env, rpat) then
        (env, PatAnd {{{t with lpat = lpat} with rpat = rpat} with ty = expectedTy})
      else never
    else never
end

lang OrPatTypeAnnot = TypeAnnot + OrPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatOr t ->
    match typeAnnotPat env expectedTy t.lpat with (env, lpat) then
      match typeAnnotPat env expectedTy t.rpat with (env, rpat) then
        (env, PatOr {{{t with lpat = lpat} with rpat = rpat} with ty = expectedTy})
      else never
    else never
end

lang NotPatTypeAnnot = TypeAnnot + NotPat
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatNot t ->
    match typeAnnotPat env expectedTy t.subpat with (env, subpat) then
      (env, PatNot {{t with subpat = subpat} with ty = expectedTy})
    else never
end

lang MExprTypeAnnot =

  -- Type compatibility
  UnknownCompatibleType + ConCompatibleType + BoolCompatibleType +
  IntCompatibleType + FloatCompatibleType + CharCompatibleType +
  FunCompatibleType + SeqCompatibleType + TensorCompatibleType +
  RecordCompatibleType + VariantCompatibleType + AppCompatibleType +
  PropagateArrowLambda + PropagateLetType + VarCompatibleType +
  AllCompatibleType +

  -- Terms
  VarTypeAnnot + AppTypeAnnot + LamTypeAnnot + RecordTypeAnnot + LetTypeAnnot +
  TypeTypeAnnot + RecLetsTypeAnnot + ConstTypeAnnot + DataTypeAnnot +
  MatchTypeAnnot + UtestTypeAnnot + SeqTypeAnnot + NeverTypeAnnot +
  ExpTypeAnnot +

  -- Patterns
  NamedPatTypeAnnot + SeqTotPatTypeAnnot + SeqEdgePatTypeAnnot +
  RecordPatTypeAnnot + DataPatTypeAnnot + IntPatTypeAnnot + CharPatTypeAnnot +
  BoolPatTypeAnnot + AndPatTypeAnnot + OrPatTypeAnnot + NotPatTypeAnnot

end

lang TestLang = MExprTypeAnnot + MExprPrettyPrint + MExprEq
end

mexpr

use TestLang in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let n = nameSym "n" in

let appConst = addi_ (int_ 5) (int_ 2) in
utest tyTm (typeAnnot appConst) with tyint_ using eqType in

let variableType = tyarrow_ tyint_ tybool_ in
let appVariable = app_ (withType variableType (nvar_ x)) (int_ 0) in
utest tyTm (typeAnnot appVariable) with tybool_ using eqType in

let partialAppConst = nlam_ x tyint_ (addi_ (int_ 5) (nvar_ x)) in
utest tyTm (typeAnnot partialAppConst)
with  tyarrow_ tyint_ tyint_
using eqType in

let badApp = bindall_ [
  nulet_ x (int_ 5),
  app_ (nvar_ x) (float_ 3.14)
] in
utest tyTm (typeAnnot badApp) with tyunknown_ using eqType in

let lamConstantReturnType = nulam_ x (int_ 0) in
utest tyTm (typeAnnot lamConstantReturnType)
with  tyarrow_ tyunknown_ tyint_
using eqType in

let letAscription = bind_ (nlet_ x tyint_ (nvar_ y)) (nvar_ x) in
utest tyTm (typeAnnot letAscription) with tyint_ using eqType in

let recLets = typeAnnot (bindall_ [
  nreclets_ [
    (x, tyarrow_ tyunit_ tyint_, nlam_ n tyunit_ (app_ (nvar_ y) uunit_)),
    (y, tyunknown_, nlam_ n tyunit_ (app_ (nvar_ x) uunit_)),
    (z, tyunknown_, nlam_ n tyunit_ (addi_ (app_ (nvar_ y) uunit_) (int_ 1)))
  ],
  uunit_
]) in
utest tyTm recLets with tyunit_ using eqType in

(match recLets with TmRecLets {bindings = bindings} then
  let b0 : RecLetBinding = get bindings 0 in
  let b1 : RecLetBinding = get bindings 1 in
  let b2 : RecLetBinding = get bindings 2 in
  let xTy = tyarrow_ tyunit_ tyint_ in
  let yTy = tyarrow_ tyunit_ tyint_ in
  let zTy = tyarrow_ tyunit_ tyint_ in
  utest b0.tyBody with xTy using eqType in
  utest b1.tyBody with yTy using eqType in
  utest b2.tyBody with zTy using eqType in
  ()
else never);

utest tyTm (typeAnnot (int_ 4)) with tyint_ using eqType in
utest tyTm (typeAnnot (char_ 'c')) with tychar_ using eqType in
utest tyTm (typeAnnot (float_ 1.2)) with tyfloat_ using eqType in
utest tyTm (typeAnnot true_) with tybool_ using eqType in

let emptySeq = typeAnnot (seq_ []) in
utest tyTm emptySeq with tyseq_ tyunknown_ using eqType in

let intSeq = typeAnnot (seq_ [int_ 1, int_ 2, int_ 3]) in
utest tyTm intSeq with tyseq_ tyint_ using eqType in

let intMatrix = typeAnnot (seq_ [seq_ [int_ 1, int_ 2],
                                 seq_ [int_ 3, int_ 4]]) in
utest tyTm intMatrix with tyseq_ (tyseq_ tyint_) using eqType in

let unknownSeq = typeAnnot (seq_ [nvar_ x, nvar_ y]) in
utest tyTm unknownSeq with tyseq_ tyunknown_ using eqType in

let emptyRecord = typeAnnot uunit_ in
utest tyTm emptyRecord with tyunit_ using eqType in

let record = typeAnnot (urecord_ [
  ("a", int_ 0), ("b", float_ 2.718), ("c", urecord_ []),
  ("d", urecord_ [
    ("e", seq_ [int_ 1, int_ 2]),
    ("f", urecord_ [
      ("x", nvar_ x), ("y", nvar_ y), ("z", nvar_ z)
    ])
  ])
]) in
let expectedRecordType = tyrecord_ [
  ("a", tyint_), ("b", tyfloat_), ("c", tyunit_),
  ("d", tyrecord_ [
    ("e", tyseq_ tyint_),
    ("f", tyrecord_ [
      ("x", tyunknown_), ("y", tyunknown_), ("z", tyunknown_)
    ])
  ])
] in
utest tyTm record with expectedRecordType using eqType in
let recordUpdate = typeAnnot (recordupdate_ record "x" (int_ 1)) in
utest tyTm recordUpdate with expectedRecordType using eqType in

let typeDecl = bind_ (ntype_ n tyunknown_) uunit_ in
utest tyTm (typeAnnot typeDecl) with tyunit_ using eqType in

let conApp = bindall_ [
  ntype_ n tyunknown_,
  ncondef_ x (tyarrow_ tyint_ (ntycon_ n)),
  nconapp_ x (int_ 4)
] in
utest tyTm (typeAnnot conApp) with ntycon_ n using eqType in

let matchInteger = typeAnnot (bindall_ [
  nulet_ x (int_ 0),
  match_ (nvar_ x) (pint_ 0) (nvar_ x) (addi_ (nvar_ x) (int_ 1))
]) in
utest tyTm matchInteger with tyint_ using eqType in
(match matchInteger with TmLet {inexpr = TmMatch t} then
  utest tyTm t.target with tyint_ using eqType in
  utest tyTm t.thn with tyint_ using eqType in
  utest tyTm t.els with tyint_ using eqType in
  ()
else never);

let matchDistinct = typeAnnot (
  match_ (int_ 0) (npvar_ n) (int_ 0) (char_ '1')
) in
utest tyTm matchDistinct with tyunknown_ using eqType in
(match matchDistinct with TmMatch t then
  utest tyTm t.target with tyint_ using eqType in
  utest tyTm t.thn with tyint_ using eqType in
  utest tyTm t.els with tychar_ using eqType in
  ()
else never);

let utestAnnot = typeAnnot (
  utest_ (int_ 0) (int_ 1) (char_ 'c')
) in
utest tyTm utestAnnot with tychar_ using eqType in
(match utestAnnot with TmUtest t then
  utest tyTm t.test with tyint_ using eqType in
  utest tyTm t.expected with tyint_ using eqType in
  utest tyTm t.next with tychar_ using eqType in
  ()
else never);

utest tyTm (typeAnnot never_) with tyunknown_ using eqType in

-- Test that types are propagated through patterns in match expressions
let matchSeq = bindall_ [
  match_ (seq_ [str_ "a", str_ "b", str_ "c", str_ "d"])
    (pseqedge_ [pseqtot_ [pchar_ 'a']] "mid" [pseqtot_ [pchar_ 'd']])
    (var_ "mid")
    never_
] in
utest tyTm (typeAnnot (symbolize matchSeq)) with tyseq_ tystr_ using eqType in

let matchTree = bindall_ [
  type_ "Tree" tyunknown_,
  condef_ "Branch" (tyarrow_ (tytuple_ [tycon_ "Tree", tycon_ "Tree"]) (tycon_ "Tree")),
  condef_ "Leaf" (tyarrow_ (tyseq_ tyint_) (tycon_ "Tree")),
  ulet_ "t" (conapp_ "Branch" (utuple_ [
    conapp_ "Leaf" (seq_ [int_ 1, int_ 2, int_ 3]),
    conapp_ "Branch" (utuple_ [
      conapp_ "Leaf" (seq_ [int_ 2]),
      conapp_ "Leaf" (seq_ [])])])),
  (match_ (var_ "t")
    (pcon_ "Branch" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]))
    (match_ (var_ "lhs")
      (pcon_ "Leaf" (pvar_ "n"))
      (var_ "n")
      never_)
    never_)
] in
utest tyTm (typeAnnot (symbolize matchTree)) with tyseq_ tyint_ using eqType in

()
