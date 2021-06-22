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
include "mexpr/type.mc"

type TypeEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  tyEnv : Map Name Type
}

let _typeEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyEnv  = mapEmpty nameCmp
}

let _isTypeAscription = use MExprAst in
  lam letTerm : {ident : Name, tyBody : Type, body : Expr,
                 inexpr : Expr, ty : Type, info : Info}.
  match letTerm.inexpr with TmVar {ident = id} then
    nameEq letTerm.ident id
  else false

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
  sem compatibleType (tyEnv : TypeEnv) (ty1: Type) =
  | ty2 ->
    let tys = (ty1, ty2) in
    match compatibleTypeBase tyEnv tys with Some ty then Some ty

    -- NOTE(dlunde,2021-05-05): Temporary hack to make sure that tyapps are
    -- reduced before tyvars. Not sure why this is needed, but it should not
    -- matter in the end when we have a proper type system.
    else match tys with (TyApp t1, _) then
      compatibleType tyEnv t1.lhs ty2
    else match tys with (_, TyApp t2) then
      compatibleType tyEnv ty1 t2.lhs
    --------

    else match reduceType tyEnv ty1 with Some ty1 then
      compatibleType tyEnv ty1 ty2
    else match reduceType tyEnv ty2 with Some ty2 then
      compatibleType tyEnv ty1 ty2
    else None ()

  sem compatibleTypeBase (tyEnv: TypeEnv) =
  | _ -> None () -- Types are not compatible by default

  sem reduceType (tyEnv: Env) =
  | _ -> None () -- Types cannot be reduced by default

end

lang UnknownCompatibleType = CompatibleType + UnknownTypeAst

  sem compatibleTypeBase (tyEnv: TypeEnv) =
  | (TyUnknown _ & ty1, TyUnknown _) -> Some ty1
  | (TyUnknown _, ! TyUnknown _ & ty2) -> Some ty2
  | (! TyUnknown _ & ty1, TyUnknown _) -> Some ty1

end

lang VarCompatibleType = CompatibleType + VarTypeAst

  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyVar t1 & ty1, TyVar t2) ->
    if nameEq t1.ident t2.ident then Some ty1 else None ()

  sem reduceType (tyEnv : TypeEnv) =
  | TyVar {info = info, ident = id} ->
    match mapLookup id tyEnv with Some ty then Some ty else
      infoErrorExit info (concat "Unbound TyVar in reduceType: " (nameGetStr id))

end

lang AppCompatibleType = CompatibleType + AppTypeAst

  sem compatibleTypeBase (tyEnv : TypeEnv) =
  -- TODO(dlunde,2021-05-05): Left out for now for compatibility with original
  -- compatibleTypes

  -- NOTE(dlunde,2021-05-05): This is NOT how we want to handle TmApp in the
  -- end. We are now just discarding the RHS of all applications
  sem reduceType (tyEnv : TypeEnv) =
  | TyApp t -> Some t.lhs

end

lang BoolCompatibleType = CompatibleType + BoolTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyBool _ & t1, TyBool _) -> Some t1
end

lang IntCompatibleType = CompatibleType + IntTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyInt _ & t1, TyInt _) -> Some t1
end

lang FloatCompatibleType = CompatibleType + FloatTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyFloat _ & t1, TyFloat _) -> Some t1
end

lang CharCompatibleType = CompatibleType + CharTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyChar _ & t1, TyChar _) -> Some t1
end

lang FunCompatibleType = CompatibleType + FunTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyArrow t1, TyArrow t2) ->
    match compatibleType tyEnv t1.from t2.from with Some a then
      match compatibleType tyEnv t1.to t2.to with Some b then
        Some (TyArrow {{t1 with from = a} with to = b})
      else None ()
    else None ()
end

lang SeqCompatibleType = CompatibleType + SeqTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TySeq t1, TySeq t2) ->
    match compatibleType tyEnv t1.ty t2.ty with Some t then
      Some (TySeq {t1 with ty = t})
    else None ()
end

lang TensorCompatibleType = CompatibleType + TensorTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
  | (TyTensor t1, TyTensor t2) ->
    match compatibleType tyEnv t1.ty t2.ty with Some t then
      Some (TyTensor {t1 with ty = t})
    else None ()
end

lang RecordCompatibleType = CompatibleType + RecordTypeAst
  sem compatibleTypeBase (tyEnv : TypeEnv) =
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
  sem compatibleTypeBase (tyEnv : TypeEnv) =
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
            infoErrorExit t.info msg
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
      match (ty lhs, ty rhs) with (TyArrow {from = from, to = to}, ty) then
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
      let env = {env with varEnv = mapInsert t.ident t.tyIdent varEnv} in
      let body = typeAnnotExpr env t.body in
      let ty = ityarrow_ t.info t.tyIdent (ty body) in
      TmLam {{t with body = body}
                with ty = ty}
    else never
end

lang TypePropagation = TypeAnnot
  sem propagateExpectedType (tyEnv : Map Name Type) =
  | (_, t) -> t
end

lang LetTypeAnnot = TypeAnnot + TypePropagation + LetAst +  UnknownTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmLet t ->
    match env with {varEnv = varEnv, tyEnv = tyEnv} then
      let body = match t.tyBody with TyUnknown _ then t.body else
        propagateExpectedType tyEnv (t.tyBody, t.body) in
      let body = typeAnnotExpr env body in
      match compatibleType tyEnv t.tyBody (ty body) with Some tyBody then
        if _isTypeAscription t then
          withType tyBody body
        else
          let env = {env with varEnv = mapInsert t.ident tyBody varEnv} in
          let inexpr = typeAnnotExpr env t.inexpr in
          TmLet {{{{t with tyBody = tyBody}
                      with body = withType tyBody body}
                      with inexpr = inexpr}
                      with ty = ty inexpr}
      else
        let msg = join [
          "Inconsistent type annotation of let-expression\n",
          "Expected type: ", _pprintType (ty body), "\n",
          "Annotated type: ", _pprintType t.tyBody
        ] in
        infoErrorExit t.info msg
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
    match compatibleType tyEnv from t.tyIdent with Some ty then
      TmLam {{t with tyIdent = ty}
                with body = propagateExpectedType tyEnv (to, t.body)}
    else
      let msg = join [
        "Inconsistent type annotation of let-expression and lambda\n",
        "Type from let: ", _pprintType from, "\n",
        "Type from lambda: ", _pprintType t.tyIdent
      ] in
      infoErrorExit t.info msg
end

lang ExpTypeAnnot = TypeAnnot + ExtAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmExt t ->
    match env with {varEnv = varEnv, tyEnv = tyEnv} then
      let env = {env with varEnv = mapInsert t.ident t.tyIdent varEnv} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmExt {{t with inexpr = inexpr}
                with ty = ty inexpr}
    else never
end

lang RecLetsTypeAnnot = TypeAnnot + TypePropagation + RecLetsAst + LamAst + UnknownTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecLets t ->
    -- Add mapping from binding identifier to annotated type before doing type
    -- annotations of the bindings. This is to make annotations work for
    -- mutually recursive functions, given correct type annotations.
    let foldBindingInit = lam acc. lam binding : RecLetBinding.
      mapInsert binding.ident binding.tyBody acc
    in
    -- Add mapping from binding identifier to the inferred type.
    let foldBindingAfter = lam acc. lam binding : RecLetBinding.
      mapInsert binding.ident binding.tyBody acc
    in
    let annotBinding = lam env : TypeEnv. lam binding : RecLetBinding.
      let body = match binding.tyBody with TyUnknown _ then binding.body else
        propagateExpectedType env.tyEnv (binding.tyBody, binding.body) in
      let body = typeAnnotExpr env body in
      match env with {tyEnv = tyEnv} then
        let tyBody =
          match compatibleType tyEnv binding.tyBody (ty body) with Some tyBody then
            tyBody
          else
            let msg = join [
              "Inconsistent type annotation of recursive let-expression\n",
              "Expected type: ", _pprintType (ty body), "\n",
              "Annotated type: ", _pprintType binding.tyBody
            ] in
            infoErrorExit t.info msg
        in
        {{binding with body = body}
                  with tyBody = tyBody}
      else never
    in
    match env with {varEnv = varEnv} then
      let env = {env with varEnv = foldl foldBindingInit varEnv t.bindings} in
      let bindings = map (annotBinding env) t.bindings in
      let env = {env with varEnv = foldl foldBindingAfter varEnv bindings} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmRecLets {{{t with bindings = bindings}
                     with inexpr = inexpr}
                     with ty = ty inexpr}
    else never
end

lang ConstTypeAnnot = TypeAnnot + MExprConstType
  sem typeAnnotExpr (env : TypeEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = f (tyConst t.val) in
    TmConst {t with ty = ty }
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let tms = map (typeAnnotExpr env) t.tms in
    let elemTy =
      if eqi (length tms) 0 then ityunknown_ t.info
      else
        let types = map (lam term. ty term) tms in
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
    let bindingTypes = mapMap ty bindings in
    let labels = mapKeys t.bindings in
    let ty = TyRecord {fields = bindingTypes, labels = labels, info = t.info} in
    TmRecord {{t with bindings = bindings}
                 with ty = ty}
  | TmRecordUpdate t ->
    let rec = typeAnnotExpr env t.rec in
    let value = typeAnnotExpr env t.value in
    TmRecordUpdate {{{t with rec = rec}
                        with value = value}
                        with ty = ty rec}
end

lang TypeTypeAnnot = TypeAnnot + TypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmType t ->
    let tyEnv = mapInsert t.ident t.tyIdent env.tyEnv in
    let inexpr = typeAnnotExpr {env with tyEnv = tyEnv} t.inexpr in
    TmType {{t with inexpr = inexpr}
               with ty = ty inexpr}
end

lang DataTypeAnnot = TypeAnnot + DataAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmConDef t ->
    match env with {conEnv = conEnv} then
      let env = {env with conEnv = mapInsert t.ident t.tyIdent conEnv} in
      let inexpr = typeAnnotExpr env t.inexpr in
      TmConDef {{t with inexpr = inexpr}
                   with ty = ty inexpr}
    else never
  | TmConApp t ->
    let body = typeAnnotExpr env t.body in
    match env with {conEnv = conEnv, tyEnv = tyEnv} then
      let ty =
        match mapLookup t.ident conEnv with Some lty then
          match lty with TyArrow {from = from, to = to} then
            recursive let tyvar = lam ty.
              match ty with TyVar _ then ty
              else match ty with TyApp t then tyvar t.lhs
              else (ityunknown_ t.info)
            in
            match compatibleType tyEnv (ty body) from with Some _ then
              tyvar to
            else
              let msg = join [
                "Inconsistent types of constructor application",
                "Constructor expected argument of type ", _pprintType from,
                ", but the actual type was ", _pprintType (ty body)
              ] in
              infoErrorExit t.info msg
          else (ityunknown_ t.info)
        else
          let msg = join ["Application of untyped constructor: ",
                          nameGetStr t.ident] in
          infoErrorExit t.info msg
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
    match typeAnnotPat env (ty target) t.pat with (thnEnv, pat) then
      let thn = typeAnnotExpr thnEnv t.thn in
      let els = typeAnnotExpr env t.els in
      let ty =
        match compatibleType env.tyEnv (ty thn) (ty els) with Some ty
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
    TmUtest {{{{{t with test = test}
                  with expected = expected}
                  with next = next}
                  with tusing = tusing}
                  with ty = ty next}
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
    let expectedTy = match expectedTy with TyUnknown _ then t.ty else expectedTy in
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

lang DataPatTypeAnnot = TypeAnnot + DataPat + VariantTypeAst + VarTypeAst +
                        FunTypeAst
  sem typeAnnotPat (env : TypeEnv) (expectedTy : Type) =
  | PatCon t ->
    match mapLookup t.ident env.conEnv
    with Some (TyArrow {from = argTy, to = to}) then
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
  UnknownCompatibleType + VarCompatibleType + BoolCompatibleType +
  IntCompatibleType + FloatCompatibleType + CharCompatibleType +
  FunCompatibleType + SeqCompatibleType + TensorCompatibleType +
  RecordCompatibleType + VariantCompatibleType + AppCompatibleType +
  PropagateArrowLambda + PropagateLetType +

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

mexpr

use TestLang in

let eqTypeEmptyEnv : Type -> Type -> Bool = eqType [] in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let n = nameSym "n" in

let appConst = addi_ (int_ 5) (int_ 2) in
utest ty (typeAnnot appConst) with tyint_ using eqTypeEmptyEnv in

let variableType = tyarrow_ tyint_ tybool_ in
let appVariable = app_ (withType variableType (nvar_ x)) (int_ 0) in
utest ty (typeAnnot appVariable) with tybool_ using eqTypeEmptyEnv in

let partialAppConst = nlam_ x tyint_ (addi_ (int_ 5) (nvar_ x)) in
utest ty (typeAnnot partialAppConst)
with  tyarrow_ tyint_ tyint_
using eqTypeEmptyEnv in

let badApp = bindall_ [
  nulet_ x (int_ 5),
  app_ (nvar_ x) (float_ 3.14)
] in
utest ty (typeAnnot badApp) with tyunknown_ using eqTypeEmptyEnv in

let lamConstantReturnType = nulam_ x (int_ 0) in
utest ty (typeAnnot lamConstantReturnType)
with  tyarrow_ tyunknown_ tyint_
using eqTypeEmptyEnv in

let letAscription = bind_ (nlet_ x tyint_ (nvar_ y)) (nvar_ x) in
utest ty (typeAnnot letAscription) with tyint_ using eqTypeEmptyEnv in

let recLets = typeAnnot (bindall_ [
  nreclets_ [
    (x, tyarrow_ tyunit_ tyint_, nlam_ n tyunit_ (app_ (nvar_ y) uunit_)),
    (y, tyunknown_, nlam_ n tyunit_ (app_ (nvar_ x) uunit_)),
    (z, tyunknown_, nlam_ n tyunit_ (addi_ (app_ (nvar_ y) uunit_) (int_ 1)))
  ],
  uunit_
]) in
utest ty recLets with tyunit_ using eqTypeEmptyEnv in

(match recLets with TmRecLets {bindings = bindings} then
  let b0 : RecLetBinding = get bindings 0 in
  let b1 : RecLetBinding = get bindings 1 in
  let b2 : RecLetBinding = get bindings 2 in
  let xTy = tyarrow_ tyunit_ tyint_ in
  let yTy = tyarrow_ tyunit_ tyint_ in
  let zTy = tyarrow_ tyunit_ tyint_ in
  utest b0.tyBody with xTy using eqTypeEmptyEnv in
  utest b1.tyBody with yTy using eqTypeEmptyEnv in
  utest b2.tyBody with zTy using eqTypeEmptyEnv in
  ()
else never);

utest ty (typeAnnot (int_ 4)) with tyint_ using eqTypeEmptyEnv in
utest ty (typeAnnot (char_ 'c')) with tychar_ using eqTypeEmptyEnv in
utest ty (typeAnnot (float_ 1.2)) with tyfloat_ using eqTypeEmptyEnv in
utest ty (typeAnnot true_) with tybool_ using eqTypeEmptyEnv in

let emptySeq = typeAnnot (seq_ []) in
utest ty emptySeq with tyseq_ tyunknown_ using eqTypeEmptyEnv in

let intSeq = typeAnnot (seq_ [int_ 1, int_ 2, int_ 3]) in
utest ty intSeq with tyseq_ tyint_ using eqTypeEmptyEnv in

let intMatrix = typeAnnot (seq_ [seq_ [int_ 1, int_ 2],
                                 seq_ [int_ 3, int_ 4]]) in
utest ty intMatrix with tyseq_ (tyseq_ tyint_) using eqTypeEmptyEnv in

let unknownSeq = typeAnnot (seq_ [nvar_ x, nvar_ y]) in
utest ty unknownSeq with tyseq_ tyunknown_ using eqTypeEmptyEnv in

let emptyRecord = typeAnnot uunit_ in
utest ty emptyRecord with tyunit_ using eqTypeEmptyEnv in

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
utest ty record with expectedRecordType using eqTypeEmptyEnv in
let recordUpdate = typeAnnot (recordupdate_ record "x" (int_ 1)) in
utest ty recordUpdate with expectedRecordType using eqTypeEmptyEnv in

let typeDecl = bind_ (ntype_ n tyunknown_) uunit_ in
utest ty (typeAnnot typeDecl) with tyunit_ using eqTypeEmptyEnv in

let conApp = bindall_ [
  ntype_ n tyunknown_,
  ncondef_ x (tyarrow_ tyint_ (ntyvar_ n)),
  nconapp_ x (int_ 4)
] in
utest ty (typeAnnot conApp) with ntyvar_ n using eqTypeEmptyEnv in

let matchInteger = typeAnnot (bindall_ [
  nulet_ x (int_ 0),
  match_ (nvar_ x) (pint_ 0) (nvar_ x) (addi_ (nvar_ x) (int_ 1))
]) in
utest ty matchInteger with tyint_ using eqTypeEmptyEnv in
(match matchInteger with TmLet {inexpr = TmMatch t} then
  utest ty t.target with tyint_ using eqTypeEmptyEnv in
  utest ty t.thn with tyint_ using eqTypeEmptyEnv in
  utest ty t.els with tyint_ using eqTypeEmptyEnv in
  ()
else never);

let matchDistinct = typeAnnot (
  match_ (int_ 0) (pvar_ n) (int_ 0) (char_ '1')
) in
utest ty matchDistinct with tyunknown_ using eqTypeEmptyEnv in
(match matchDistinct with TmMatch t then
  utest ty t.target with tyint_ using eqTypeEmptyEnv in
  utest ty t.thn with tyint_ using eqTypeEmptyEnv in
  utest ty t.els with tychar_ using eqTypeEmptyEnv in
  ()
else never);

let utestAnnot = typeAnnot (
  utest_ (int_ 0) false_ (char_ 'c')
) in
utest ty utestAnnot with tychar_ using eqTypeEmptyEnv in
(match utestAnnot with TmUtest t then
  utest ty t.test with tyint_ using eqTypeEmptyEnv in
  utest ty t.expected with tybool_ using eqTypeEmptyEnv in
  utest ty t.next with tychar_ using eqTypeEmptyEnv in
  ()
else never);

utest ty (typeAnnot never_) with tyunknown_ using eqTypeEmptyEnv in

-- Test that types are propagated through patterns in match expressions
let matchSeq = bindall_ [
  match_ (seq_ [str_ "a", str_ "b", str_ "c", str_ "d"])
    (pseqedge_ [pseqtot_ [pchar_ 'a']] "mid" [pseqtot_ [pchar_ 'd']])
    (var_ "mid")
    never_
] in
utest ty (typeAnnot (symbolize matchSeq)) with tyseq_ tystr_ using eqTypeEmptyEnv in

let matchTree = bindall_ [
  type_ "Tree" tyunknown_,
  condef_ "Branch" (tyarrow_ (tytuple_ [tyvar_ "Tree", tyvar_ "Tree"]) (tyvar_ "Tree")),
  condef_ "Leaf" (tyarrow_ (tyseq_ tyint_) (tyvar_ "Tree")),
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
utest ty (typeAnnot (symbolize matchTree)) with tyseq_ tyint_ using eqTypeEmptyEnv in

()
