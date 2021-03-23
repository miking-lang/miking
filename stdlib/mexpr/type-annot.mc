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
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

type TypeEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  tyEnv : AssocSeq Name Type
}

let _typeEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyEnv  = []
}

-- Given two types that are possibly unknown, this function attempts to find a
-- type that is compatible with both given types in the given type environment.
-- It is equivalent to type equality, except that unknown types are considered
-- compatible with any other type. If no compatible type can be found, `None`
-- is returned.
recursive
let _compatibleType =
  use MExprAst in
  use MExprEq in
  lam tyEnv. lam ty1. lam ty2.
  match (ty1, ty2) with (TyUnknown {}, _) then Some ty2
  else match (ty1, ty2) with (_, TyUnknown {}) then Some ty1
  else match (ty1, ty2) with (TyArrow t1, TyArrow t2) then
    match _compatibleType tyEnv t1.from t2.from with Some a then
      match _compatibleType tyEnv t1.to t2.to with Some b then
        Some (TyArrow {from = a, to = b})
      else None ()
    else None ()
  else match (ty1, ty2) with (TySeq t1, TySeq t2) then
    match _compatibleType tyEnv t1.ty t2.ty with Some t then
      Some (TySeq {ty = t})
    else None ()
  else if eqType tyEnv ty1 ty2 then Some ty1
  else None ()
end

let _isTypeAscription = use MExprAst in
  lam letTerm.
  match letTerm.inexpr with TmVar {ident = id} then
    nameEq letTerm.ident id
  else false

lang TypeAnnot
  sem typeAnnotExpr (env : TypeEnv) =
  -- Intentionally left blank

  sem typeAnnot =
  | expr -> typeAnnotExpr _typeEnvEmpty expr
end

lang VarTypeAnnot = TypeAnnot + VarAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmVar t ->
    let ty =
      match env with {varEnv = varEnv, tyEnv = tyEnv} then
        match mapLookup t.ident varEnv with Some ty then
          match _compatibleType tyEnv t.ty ty with Some ty then
            ty
          else error "Inconsistent type of annotated variable"
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
        match _compatibleType env.tyEnv from ty with Some _ then
          to
        else tyunknown_
      else tyunknown_
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
      let ty = tyarrow_ t.tyIdent (ty body) in
      TmLam {{t with body = body}
                with ty = ty}
    else never
end

lang LetTypeAnnot = TypeAnnot + LetAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmLet t ->
    match env with {varEnv = varEnv, tyEnv = tyEnv} then
      let body = typeAnnotExpr env t.body in
      match _compatibleType tyEnv t.tyBody (ty body) with Some tyBody then
        if _isTypeAscription t then
          withType tyBody body
        else
          let env = {env with varEnv = mapInsert t.ident tyBody varEnv} in
          let inexpr = typeAnnotExpr env t.inexpr in
          TmLet {{{{t with tyBody = tyBody}
                      with body = body}
                      with inexpr = inexpr}
                      with ty = ty inexpr}
      else error "Inconsistent type annotation of let-term"
    else never
end

lang RecLetsTypeAnnot = TypeAnnot + RecLetsAst + LamAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecLets t ->
    -- Add mapping from binding identifier to annotated type before doing type
    -- annotations of the bindings. This is to make annotations work for
    -- mutually recursive functions, given correct type annotations.
    let foldBindingInit = lam acc. lam binding.
      mapInsert binding.ident binding.tyBody acc
    in
    -- Add mapping from binding identifier to the inferred type.
    let foldBindingAfter = lam acc. lam binding.
      mapInsert binding.ident binding.ty acc
    in
    let annotBinding = lam env. lam binding.
      let body = typeAnnotExpr env binding.body in
      match env with {tyEnv = tyEnv} then
        let tyBody =
          match _compatibleType tyEnv binding.tyBody (ty body) with Some tyBody then
            tyBody
          else error "Inconsistent type annotation of recursive let-term"
        in
        {{binding with body = body}
                  with ty = tyBody}
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

lang ConstTypeAnnot = TypeAnnot + ConstAst
  sem typeConst =
  -- Intentionally left blank

  sem typeAnnotExpr (env : TypeEnv) =
  | TmConst t -> TmConst {t with ty = typeConst t.val}
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let tms = map (typeAnnotExpr env) t.tms in
    let elemTy =
      if eqi (length tms) 0 then tyunknown_
      else
        let fstty = ty (get tms 0) in
        if all (lam tm. eqType env.tyEnv fstty (ty tm)) tms then fstty
        else tyunknown_
    in
    TmSeq {{t with tms = tms}
              with ty = tyseq_ elemTy}
end

lang RecordTypeAnnot = TypeAnnot + RecordAst + RecordTypeAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecord t ->
    let bindings = mapMap (typeAnnotExpr env) t.bindings in
    let bindingTypes = mapMap ty bindings in
    let ty = TyRecord {fields = bindingTypes} in
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
    let tyEnv = assocSeqInsert t.ident t.tyIdent env.tyEnv in
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
          match lty with TyArrow {from = from, to = TyVar target} then
            match _compatibleType tyEnv (ty body) from with Some _ then
              TyVar target
            else error "Inconsistent type annotation of constructor application"
          else tyunknown_
        else error "Application of undefined constructor"
      in
      TmConApp {{t with body = body}
                   with ty = ty}
    else never
end

lang MatchTypeAnnot = TypeAnnot + MatchAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmMatch t ->
    let target = typeAnnotExpr env t.target in
    let thn = typeAnnotExpr env t.thn in
    let els = typeAnnotExpr env t.els in
    let ty =
      match env with {tyEnv = tyEnv} then
        match _compatibleType tyEnv (ty thn) (ty els) with Some ty then
          ty
        else tyunknown_
      else never
    in
    TmMatch {{{{t with target = target}
                  with thn = thn}
                  with els = els}
                  with ty = ty}
end

lang UtestTypeAnnot = TypeAnnot + UtestAst + MExprEq
  sem typeAnnotExpr (env : TypeEnv) =
  | TmUtest t ->
    let test = typeAnnotExpr env t.test in
    let expected = typeAnnotExpr env t.expected in
    let next = typeAnnotExpr env t.next in
    TmUtest {{{{t with test = test}
                  with expected = expected}
                  with next = next}
                  with ty = ty next}
end

lang NeverTypeAnnot = TypeAnnot + NeverAst
  sem typeAnnotExpr (env : TypeEnv) =
  | TmNever t -> TmNever {t with ty = tyunknown_}
end

lang IntTypeAnnot = ConstTypeAnnot + IntAst
  sem typeConst =
  | CInt _ -> tyint_
end

lang ArithIntTypeAnnot = ConstTypeAnnot + ArithIntAst
  sem typeConst =
  | CAddi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSubi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CMuli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CDivi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CNegi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CModi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
end

lang ShiftIntTypeAnnot = ConstTypeAnnot + ShiftIntAst
  sem typeConst =
  | CSlli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSrli _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CSrai _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
end

lang FloatTypeAnnot = ConstTypeAnnot + FloatAst
  sem typeConst =
  | CFloat _ -> tyfloat_
end

lang ArithFloatTypeAnnot = ConstTypeAnnot + ArithFloatAst
  sem typeConst =
  | CAddf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CSubf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CMulf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CDivf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
  | CNegf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tyfloat_)
end

lang FloatIntConversionTypeAnnot = ConstTypeAnnot + FloatIntConversionAst
  sem typeConst =
  | CFloorfi _ -> tyarrow_ tyfloat_ tyint_
  | CCeilfi _ -> tyarrow_ tyfloat_ tyint_
  | CRoundfi _ -> tyarrow_ tyfloat_ tyint_
  | CInt2float _ -> tyarrow_ tyint_ tyfloat_
end

lang BoolTypeAnnot = ConstTypeAnnot + BoolAst
  sem typeConst =
  | CBool _ -> tybool_
end

lang CmpIntTypeAnnot = ConstTypeAnnot + CmpIntAst
  sem typeConst =
  | CEqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CNeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CLti _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CGti _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CLeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
  | CGeqi _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tybool_)
end

lang CmpFloatTypeAnnot = ConstTypeAnnot + CmpFloatAst
  sem typeConst =
  | CEqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CNeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CLtf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CGtf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CLeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
  | CGeqf _ -> tyarrow_ tyfloat_ (tyarrow_ tyfloat_ tybool_)
end

lang CharTypeAnnot = ConstTypeAnnot + CharAst
  sem typeConst =
  | CChar _ -> tychar_
end

lang CmpCharTypeAnnot = ConstTypeAnnot + CmpCharAst
  sem typeConst =
  | CEqc _ -> tyarrow_ tychar_ (tyarrow_ tychar_ tybool_)
end

lang IntCharConversionTypeAnnot = ConstTypeAnnot + IntCharConversionAst
  sem typeConst =
  | CInt2Char _ -> tyarrow_ tyint_ tychar_
  | CChar2Int _ -> tyarrow_ tychar_ tyint_
end

lang FloatStringConversionTypeAnnot = ConstTypeAnnot + FloatStringConversionAst
  sem typeConst =
  | CString2float _ -> tyarrow_ tystr_ tyfloat_
end

-- NOTE(larshum, 2021-03-08): There is currently no type for symbols, so they
-- are considered to be of an unknown type.
lang SymbTypeAnnot = ConstTypeAnnot + SymbAst
  sem typeConst =
  | CSymb _ -> tyunknown_
  | CGensym _ -> tyarrow_ tyunit_ tyunknown_
  | CSym2hash _ -> tyarrow_ tyunknown_ tyint_
end

lang CmpSymbTypeAnnot = ConstTypeAnnot + CmpSymbAst
  sem typeConst =
  | CEqsym _ -> tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_)
end

lang SeqOpTypeAnnot = ConstTypeAnnot + SeqOpAst
  sem typeConst =
  | CSet _ -> tyarrow_ utyseq_ (tyarrow_ tyint_ (tyarrow_ tyunknown_ utyseq_))
  | CGet _ -> tyarrow_ utyseq_ (tyarrow_ tyint_ utyseq_)
  | CCons _ -> tyarrow_ tyunknown_ (tyarrow_ utyseq_ utyseq_)
  | CSnoc _ -> tyarrow_ utyseq_ (tyarrow_ tyunknown_ utyseq_)
  | CConcat _ -> tyarrow_ utyseq_ (tyarrow_ utyseq_ utyseq_)
  | CLength _ -> tyarrow_ utyseq_ tyint_
  | CReverse _ -> tyarrow_ utyseq_ utyseq_
  | CCreate _ -> tyarrow_ tyint_ (tyarrow_ (tyarrow_ tyint_ tyunknown_) utyseq_)
  | CSplitAt _ -> tyarrow_ utyseq_ (tyarrow_ tyint_ (tytuple_ [utyseq_, utyseq_]))
  | CSubsequence _ -> tyarrow_ utyseq_ (tyarrow_ tyint_ (tyarrow_ tyint_ utyseq_))
end

lang FileOpTypeAnnot = ConstTypeAnnot + FileOpAst
  sem typeConst =
  | CFileRead _ -> tyarrow_ tystr_ tystr_
  | CFileWrite _ -> tyarrow_ tystr_ (tyarrow_ tystr_ tyunit_)
  | CFileExists _ -> tyarrow_ tystr_ tybool_
  | CFileDelete _ -> tyarrow_ tystr_ tyunit_
end

lang IOTypeAnnot = ConstTypeAnnot + IOAst
  sem typeConst =
  | CPrint _ -> tyarrow_ tystr_ tyunit_
  | CReadLine _ -> tyarrow_ tyunit_ tystr_
  | CReadBytesAsString _ -> tyarrow_ tyint_ (tytuple_ [tystr_, tyint_])
end

lang RandomNumberGeneratorTypeAnnot = ConstTypeAnnot + RandomNumberGeneratorAst
  sem typeConst =
  | CRandIntU _ -> tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
  | CRandSetSeed _ -> tyarrow_ tyint_ tyunit_
end

lang SysTypeAnnot = ConstTypeAnnot + SysAst
  sem typeConst =
  | CExit _ -> tyarrow_ tyint_ tyunknown_
  | CError _ -> tyarrow_ tystr_ tyunknown_
  | CArgv _ -> tyseq_ tystr_
end

lang TimeTypeAnnot = ConstTypeAnnot + TimeAst
  sem typeConst =
  | CWallTimeMs _ -> tyarrow_ tyunit_ tyfloat_
  | CSleepMs _ -> tyarrow_ tyint_ tyunit_
end

-- NOTE(larshum, 2021-03-08): There is currently no reference type in MExpr, so
-- they are considered to be of an unknown type.
lang RefOpTypeAnnot = ConstTypeAnnot + RefOpAst
  sem typeConst =
  | CRef _ -> tyarrow_ tyunknown_ tyunknown_
  | CModRef _ -> tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunit_)
  | CDeRef _ -> tyarrow_ tyunknown_ tyunknown_
end

lang MapTypeAnnot = ConstTypeAnnot + MapAst
  sem typeConst =
  | CMapEmpty _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_)) tyunknown_
  | CMapInsert _ ->
    tyarrow_ tyunknown_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
  | CMapRemove _ ->
    tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)
  | CMapFindWithExn _ ->
    tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)
  | CMapFindOrElse _ ->
    tyarrow_ (tyarrow_ tyunit_ tyunknown_)
             (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
  | CMapFindApplyOrElse _ ->
    tyarrow_ (tyarrow_ tyunknown_ tyunknown_)
             (tyarrow_ (tyarrow_ tyunit_ tyunknown_)
                       (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
  | CMapBindings _ ->
    tyarrow_ tyunknown_ (tyseq_ (tytuple_ [tyunknown_, tyunknown_]))
  | CMapSize _ ->
    tyarrow_ tyunknown_ tyint_
  | CMapMem _ ->
    tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_)
  | CMapAny _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
             (tyarrow_ tyunknown_ tybool_)
  | CMapMap _ ->
    tyarrow_ (tyarrow_ tyunknown_ tyunknown_)
             (tyarrow_ tyunknown_ tyunknown_)
  | CMapMapWithKey _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_))
             (tyarrow_ tyunknown_ tyunknown_)
  | CMapFoldWithKey _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)))
             tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyunknown_)
  | CMapEq _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
             (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tybool_))
  | CMapCmp _ ->
    tyarrow_ (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_))
             (tyarrow_ tyunknown_ (tyarrow_ tyunknown_ tyint_))
  | CMapGetCmpFun _ ->
    tyarrow_ tyunknown_ (tyarrow_ tyunknown_
                        (tyarrow_ tyunknown_ tyint_))
end

lang MExprTypeAnnot =

  -- Terms
  VarTypeAnnot + AppTypeAnnot + LamTypeAnnot + RecordTypeAnnot + LetTypeAnnot +
  TypeTypeAnnot + RecLetsTypeAnnot + ConstTypeAnnot + DataTypeAnnot +
  MatchTypeAnnot + UtestTypeAnnot + SeqTypeAnnot + NeverTypeAnnot +

  -- Constants
  IntTypeAnnot + ArithIntTypeAnnot + ShiftIntTypeAnnot + FloatTypeAnnot +
  ArithFloatTypeAnnot + FloatIntConversionTypeAnnot + BoolTypeAnnot +
  CmpIntTypeAnnot + CmpFloatTypeAnnot + CharTypeAnnot + CmpCharTypeAnnot +
  IntCharConversionTypeAnnot + FloatStringConversionTypeAnnot + SymbTypeAnnot +
  CmpSymbTypeAnnot + SeqOpTypeAnnot + FileOpTypeAnnot + IOTypeAnnot +
  RandomNumberGeneratorTypeAnnot + SysTypeAnnot + TimeTypeAnnot +
  RefOpTypeAnnot
end

lang TestLang = MExprTypeAnnot + MExprPrettyPrint + MExprEq

mexpr

use TestLang in

let eqTypeEmptyEnv = eqType [] in

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
    (x, tyarrow_ tyunit_ tyint_, nlam_ n tyunit_ (app_ (nvar_ y) unit_)),
    (y, tyunknown_, nlam_ n tyunit_ (app_ (nvar_ x) unit_)),
    (z, tyunknown_, nlam_ n tyunit_ (addi_ (app_ (nvar_ y) unit_) (int_ 1)))
  ],
  unit_
]) in
utest ty recLets with tyunit_ using eqTypeEmptyEnv in

(match recLets with TmRecLets {bindings = bindings} then
  let xTy = tyarrow_ tyunit_ tyint_ in
  let yTy = tyarrow_ tyunit_ tyint_ in
  let zTy = tyarrow_ tyunit_ tyint_ in
  utest (get bindings 0).ty with xTy using eqTypeEmptyEnv in
  utest (get bindings 1).ty with yTy using eqTypeEmptyEnv in
  utest (get bindings 2).ty with zTy using eqTypeEmptyEnv in
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

let emptyRecord = typeAnnot unit_ in
utest ty emptyRecord with tyunit_ using eqTypeEmptyEnv in

let record = typeAnnot (record_ [
  ("a", int_ 0), ("b", float_ 2.718), ("c", record_ []),
  ("d", record_ [
    ("e", seq_ [int_ 1, int_ 2]),
    ("f", record_ [
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

let typeDecl = bind_ (ntype_ n tyunknown_) unit_ in
utest ty (typeAnnot typeDecl) with tyunit_ using eqTypeEmptyEnv in

let conApp = bindall_ [
  ntype_ n tyunknown_,
  ncondef_ x (tyarrow_ tyint_ (ntyvar_ n)),
  nconapp_ x (int_ 4)
] in
utest ty (typeAnnot conApp) with ntyvar_ n using eqTypeEmptyEnv in

let matchInteger = typeAnnot (bindall_ [
  nlet_ x tyint_ (int_ 0),
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

()
