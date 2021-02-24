include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

type TypeEnv = {
  varEnv: AssocMap Name Type,
  conEnv: AssocMap Name Type,
  tyEnv : AssocMap Name Type
}

let _typeEnvEmpty = {
  varEnv = assocEmpty,
  conEnv = assocEmpty,
  tyEnv  = assocEmpty
}

let _envInsert = assocInsert {eq = nameEqSym}
let _envLookup = assocLookup {eq = nameEqSym}

let _isTypeAscription = use MExprAst in
  lam letTerm.
  match letTerm.inexpr with TmVar {ident = id} then
    nameEq letTerm.ident id
  else false

lang TypeAnnot =
  UnknownTypeAst + TypeAst + DataAst + FunTypeAst + VarTypeAst + VariantTypeAst

  sem typeExpr (env : TypeEnv) =

  sem typeAnnotExpr (env : TypeEnv) =

  sem collectDataTypes (env : TypeEnv) =
  | TmType t ->
    match env with {tyEnv = tyEnv} then
      let emptyVariantType = TyVariant {constrs = []} in
      let env = {env with tyEnv = _envInsert t.ident emptyVariantType tyEnv} in
      collectDataTypes env t.inexpr
    else never
  | TmConDef t ->
    match env with {conEnv = conEnv, tyEnv = tyEnv} then
      match t.ty with TyArrow {from = from, to = TyVar {ident = id}} then
        match _envLookup id tyEnv with Some (TyVariant c) then
          let tyv = TyVariant {c with constrs = cons t.ident c.constrs} in
          let env = {{env with tyEnv = _envInsert id tyv tyEnv}
                          with conEnv = _envInsert t.ident t.ty conEnv} in
          collectDataTypes env t.inexpr
        else
          error (join [
            "Type constructor ",
            nameGetStr t.ident,
            " references undefined type ",
            nameGetStr id
          ])
      else
        error (join ["Invalid type of type constructor ", nameGetStr t.ident])
    else never
  | t -> sfold_Expr_Expr collectDataTypes env t

  sem typeAnnot =
  | expr ->
    let env = collectDataTypes _typeEnvEmpty expr in
    typeAnnotExpr env expr
end

lang VarTypeAnnot = TypeAnnot + VarAst
  sem typeExpr (env : TypeEnv) =
  | TmVar t ->
    match t.ty with TyUnknown {} then
      match env with {varEnv = varEnv} then
        match _envLookup t.ident varEnv with Some ty then
          ty
        else t.ty
      else never
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | var & TmVar t ->
    TmVar {t with ty = typeExpr env var}
end

lang AppTypeAnnot = TypeAnnot + AppAst + FunTypeAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmApp t ->
    match t.ty with TyUnknown {} then
      match env with {tyEnv = tyEnv} then
        match typeExpr env t.lhs with TyArrow {from = from, to = to} then
          let ty = typeExpr env t.rhs in
          if eqType tyEnv from ty then
            to
          else error "Unexpected type of right-hand side of application"
        else error "Unexpected type of left-hand side of application"
      else never
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmApp t ->
    let t = {{t with lhs = typeAnnotExpr env t.lhs}
                with rhs = typeAnnotExpr env t.rhs} in
    TmApp {t with ty = typeExpr env (TmApp t)}
end

lang LamTypeAnnot = TypeAnnot + LamAst + FunTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmLam t ->
    match t.ty with TyUnknown {} then
      TyArrow {from = t.ty, to = typeExpr env t.body}
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmLam t ->
    match env with {varEnv = varEnv} then
      let env = {env with varEnv = _envInsert t.ident t.ty varEnv} in
      let t = {t with body = typeAnnotExpr env t.body} in
      TmLam {t with ty = typeExpr env (TmLam t)}
    else never
end

lang RecordTypeAnnot = TypeAnnot + RecordAst + RecordTypeAst
  sem typeExpr (env : TypeEnv) =
  | TmRecord t ->
    let f = lam acc. lam k. lam v.
      assocInsert {eq=eqString} k (typeExpr env v) acc
    in
    match t.ty with TyUnknown {} then
      TyRecord {fields = assocFold {eq=eqString} f assocEmpty t.bindings}
    else t.ty
  | TmRecordUpdate t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.rec
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmRecord t ->
    let bindings = assocMap {eq=eqString} (typeAnnotExpr env) t.bindings in
    let t = {t with bindings = bindings} in
    TmRecord {t with ty = typeExpr env (TmRecord t)}
  | TmRecordUpdate t ->
    let t = {{t with rec = typeAnnotExpr env t.rec}
                with value = typeAnnotExpr env t.value} in
    TmRecordUpdate {t with ty = typeExpr env (TmRecordUpdate t)}
end

lang LetTypeAnnot = TypeAnnot + LetAst
  sem typeExpr (env : TypeEnv) =
  | TmLet t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.inexpr
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | l & TmLet t ->
    let tyBody =
      match t.tyBody with TyUnknown {} then
        typeExpr env t.body
      else t.tyBody
    in
    if _isTypeAscription t then
      withType tyBody t.body
    else
      let t = {t with inexpr = typeAnnotExpr env t.inexpr} in
      let ty = typeExpr env (TmLet t) in
      let body = withType tyBody t.body in
      match env with {varEnv = varEnv} then
        let env = {env with varEnv = _envInsert t.ident tyBody varEnv} in
        TmLet {{{t with tyBody = tyBody}
                   with body = body}
                   with ty = ty}
      else never
end

lang TypeTypeAnnot = TypeAnnot + TypeAst
  sem typeExpr (env : TypeEnv) =
  | TmType t ->
    match env with {tyEnv = tyEnv} then
      match _envLookup t.ident tyEnv with Some ty then
        ty
      else t.ty
    else never

  sem typeAnnotExpr (env : TypeEnv) =
  | tpe & TmType t ->
    TmType {{t with ty = typeExpr env tpe}
               with inexpr = typeAnnotExpr env t.inexpr}
end

lang RecLetsTypeAnnot = TypeAnnot + RecLetsAst + LamAst
  sem typeExpr (env : TypeEnv) =
  | TmRecLets t ->
    let f = lam b.
      match b.ty with TyUnknown {} then
        match b.body with TmLam _ then
          typeExpr env b.body
        else
          error "Right-hand side of recursive let must be a lambda"
      else b.ty
    in
    match t.ty with TyUnknown {} then
      let _ = map f t.bindings in
      typeExpr env t.inexpr
    else t.ty
  sem typeAnnotExpr (env : TypeEnv) =
  | rl & TmRecLets t ->
    let bindingf = lam binding.
      let body = typeAnnotExpr env binding.body in
      {{binding with body = body}
                with ty = ty body}
    in
    let t = {{t with bindings = map bindingf t.bindings}
                with inexpr = typeAnnotExpr env t.inexpr} in
    TmRecLets {t with ty = typeExpr env (TmRecLets t)}
end

lang ConstTypeAnnot = TypeAnnot + ConstAst
  sem typeConst =
  -- Intentionally left blank

  sem typeExpr (env : TypeEnv) =
  | TmConst t ->
    match t.ty with TyUnknown {} then
      typeConst t.val
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | const & TmConst t ->
    TmConst {t with ty = typeExpr env const}
end

lang DataTypeAnnot = TypeAnnot + DataAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmConDef t -> t.ty
  | TmConApp t ->
    match env with {tyEnv = tyEnv, conEnv = conEnv} then
      match _envLookup t.ident conEnv with Some (TyArrow a) then
        if eqType tyEnv a.from (typeExpr env t.body) then
          a.to
        else error "Invalid type of right-hand side of constructor application"
      else error "Invalid type of left-hand side of constructor application"
    else never

  sem typeAnnotExpr (env : TypeEnv) =
  | TmConDef t ->
    TmConDef {t with inexpr = typeAnnotExpr env t.inexpr}
  | TmConApp t ->
    let t = {t with body = typeAnnotExpr env t.body} in
    TmConApp {t with ty = typeExpr env (TmConApp t)}
end

lang MatchTypeAnnot = TypeAnnot + MatchAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmMatch t ->
    match t.ty with TyUnknown {} then
      match env with {tyEnv = tyEnv} then
        let thnty = typeExpr env t.thn in
        let elsty = typeExpr env t.els in
        if eqType tyEnv thnty elsty then
          thnty
        else error "Types of match branches have different types"
      else never
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmMatch t ->
    let t = {{{t with target = typeAnnotExpr env t.target}
                 with thn = typeAnnotExpr env t.thn}
                 with els = typeAnnotExpr env t.els} in
    TmMatch {t with ty = typeExpr env (TmMatch t)}
end

lang UtestTypeAnnot = TypeAnnot + UtestAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmUtest t ->
    match t.ty with TyUnknown {} then
      match env with {tyEnv = tyEnv} then
        let lty = typeExpr env t.test in
        let rty = typeExpr env t.expected in
        if eqType tyEnv lty rty then
          typeExpr env t.next
        else
          error "Utest comparing terms of different types"
      else never
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmUtest t ->
    let t = {{{t with test = typeAnnotExpr env t.test}
                 with expected = typeAnnotExpr env t.expected}
                 with next = typeAnnotExpr env t.next} in
    TmUtest {t with ty = typeExpr env (TmUtest t)}
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmSeq t ->
    match t.ty with TyUnknown {} then
      match env with {tyEnv = tyEnv} then
        let fstType = typeExpr env (get t.tms 0) in
        if all (lam t. eqType tyEnv fstType (typeExpr env t)) t.tms then
          tyseq_ fstType
        else
          error "Sequence contains elements of different types"
      else never
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let t = {t with tms = map (typeAnnotExpr env) t.tms} in
    TmSeq {t with ty = typeExpr env (TmSeq t)}
end

-- TODO(larshum, 2021-02-05): Never terms should have a bottom type
lang NeverTypeAnnot = TypeAnnot + NeverAst
  sem typeExpr (env : TypeEnv) =
  | TmNever t -> TyUnknown {}

  sem typeAnnotExpr (env : TypeEnv) =
  | n & TmNever t -> TmNever {t with ty = typeExpr env n}
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

lang MExprTypeAnnot =

  -- Terms
  VarTypeAnnot + AppTypeAnnot + LamTypeAnnot + RecordTypeAnnot + LetTypeAnnot +
  TypeTypeAnnot + RecLetsTypeAnnot + ConstTypeAnnot + DataTypeAnnot +
  MatchTypeAnnot + UtestTypeAnnot + SeqTypeAnnot + NeverTypeAnnot +

  -- Constants
  IntTypeAnnot + ArithIntTypeAnnot + ShiftIntTypeAnnot + FloatTypeAnnot +
  ArithFloatTypeAnnot + FloatIntConversionTypeAnnot + BoolTypeAnnot +
  CmpIntTypeAnnot + CmpFloatTypeAnnot + CharTypeAnnot + CmpCharTypeAnnot +
  IntCharConversionTypeAnnot + FloatStringConversionTypeAnnot
end

lang TestLang = MExprTypeAnnot + MExprPrettyPrint + MExprEq

mexpr

use TestLang in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in
let n = nameSym "n" in

-- Type annotation of terms

let ascription = lam body.
  bind_ (nulet_ x body) (nvar_ x)
in

let appBody = addi_ (int_ 5) (int_ 2) in
utest ty (typeAnnot (ascription appBody))
with  tyint_
using eqType assocEmpty in

let lamBody = nulam_ y (float_ 2.718) in
utest ty (typeAnnot (ascription lamBody))
with  tyarrow_ tyunknown_ tyfloat_
using eqType assocEmpty in

let letWithTypedBody = bind_ (nulet_ x (int_ 0)) unit_ in
let typedLet = typeAnnot letWithTypedBody in
let letBodyType =
  match typedLet with TmLet {tyBody = tyBody} then
    tyBody
  else never
in
utest letBodyType with tyint_ using eqType assocEmpty in
utest ty typedLet with tyunit_ using eqType assocEmpty in

let recordBody = record_ [("a", int_ 2), ("b", float_ 2.0), ("c", false_)] in
let recordType = tyrecord_ [
  ("a", tyint_), ("b", tyfloat_), ("c", tybool_)
] in
utest ty (typeAnnot (ascription recordBody))
with  recordType
using eqType assocEmpty in

let recletsBody =
  bind_
    (nreclets_ [
      (x, tyunknown_, nulam_ y (int_ 5))
    ])
    unit_ in
let typeOfInnerLet =
  match typeAnnot recletsBody with TmRecLets {bindings = [t] ++ bindings} then
    ty (t.body)
  else never
in
utest typeOfInnerLet
with  tyarrow_ tyunknown_ tyint_
using eqType assocEmpty in
utest ty (typeAnnot recletsBody)
with  tyunit_
using eqType assocEmpty in

let constBody = int_ 0 in
utest ty (typeAnnot (ascription constBody))
with  tyint_
using eqType assocEmpty in

let matchBody = if_ true_ (int_ 2) (int_ 3) in
utest ty (typeAnnot (ascription matchBody))
with  tyint_
using eqType assocEmpty in

let utestBody = utest_ (int_ 2) (int_ 4) unit_ in
let typeOfInnerExpression =
  match typeAnnot utestBody with TmUtest {test = test} then
    ty test
  else never
in
utest typeOfInnerExpression
with  tyint_
using eqType assocEmpty in
utest ty (typeAnnot utestBody)
with  tyunit_
using eqType assocEmpty in

let seqBody = seq_ [int_ 2, int_ 3, int_ 4] in
utest ty (typeAnnot (ascription seqBody))
with  tyseq_ tyint_
using eqType assocEmpty in

utest ty (typeAnnot never_)
with  tyunknown_
using eqType assocEmpty in

let treeName = nameSym "Tree" in
let nodeName = nameSym "Node" in
let leafName = nameSym "Leaf" in
let treeConType = lam lty. tyarrow_ lty (ntyvar_ treeName) in
let dataType = lam t.
  bindall_ [
    ntype_ treeName (TyVariant {constrs = []}),
    ncondef_ nodeName (treeConType (tytuple_ [ntyvar_ treeName, ntyvar_ treeName])),
    ncondef_ leafName (treeConType tyint_),
    t
  ]
in
let expectedVariantType = TyVariant {constrs = [nodeName, leafName]} in
utest ty (typeAnnot (dataType unit_))
with  expectedVariantType
using eqType assocEmpty in

let tyEnv = seq2assoc {eq=nameEq} [(treeName, expectedVariantType)] in
let typeOfDataType = lam dataType.
  match dataType with TmType t then
    match t.inexpr with TmConDef t then
      match t.inexpr with TmConDef t then
        match t.inexpr with TmConApp t then
          t.ty
        else never
      else never
    else never
  else never
in
let treeLeafApp = nconapp_ leafName (int_ 5) in
utest typeOfDataType (typeAnnot (dataType treeLeafApp))
with  expectedVariantType
using eqType tyEnv in

let treeNodeApp = nconapp_ nodeName (tuple_ [
  nconapp_ leafName (int_ 0),
  nconapp_ leafName (int_ 1)
]) in
utest typeOfDataType (typeAnnot (dataType treeNodeApp))
with  expectedVariantType
using eqType tyEnv in

-- Type annotation of constant terms

let constlet = lam body. lam ty.
  bind_ (nlet_ x ty body) (nvar_ x)
in

let intLiteralLet = constlet (int_ 4) tyunknown_ in
utest ty (typeAnnot intLiteralLet)
with  tyint_
using eqType assocEmpty in

let addiLet = constlet (const_ (CAddi ())) tyunknown_ in
utest ty (typeAnnot addiLet)
with  tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)
using eqType assocEmpty in

let floatLiteralLet = constlet (float_ 4.0) tyunknown_ in
utest ty (typeAnnot floatLiteralLet)
with  tyfloat_
using eqType assocEmpty in

let boolLiteralLet = constlet true_ tyunknown_ in
utest ty (typeAnnot boolLiteralLet)
with  tybool_
using eqType assocEmpty in

let charLiteralLet = constlet (char_ 'a') tyunknown_ in
utest ty (typeAnnot charLiteralLet)
with  tychar_
using eqType assocEmpty in

let partialApp = lam ty1. lam ty2.
  bind_
    (nlet_ x ty1 (withType ty1 (app_ (const_ (CLtf ())) (float_ 3.14))))
    (nvar_ x)
in
utest ty (typeAnnot (partialApp tyunknown_ tyunknown_))
with  tyarrow_ tyfloat_ tybool_
using eqType assocEmpty in

()
