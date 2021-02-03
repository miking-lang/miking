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
    match env with {tyEnv = tyEnv} then
      match t.ty with TyUnknown {} then
        match typeExpr env t.lhs with TyArrow {from = from, to = to} then
          let ty = typeExpr env t.rhs in
          if eqType tyEnv from ty then
            to
          else error "Unexpected type of right-hand side of application"
        else error "Unexpected type of left-hand side of application"
      else t.ty
    else never

  sem typeAnnotExpr (env : TypeEnv) =
  | TmApp t ->
    let t = {{t with lhs = typeAnnotExpr env t.lhs}
                with rhs = typeAnnotExpr env t.rhs} in
    TmApp {t with ty = typeExpr env (TmApp t)}
end

lang FunTypeAnnot = TypeAnnot + FunAst + FunTypeAst
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
    TyRecord {fields = assocFold {eq=eqString} f assocEmpty t.bindings}
  | TmRecordUpdate t -> typeExpr env t.rec
end

lang LetTypeAnnot = TypeAnnot + LetAst
  sem typeExpr (env : TypeEnv) =
  | TmLet t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.body
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | l & TmLet t ->
    if _isTypeAscription t then
      let ty = typeExpr env l in
      withType ty t.body
    else
      let t = {t with body = typeAnnotExpr env t.body} in
      let ty = typeExpr env (TmLet t) in
      match env with {varEnv = varEnv} then
        let env = {env with varEnv = _envInsert t.ident ty varEnv} in
        TmLet {{t with ty = ty}
                  with inexpr = typeAnnotExpr env t.inexpr}
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

lang ConstTypeAnnot = TypeAnnot + ConstAst
  sem typeConst =

  sem typeExpr (env : TypeEnv) =
  | TmConst {val = v} -> typeConst v

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

lang MatchTypeAnnot = TypeAnnot + MatchAst
  sem typeExpr (env : TypeEnv) =
  | TmMatch t ->
    match t.ty with TyUnknown {} then
      typeExpr env t.thn
    else t.ty

  sem typeAnnotExpr (env : TypeEnv) =
  | TmMatch t ->
    let t = {{{t with target = typeAnnotExpr env t.target}
                 with thn = typeAnnotExpr env t.thn}
                 with els = typeAnnotExpr env t.els} in
    TmMatch {t with ty = typeExpr env (TmMatch t)}
end

lang SeqTypeAnnot = TypeAnnot + SeqAst + MExprEq
  sem typeExpr (env : TypeEnv) =
  | TmSeq t ->
    match env with {tyEnv = tyEnv} then
      match t.ty with TyUnknown {} then
        let fstType = typeExpr env (get t.tms 0) in
        if all (lam t. eqType tyEnv fstType (typeExpr env t)) t.tms then
          tyseq_ fstType
        else
          error "Sequence contains elements of different types"
      else t.ty
    else never

  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeq t ->
    let t = {t with tms = map (typeAnnotExpr env) t.tms} in
    TmSeq {t with ty = typeExpr env (TmSeq t)}
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
  VarTypeAnnot + AppTypeAnnot + FunTypeAnnot + RecordTypeAnnot + LetTypeAnnot +
  TypeTypeAnnot + ConstTypeAnnot + DataTypeAnnot + MatchTypeAnnot + SeqTypeAnnot +

  -- Constants
  IntTypeAnnot + ArithIntTypeAnnot + ShiftIntTypeAnnot + FloatTypeAnnot +
  ArithFloatTypeAnnot + FloatIntConversionTypeAnnot + BoolTypeAnnot +
  CmpIntTypeAnnot + CmpFloatTypeAnnot + CharTypeAnnot + CmpCharTypeAnnot +
  IntCharConversionTypeAnnot + FloatStringConversionTypeAnnot

  sem typeExpr (env : TypeEnv) =
  | t -> TyUnknown {}

  sem typeAnnotExpr (env : TypeEnv) =
  | t -> smap_Expr_Expr (typeAnnotExpr env) t
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
  bind_ (nlet_ x tyunknown_ body) (nvar_ x)
in

let appBody = addi_ (int_ 5) (int_ 2) in
utest ty (typeAnnot (ascription appBody))
with  tyint_
using eqType assocEmpty in

let lamBody = nulam_ y (float_ 2.718) in
utest ty (typeAnnot (ascription lamBody))
with  tyarrow_ tyunknown_ tyfloat_
using eqType assocEmpty in

let recordBody = record_ [("a", int_ 2), ("b", float_ 2.0), ("c", false_)] in
let recordType = tyrecord_ [
  ("a", tyint_), ("b", tyfloat_), ("c", tybool_)
] in
utest ty (typeAnnot (ascription recordBody))
with  recordType
using eqType assocEmpty in

let constBody = int_ 0 in
utest ty (typeAnnot (ascription constBody))
with  tyint_
using eqType assocEmpty in

let matchBody = if_ true_ (int_ 2) (int_ 3) in
utest ty (typeAnnot (ascription matchBody))
with  tyint_
using eqType assocEmpty in

let seqBody = seq_ [int_ 2, int_ 3, int_ 4] in
utest ty (typeAnnot (ascription seqBody))
with  tyseq_ tyint_
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
