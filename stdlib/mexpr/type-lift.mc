-- Lift out types of an MExpr program. In particular, record types are lifted
-- and replaced with type variables, and all constructors for variant types are
-- lifted and collected into a single type.  Note that the latter probably has
-- consequences for type checking: information is lost when lifting constructor
-- definitions.
--
-- Requires symbolize and type-annot to be run first.
include "assoc-seq.mc"
include "map.mc"
include "name.mc"
include "stringid.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

------------------------------
-- TYPE LIFTING ENVIRONMENT --
------------------------------

type TypeLiftEnv = {

  -- Collects all type bindings encountered in the program in sequence.
  typeEnv: AssocSeq Name Type,

  -- Record types encountered so far. Uses intrinsic maps as this is
  -- performance critical.
  records: Map (Map SID Type) Name,

  -- Variant types and their constructors encountered so far.
  variants: Map Name (Map Name Type)
}

-- This type is added specifically for the type lifting to allow distinguishing
-- between variant types in the type environment before their constructors have
-- been added.
lang VariantNameTypeAst
  syn Type =
  | TyVariantName {ident : Name}

  sem eqType (typeEnv : TypeEnv) (lhs : Type) =
  | TyVariantName {ident = rid} ->
    match lhs with TyVariantName {ident = lid} then
      nameEq lid rid
    else false
end

-- Replaces all variant type names with the variant type they represent. This
-- function is called after going through the program, at which point all
-- variant constructors have been identified.
let _replaceVariantNamesInTypeEnv = lam env.
  use VariantTypeAst in
  use VariantNameTypeAst in
  let f = lam ty.
    match ty with TyVariantName {ident = ident} then
      match mapLookup ident env.variants with Some constrs then
        TyVariant {constrs = constrs}
      else
        error (join ["No variant type ", nameGetStr ident,
                     " found in environment"])
    else ty
  in
  assocSeqMap f env.typeEnv

-- This function is a simple comparison function for types. It required as a
-- comparison function for the records map of the type-lifting environment.
recursive let _cmpType = lam ty1. lam ty2.
  use MExprAst in
  let _typeId = lam ty.
    match ty with TyUnknown _ then 0
    else match ty with TyBool _ then 1
    else match ty with TyInt _ then 2
    else match ty with TyFloat _ then 3
    else match ty with TyChar _ then 4
    else match ty with TyArrow _ then 5
    else match ty with TySeq _ then 6
    else match ty with TyRecord _ then 7
    else match ty with TyVariant _ then 8
    else match ty with TyVar _ then 9
    else match ty with TyApp _ then 10
    else never
  in
  let id1 = _typeId ty1 in
  let id2 = _typeId ty2 in
  let diff = subi id1 id2 in
  if eqi diff 0 then
    match (ty1, ty2) with (TyArrow t1, TyArrow t2) then
      let fromDiff = _cmpType t1.from t2.from in
      if eqi fromDiff 0 then _cmpType t1.to t2.to
      else fromDiff
    else match (ty1, ty2) with (TySeq t1, TySeq t2) then
      _cmpType t1.ty t2.ty
    else match (ty1, ty2) with (TyRecord t1, TyRecord t2) then
      mapCmp _cmpType t1.fields t2.fields
    else match (ty1, ty2) with (TyVariant t1, TyVariant t2) then
      mapCmp _cmpType t1.constrs t2.constrs
    else match (ty1, ty2) with (TyVar t1, TyVar t2) then
      nameCmp t1.ident t2.ident
    else match (ty1, ty2) with (TyApp t1, TyApp t2) then
      let lhsDiff = _cmpType t1.lhs t2.lhs in
      if eqi lhsDiff 0 then _cmpType t1.rhs t2.rhs
      else lhsDiff
    else diff
  else diff
end

-----------
-- TERMS --
-----------

lang TypeLift = MExprEq
  sem typeLiftH (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLift =
  | e ->
    let emptyEnv = {
      typeEnv = [],
      records = mapEmpty (mapCmp _cmpType),
      variants = mapEmpty nameCmp
    } in
    match typeLiftH emptyEnv e with (env, t) then
      let typeEnv = _replaceVariantNamesInTypeEnv env in
      (typeEnv, t)
    else never
end

lang VarTypeLift = TypeLift + VarAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmVar t -> (env, TmVar t)
end

lang AppTypeLift = TypeLift + AppAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmApp t ->
    match typeLiftH env t.lhs with (env, lhs) then
      match typeLiftH env t.rhs with (env, rhs) then
        (env, TmApp {{t with lhs = lhs}
                        with rhs = rhs})
      else never
    else never
end

lang LamTypeLift = TypeLift + LamAst
  sem liftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftH (env : TypeLiftEnv) =
  | TmLam t ->
    match liftType env t.tyIdent with (env, tyIdent) then
      match typeLiftH env t.body with (env, body) then
        (env, TmLam {{t with tyIdent = tyIdent}
                        with body = body})
      else never
    else never
end

lang LetTypeLift = TypeLift + LetAst
  sem liftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftH (env : TypeLiftEnv) =
  | TmLet t ->
    match typeLiftH env t.body with (env, body) then
      match liftType env t.tyBody with (env, tyBody) then
        match typeLiftH env t.inexpr with (env, inexpr) then
          (env, TmLet {{{t with body = body}
                           with tyBody = tyBody}
                           with inexpr = inexpr})
        else never
      else never
    else never
end

lang RecLetsTypeLift = TypeLift + RecLetsAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmRecLets t ->
    let f = lam env. lam binding. typeLiftH env binding.body in
    match mapAccumL f env t.bindings with (env, bindings) then
      match typeLiftH env t.inexpr with (env, inexpr) then
        (env, TmRecLets {{t with bindings = bindings}
                            with inexpr = inexpr})
      else never
    else never
end

lang ConstTypeLift = TypeLift + ConstAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmConst t -> (env, TmConst t)
end

lang SeqTypeLift = TypeLift + SeqAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmSeq t ->
    match mapAccumL typeLiftH env t.tms with (env, tms) then
      (env, TmSeq {t with tms = tms})
    else never
end

lang RecordTypeLift = TypeLift + RecordAst
  sem liftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftH (env : TypeLiftEnv) =
  | TmRecord t ->
    let f = lam env. lam. lam v. typeLiftH env v in
    match mapMapAccum f env t.bindings with (env, bindings) then
      match liftType env t.ty with (env, ty) then
        (env, TmRecord {{t with bindings = bindings}
                           with ty = ty})
      else never
    else never
  | TmRecordUpdate t ->
    match typeLiftH env t.rec with (env, rec) then
      match typeLiftH env t.value with (env, value) then
        (env, TmRecordUpdate {{t with rec = rec}
                                 with value = value})
      else never
    else never
end

lang TypeTypeLift = TypeLift + TypeAst + VariantTypeAst + UnknownTypeAst +
                    VariantNameTypeAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmType t ->
    let tyIdent =
      match t.tyIdent with TyUnknown {} then
        tyvariant_ []
      else t.tyIdent
    in
    let env =
      -- Ignore any existing constructors in the variant type because otherwise
      -- we may get duplicates.
      match tyIdent with TyVariant _ then
        let variantNameTy = TyVariantName {ident = t.ident} in
        {{env with variants = mapInsert t.ident (mapEmpty nameCmp) env.variants}
              with typeEnv = assocSeqInsert t.ident variantNameTy env.typeEnv}
      else
        {env with typeEnv = assocSeqInsert t.ident tyIdent env.typeEnv}
    in
    match typeLiftH env t.inexpr with (env, inexpr) then
      (env, inexpr)
    else never
end

lang DataTypeLift = TypeLift + DataAst + FunTypeAst + VarTypeAst
  sem liftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftH (env : TypeLiftEnv) =
  | TmConDef t ->
    let env =
      match t.tyIdent with TyArrow {from = from, to = TyVar {ident = ident}} then
        let f = lam variantMap. mapInsert t.ident from variantMap in
        let err = lam.
          error (join ["Constructor ", nameGetStr t.ident,
                       " defined before referenced variant type ",
                       nameGetStr ident])
        in
        let variantMap = mapLookupApplyOrElse f err ident env.variants in
        {env with variants = mapInsert ident variantMap env.variants}
      else env
    in
    match typeLiftH env t.inexpr with (env, inexpr) then
      (env, inexpr)
    else never
  | TmConApp t ->
    match typeLiftH env t.body with (env, body) then
      (env, TmConApp {t with body = body})
    else never
end

lang MatchTypeLift = TypeLift + MatchAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmMatch t ->
    match typeLiftH env t.target with (env, target) then
      match typeLiftH env t.thn with (env, thn) then
        match typeLiftH env t.els with (env, els) then
          (env, TmMatch {{{t with target = target}
                             with thn = thn}
                             with els = els})
        else never
      else never
    else never
end

lang UtestTypeLift = TypeLift + UtestAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmUtest t ->
    match typeLiftH env t.test with (env, test) then
      match typeLiftH env t.expected with (env, expected) then
        match typeLiftH env t.next with (env, next) then
          (env, TmUtest {{{t with test = test}
                             with expected = expected}
                             with next = next})
        else never
      else never
    else never
end

lang NeverTypeLift = TypeLift + NeverAst
  sem typeLiftH (env : TypeLiftEnv) =
  | TmNever t -> (env, TmNever t)
end

-----------
-- TYPES --
-----------

lang UnknownTypeTypeLift = TypeLift + UnknownTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyUnknown {} -> (env, TyUnknown {})
end

lang BoolTypeTypeLift = TypeLift + BoolTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyBool {} -> (env, TyBool {})
end

lang IntTypeTypeLift = TypeLift + IntTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyInt {} -> (env, TyInt {})
end

lang FloatTypeTypeLift = TypeLift + FloatTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyFloat {} -> (env, TyFloat {})
end

lang CharTypeTypeLift = TypeLift + CharTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyChar {} -> (env, TyChar {})
end

lang FunTypeTypeLift = TypeLift + FunTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyArrow t ->
    match liftType env t.from with (env, from) then
      match liftType env t.to with (env, to) then
        (env, TyArrow {from = from, to = to})
      else never
    else never
end

lang SeqTypeTypeLift = TypeLift + SeqTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TySeq t ->
    match liftType env t.ty with (env, ty) then
      (env, TySeq {ty = ty})
    else never
end

lang RecordTypeTypeLift = TypeLift + RecordTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyRecord {fields = fields} & ty ->
    if eqi (mapLength fields) 0 then
      (env, ty)
    else match mapLookup fields env.records with Some name then
      match assocSeqLookup {eq=nameEq} name env.typeEnv with Some recTyVar then
        (env, recTyVar)
      else
        dprintLn (mapBindings fields);
        dprintLn name;
        dprintLn env.typeEnv;
        error "Record mapped to unknown type"
    else
      let recName = nameSym "Rec" in
      let recVar = ntyvar_ recName in
      let env = {{env with records = mapInsert fields recName env.records}
                      with typeEnv = assocSeqInsert recName ty env.typeEnv} in
      (env, recVar)
end

lang VariantTypeTypeLift = TypeLift + VariantTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyVariant t -> (env, TyVariant t)
end

lang VarTypeTypeLift = TypeLift + VarTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyVar t -> (env, TyVar t)
end

lang AppTypeTypeLift = TypeLift + AppTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyApp t ->
    match liftType env t.lhs with (env, lhs) then
      match liftType env t.rhs with (env, rhs) then
        (env, TyApp {lhs = lhs, rhs = rhs})
      else never
    else never
end

lang VariantNameTypeTypeLift = TypeLift + VariantNameTypeAst
  sem liftType (env : TypeLiftEnv) =
  | TyVariantName t -> (env, TyVariantName t)
end

lang MExprTypeLift =
  -- Terms
  VarTypeLift + AppTypeLift + LamTypeLift + LetTypeLift + RecLetsTypeLift +
  ConstTypeLift + SeqTypeLift + RecordTypeLift + TypeTypeLift + DataTypeLift +
  MatchTypeLift + UtestTypeLift + NeverTypeLift +

  -- Types
  UnknownTypeTypeLift + BoolTypeTypeLift + IntTypeTypeLift +
  FloatTypeTypeLift + CharTypeTypeLift + FunTypeTypeLift + SeqTypeTypeLift +
  RecordTypeTypeLift + VariantTypeTypeLift + VarTypeTypeLift +
  AppTypeTypeLift + VariantNameTypeTypeLift
end

lang TestLang = MExprTypeLift + MExprSym + MExprTypeAnnot + MExprPrettyPrint

mexpr

use TestLang in

let eqEnv = lam lenv. lam renv.
  use MExprEq in
  let elemCmp = lam l. lam r.
    and (eqString (nameGetStr l.0) (nameGetStr r.0))
        (eqType assocSeqEmpty l.1 r.1)
  in
  if eqi (assocSeqLength lenv) (assocSeqLength renv) then
    eqSeq elemCmp (assocSeq2seq lenv) (assocSeq2seq renv)
  else false
in

let unitNotLifted = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  unit_
])) in
(match typeLift unitNotLifted with (env, t) then
  utest env with assocSeqEmpty using eqEnv in
  utest t with unitNotLifted using eqExpr in
  ()
else never);

let noVariantsOrRecords = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (int_ 3),
  ulet_ "y" (int_ 2),
  ulet_ "z" (addi_ (var_ "x") (var_ "y")),
  var_ "z"
])) in
(match typeLift noVariantsOrRecords with (env, t) then
  utest env with assocSeqEmpty using eqEnv in
  utest t with noVariantsOrRecords using eqExpr in
  ()
else never);

let treeName = nameSym "Tree" in
let branchName = nameSym "Branch" in
let leafName = nameSym "Leaf" in
let variant = typeAnnot (symbolize (bindall_ [
  ntype_ treeName tyunknown_,
  ncondef_ branchName (tyarrow_ (tytuple_ [
    ntyvar_ treeName,
    ntyvar_ treeName]) (ntyvar_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntyvar_ treeName)),
  unit_
])) in
let expectedEnv = seq2assocSeq [
  (treeName, tyvariant_ [
    (branchName, tytuple_ [ntyvar_ treeName, ntyvar_ treeName]),
    (leafName, tyint_)
  ])
] in
(match typeLift variant with (env, t) then
  utest env with expectedEnv using eqEnv in
  utest t with unit_ using eqExpr in
  ()
else never);

let lastTerm = nconapp_ branchName (record_ [
  ("lhs", nconapp_ leafName (int_ 1)),
  ("rhs", nconapp_ leafName (int_ 2))
]) in
let variantWithRecords = typeAnnot (symbolize (bindall_ [
  ntype_ treeName (tyvariant_ []),
  ncondef_ branchName (tyarrow_ (tyrecord_ [
    ("lhs", ntyvar_ treeName),
    ("rhs", ntyvar_ treeName)]) (ntyvar_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntyvar_ treeName)),
  lastTerm
])) in
let expectedEnv = seq2assocSeq [
  (treeName, tyvariant_ [
    (branchName, tyrecord_ [("lhs", ntyvar_ treeName), ("rhs", ntyvar_ treeName)]),
    (leafName, tyint_)
  ]),
  (nameNoSym "Rec", tyrecord_ [
    ("lhs", ntyvar_ treeName), ("rhs", ntyvar_ treeName)
  ])
] in
(match typeLift variantWithRecords with (env, t) then
  utest env with expectedEnv using eqEnv in
  utest t with lastTerm using eqExpr in
  ()
else never);

let nestedRecord = typeAnnot (symbolize (bindall_ [
  ulet_ "r" (record_ [
    ("a", record_ [
      ("x", int_ 2),
      ("y", float_ 3.14),
      ("z", unit_)
    ]),
    ("b", int_ 7)
  ]),
  unit_
])) in
let expectedEnv = seq2assocSeq [
  (nameNoSym "Rec", tyrecord_ [
    ("x", tyint_),
    ("y", tyfloat_),
    ("z", tyunit_)
  ]),
  (nameNoSym "Rec", tyrecord_ [
    ("a", tyrecord_ [
      ("x", tyint_),
      ("y", tyfloat_),
      ("z", tyunit_)
    ]),
    ("b", tyint_)
  ])
] in
(match typeLift nestedRecord with (env, t) then
  utest env with expectedEnv using eqEnv in
  utest t with nestedRecord using eqExpr in
  ()
else never);

let recordsSameFieldsDifferentTypes = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (record_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (record_ [("a", int_ 2), ("b", true_)]),
  unit_
])) in
let expectedEnv = seq2assocSeq [
  (nameNoSym "Rec", tyrecord_ [("a", tyint_), ("b", tyint_)]),
  (nameNoSym "Rec", tyrecord_ [("a", tyint_), ("b", tybool_)])
] in
(match typeLift recordsSameFieldsDifferentTypes with (env, t) then
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsDifferentTypes using eqExpr in
  ()
else never);

let recordsSameFieldsSameTypes = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (record_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (record_ [("a", int_ 3), ("b", int_ 6)]),
  unit_
])) in
let expectedEnv = seq2assocSeq [
  (nameNoSym "Rec", tyrecord_ [("a", tyint_), ("b", tyint_)])
] in
(match typeLift recordsSameFieldsSameTypes with (env, t) then
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsSameTypes using eqExpr in
  ()
else never);

()
