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

-- Adds a record type with the given fields to the type lifting environment.
let _addRecordTypeVar = lam env. lam fields.
  use MExprAst in
  let record = TyRecord {fields = fields} in
  let recName = nameSym "Rec" in
  let recTyVar = ntyvar_ recName in
  let env = {{env with records = mapInsert fields recName env.records}
                  with typeEnv = assocSeqInsert recName record env.typeEnv} in
  (env, recTyVar)

-----------
-- TERMS --
-----------

lang TypeLift = MExprEq
  sem typeLiftExpr (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  -- Lifts all records, variants and type aliases from the given expression
  -- `e`. The result is returned as an environment containing tuples of names
  -- and their corresponding types, together with a modified version of the
  -- expression `e` where:
  -- * `TmType`s and `TmConDef`s have been removed.
  -- * `TyRecord`s have been replaced with a `TyVar` whose name is
  --   contained in the resulting environment.
  -- * The constructor names and argument types have been added to the
  --   `TyVariant`s.
  sem typeLift = -- Expr -> (AssocSeq Name Type, Expr)
  | e ->
    let emptyEnv = {
      typeEnv = [],
      records = mapEmpty (mapCmp _cmpType),
      variants = mapEmpty nameCmp
    } in
    match typeLiftExpr emptyEnv e with (env, t) then
      let typeEnv = _replaceVariantNamesInTypeEnv env in
      (typeEnv, t)
    else never
end

lang VarTypeLift = TypeLift + VarAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmVar t ->
    match typeLiftType env t.ty with (env, ty) then
      (env, TmVar {t with ty = ty})
    else never
end

lang AppTypeLift = TypeLift + AppAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmApp t ->
    match typeLiftExpr env t.lhs with (env, lhs) then
      match typeLiftExpr env t.rhs with (env, rhs) then
        match typeLiftType env t.ty with (env, ty) then
          (env, TmApp {{{t with lhs = lhs}
                           with rhs = rhs}
                           with ty = ty})
        else never
      else never
    else never
end

lang LamTypeLift = TypeLift + LamAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmLam t ->
    match typeLiftType env t.tyIdent with (env, tyIdent) then
      match typeLiftExpr env t.body with (env, body) then
        match typeLiftType env t.ty with (env, ty) then
          (env, TmLam {{{t with tyIdent = tyIdent}
                           with body = body}
                           with ty = ty})
        else never
      else never
    else never
end

lang LetTypeLift = TypeLift + LetAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmLet t ->
    match typeLiftExpr env t.body with (env, body) then
      match typeLiftType env t.tyBody with (env, tyBody) then
        match typeLiftExpr env t.inexpr with (env, inexpr) then
          match typeLiftType env t.ty with (env, ty) then
            (env, TmLet {{{{t with body = body}
                              with tyBody = tyBody}
                              with inexpr = inexpr}
                              with ty = ty})
          else never
        else never
      else never
    else never
end

lang RecLetsTypeLift = TypeLift + RecLetsAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmRecLets t ->
    let f = lam env. lam binding. typeLiftExpr env binding.body in
    match mapAccumL f env t.bindings with (env, bindings) then
      match typeLiftExpr env t.inexpr with (env, inexpr) then
        match typeLiftType env t.ty with (env, ty) then
          (env, TmRecLets {{{t with bindings = bindings}
                               with inexpr = inexpr}
                               with ty = ty})
        else never
      else never
    else never
end

lang ConstTypeLift = TypeLift + ConstAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmConst t ->
    match typeLiftType env t.ty with (env, ty) then
      (env, TmConst {t with ty = ty})
    else never
end

lang SeqTypeLift = TypeLift + SeqAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmSeq t ->
    match mapAccumL typeLiftExpr env t.tms with (env, tms) then
      match typeLiftType env t.ty with (env, ty) then
        (env, TmSeq {{t with tms = tms}
                        with ty = ty})
      else never
    else never
end

lang RecordTypeLift = TypeLift + RecordAst
  sem typeLiftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmRecord t ->
    let f = lam env. lam. lam v. typeLiftExpr env v in
    match mapMapAccum f env t.bindings with (env, bindings) then
      match typeLiftType env t.ty with (env, ty) then
        (env, TmRecord {{t with bindings = bindings}
                           with ty = ty})
      else never
    else never
  | TmRecordUpdate t ->
    match typeLiftExpr env t.rec with (env, rec) then
      match typeLiftExpr env t.value with (env, value) then
        match typeLiftType env t.ty with (env, ty) then
          (env, TmRecordUpdate {{{t with rec = rec}
                                    with value = value}
                                    with ty = ty})
        else never
      else never
    else never
end

lang TypeTypeLift = TypeLift + TypeAst + VariantTypeAst + UnknownTypeAst +
                    VariantNameTypeAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmType t ->
    let tyIdent =
      match t.tyIdent with TyUnknown {} then tyvariant_ []
      else t.tyIdent
    in
    match typeLiftType env tyIdent with (env, tyIdent) then
      let env =
        -- Ignore any existing constructors in the variant type.
        match tyIdent with TyVariant _ then
          let variantNameTy = TyVariantName {ident = t.ident} in
          {{env with variants = mapInsert t.ident (mapEmpty nameCmp) env.variants}
                with typeEnv = assocSeqInsert t.ident variantNameTy env.typeEnv}
        else match tyIdent with TyRecord {fields = fields} then
          let f = lam env. lam. lam ty. typeLiftType env ty in
          match mapMapAccum f env fields with (env, fields) then
            match _addRecordTypeVar env fields with (env, _) then
              env
            else never
          else never
        else
          {env with typeEnv = assocSeqInsert t.ident tyIdent env.typeEnv}
      in
      match typeLiftExpr env t.inexpr with (env, inexpr) then
        (env, inexpr)
      else never
    else never
end

lang DataTypeLift = TypeLift + DataAst + FunTypeAst + VarTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftExpr (env : TypeLiftEnv) =
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
    match typeLiftExpr env t.inexpr with (env, inexpr) then
      (env, inexpr)
    else never
  | TmConApp t ->
    match typeLiftExpr env t.body with (env, body) then
      match typeLiftType env t.ty with (env, ty) then
        (env, TmConApp {{t with body = body}
                           with ty = ty})
      else never
    else never
end

lang MatchTypeLift = TypeLift + MatchAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmMatch t ->
    match typeLiftExpr env t.target with (env, target) then
      match typeLiftExpr env t.thn with (env, thn) then
        match typeLiftExpr env t.els with (env, els) then
          match typeLiftType env t.ty with (env, ty) then
            (env, TmMatch {{{{t with target = target}
                                with thn = thn}
                                with els = els}
                                with ty = ty})
          else never
        else never
      else never
    else never
end

lang UtestTypeLift = TypeLift + UtestAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmUtest t ->
    match typeLiftExpr env t.test with (env, test) then
      match typeLiftExpr env t.expected with (env, expected) then
        match typeLiftExpr env t.next with (env, next) then
          match typeLiftType env t.ty with (env, ty) then
            (env, TmUtest {{{{t with test = test}
                                with expected = expected}
                                with next = next}
                                with ty = ty})
          else never
        else never
      else never
    else never
end

lang NeverTypeLift = TypeLift + NeverAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmNever t ->
    match typeLiftType env t.ty with (env, ty) then
      (env, TmNever {t with ty = ty})
    else never
end

-----------
-- TYPES --
-----------

lang UnknownTypeTypeLift = TypeLift + UnknownTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyUnknown {} -> (env, TyUnknown {})
end

lang BoolTypeTypeLift = TypeLift + BoolTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyBool {} -> (env, TyBool {})
end

lang IntTypeTypeLift = TypeLift + IntTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyInt {} -> (env, TyInt {})
end

lang FloatTypeTypeLift = TypeLift + FloatTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyFloat {} -> (env, TyFloat {})
end

lang CharTypeTypeLift = TypeLift + CharTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyChar {} -> (env, TyChar {})
end

lang FunTypeTypeLift = TypeLift + FunTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyArrow t ->
    match typeLiftType env t.from with (env, from) then
      match typeLiftType env t.to with (env, to) then
        (env, TyArrow {from = from, to = to})
      else never
    else never
end

lang SeqTypeTypeLift = TypeLift + SeqTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TySeq t ->
    match typeLiftType env t.ty with (env, ty) then
      (env, TySeq {ty = ty})
    else never
end

lang RecordTypeTypeLift = TypeLift + RecordTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyRecord t & ty ->
    if eqi (mapLength t.fields) 0 then
      (env, ty)
    else
      let f = lam env. lam. lam ty. typeLiftType env ty in
      match mapMapAccum f env t.fields with (env, fields) then
        match mapLookup fields env.records with Some name then
          (env, ntyvar_ name)
        else
          _addRecordTypeVar env fields
      else never
end

lang VariantTypeTypeLift = TypeLift + VariantTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyVariant t -> (env, TyVariant t)
end

lang VarTypeTypeLift = TypeLift + VarTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyVar t -> (env, TyVar t)
end

lang AppTypeTypeLift = TypeLift + AppTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyApp t ->
    match typeLiftType env t.lhs with (env, lhs) then
      match typeLiftType env t.rhs with (env, rhs) then
        (env, TyApp {lhs = lhs, rhs = rhs})
      else never
    else never
end

lang VariantNameTypeTypeLift = TypeLift + VariantNameTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
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
    and (nameEq l.0 r.0)
        (eqType [] l.1 r.1)
  in
  if eqi (length lenv) (length renv) then
    eqSeq elemCmp lenv renv
  else false
in

let unitNotLifted = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  unit_
])) in
(match typeLift unitNotLifted with (env, t) then
  utest env with [] using eqEnv in
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
  utest env with [] using eqEnv in
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
let expectedEnv = [
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
(match typeLift variantWithRecords with (env, t) then
  let recid = (get env 0).0 in
  let expectedEnv = [
    (recid, tyrecord_ [
      ("lhs", ntyvar_ treeName), ("rhs", ntyvar_ treeName)
    ]),
    (treeName, tyvariant_ [
      (branchName, tyrecord_ [("lhs", ntyvar_ treeName), ("rhs", ntyvar_ treeName)]),
      (leafName, tyint_)
    ])
  ] in
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
(match typeLift nestedRecord with (env, t) then
  let fstid = (get env 0).0 in
  let sndid = (get env 1).0 in
  let expectedEnv = [
    (fstid, tyrecord_ [
      ("a", ntyvar_ sndid),
      ("b", tyint_)
    ]),
    (sndid, tyrecord_ [
      ("x", tyint_),
      ("y", tyfloat_),
      ("z", tyunit_)
    ])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with nestedRecord using eqExpr in
  ()
else never);

let recordsSameFieldsDifferentTypes = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (record_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (record_ [("a", int_ 2), ("b", true_)]),
  unit_
])) in
(match typeLift recordsSameFieldsDifferentTypes with (env, t) then
  let fstid = (get env 0).0 in
  let sndid = (get env 1).0 in
  let expectedEnv = [
    (fstid, tyrecord_ [("a", tyint_), ("b", tybool_)]),
    (sndid, tyrecord_ [("a", tyint_), ("b", tyint_)])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsDifferentTypes using eqExpr in
  ()
else never);

let recordsSameFieldsSameTypes = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (record_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (record_ [("a", int_ 3), ("b", int_ 6)]),
  unit_
])) in
(match typeLift recordsSameFieldsSameTypes with (env, t) then
  let recid = (get env 0).0 in
  let expectedEnv = [
    (recid, tyrecord_ [("a", tyint_), ("b", tyint_)])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsSameTypes using eqExpr in
  ()
else never);

let record = typeAnnot (symbolize (record_ [
  ("a", int_ 2),
  ("b", float_ 1.5)
])) in
(match typeLift record with (env, t) then
  match ty t with TyVar {ident = ident} then
    match assocSeqLookup {eq=nameEq} ident env with Some recordTy then
      utest recordTy with ty record using eqType [] in
      ()
    else never
  else never
else never);

let recordUpdate = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (record_ [("a", int_ 0), ("b", int_ 1)]),
  recordupdate_ (var_ "x") "a" (int_ 2)
])) in
let recordType = tyrecord_ [("a", tyint_), ("b", tyint_)] in
(match typeLift recordUpdate with (env, t) then
  match t with TmLet {tyBody = TyVar {ident = ident}} then
    match assocSeqLookup {eq=nameEq} ident env with Some ty then
      utest ty with recordType using eqType [] in
      ()
    else never
  else never
else never);

let typeAliases = typeAnnot (symbolize (bindall_ [
  type_ "GlobalEnv" (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "LocalEnv" (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "Env" (tyrecord_ [
    ("global", tyvar_ "GlobalEnv"),
    ("local", tyvar_ "LocalEnv")
  ]),
  ulet_ "env" (record_ [
    ("global", seq_ [tuple_ [str_ "x", int_ 4]]),
    ("local", seq_ [tuple_ [str_ "a", int_ 0]])
  ]),
  var_ "env"
])) in
(match typeLift typeAliases with (env, t) then
  -- Note that records and variants are added to the front of the environment
  -- as they are processed, so the last record in the given term will be first
  -- in the environment.
  let ids = map (lam p. p.0) env in
  let fstRecordId = get ids 5 in -- type Rec1 = {0 : [Char], 1 : Int}
  let globalEnvId = get ids 4 in -- type GlobalEnv = [Rec1]
  let localEnvId = get ids 3 in  -- type LocalEnv = [Rec1]
  let sndRecordId = get ids 2 in -- type Rec2 = {global : GlobalEnv, local : LocalEnv}
  let envId = get ids 1 in       -- type Env = Rec2
  let trdRecordId = get ids 0 in -- type Rec3 = {global : [Rec1], local : [Rec1]}
  let expectedEnv = [
    (trdRecordId, tyrecord_ [
      ("local", tyseq_ (ntyvar_ fstRecordId)),
      ("global", tyseq_ (ntyvar_ fstRecordId))
    ]),
    (envId, ntyvar_ sndRecordId),
    (sndRecordId, tyrecord_ [
      ("local", ntyvar_ localEnvId),
      ("global", ntyvar_ globalEnvId)
    ]),
    (localEnvId, tyseq_ (ntyvar_ fstRecordId)),
    (globalEnvId, tyseq_ (ntyvar_ fstRecordId)),
    (fstRecordId, tytuple_ [tystr_, tyint_])
  ] in
  utest env with expectedEnv using eqEnv in
  ()
else never);

()
