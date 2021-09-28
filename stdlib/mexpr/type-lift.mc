-- Lift out types of an MExpr program. In particular, record types are lifted
-- and replaced with type variables, and all constructors for variant types are
-- lifted and collected into a single type.  Note that the latter probably has
-- consequences for type checking: information is lost when lifting constructor
-- definitions.
--
-- Requires symbolize and type-annot to be run first.
include "assoc-seq.mc"
include "map.mc"
include "set.mc"
include "name.mc"
include "stringid.mc"

include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "symbolize.mc"
include "type-annot.mc"
include "cmp.mc"

------------------------------
-- TYPE LIFTING ENVIRONMENT --
------------------------------

type TypeLiftEnv = {

  -- Collects all type bindings encountered in the program in sequence.
  typeEnv: AssocSeq Name Type,

  -- Record types encountered so far. Uses intrinsic maps as this is
  -- performance critical.
  records: Map (Map SID Type) Name,

  labels: Set [SID],

  -- Variant types and their constructors encountered so far.
  variants: Map Name (Map Name Type)

}

-- This type is added specifically for the type lifting to allow distinguishing
-- between variant types in the type environment before their constructors have
-- been added.
lang VariantNameTypeAst = Eq
  syn Type =
  | TyVariantName {ident : Name}

  sem eqTypeH (typeEnv : TypeEnv) (lhs : Type) =
  | TyVariantName {ident = rid} ->
    match lhs with TyVariantName {ident = lid} then
      nameEq lid rid
    else false

end

-- Replaces all variant type names with the variant type they represent. This
-- function is called after going through the program, at which point all
-- variant constructors have been identified.
let _replaceVariantNamesInTypeEnv = lam env : TypeLiftEnv.
  use VariantTypeAst in
  use VariantNameTypeAst in
  let f = lam ty : Type.
    match ty with TyVariantName {ident = ident} then
      match mapLookup ident env.variants with Some constrs then
        TyVariant {constrs = constrs, info = NoInfo ()}
      else
        error (join ["No variant type ", nameGetStr ident,
                     " found in environment"])
    else ty
  in
  assocSeqMap f env.typeEnv


let _addRecordToEnv =
  use MExprAst in
  lam env : TypeLiftEnv. lam name : Option Name. lam ty : Type.
  match ty with TyRecord {fields = fields, labels = labels, info = info} then
    match name with Some name then
      let tyvar = TyCon {ident = name, info = info} in
      (env, tyvar)
    else match name with None _ then
      let name = nameSym "Rec" in
      let tyvar = TyCon {ident = name, info = info} in
      let env = {{{env
                    with records = mapInsert fields name env.records}
                    with labels = setInsert labels env.labels}
                    with typeEnv = assocSeqInsert name ty env.typeEnv}
      in
      (env, tyvar)
    else never
  else error "Expected record type"

-- This implementation takes record field order into account when populating
-- the environment
lang TypeLiftAddRecordToEnvOrdered = RecordTypeAst
  sem addRecordToEnv (env : TypeLiftEnv) =
  | TyRecord {fields = fields, labels = labels, info = info} & ty ->
    match (mapLookup fields env.records, setMem labels env.labels)
    with (name, true) then
      _addRecordToEnv env name ty
    else
      _addRecordToEnv env (None ()) ty
  | ty -> (env, ty)
end

-- This implementation does not take record field order into account when
-- populating the environment
lang TypeLiftAddRecordToEnvUnOrdered = RecordTypeAst
  sem addRecordToEnv (env : TypeLiftEnv) =
  | TyRecord {fields = fields, labels = labels, info = info} & ty ->
    _addRecordToEnv
      env (mapLookup fields env.records) ty
  | ty -> (env, ty)
end

-----------
-- TERMS --
-----------

lang TypeLift = Cmp

  sem addRecordToEnv (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftExpr (env : TypeLiftEnv) =
  | t ->
    -- Lift all sub-expressions
    match smapAccumL_Expr_Expr typeLiftExpr env t with (env, t) then
      -- Lift the contained types
      match smapAccumL_Expr_Type typeLiftType env t with (env, t) then
        -- Lift the annotated type
        match typeLiftType env (ty t) with (env, ty) then
          (env, withType ty t)
        else never
      else never
    else never

  sem typeLiftType (env : TypeLiftEnv) =
  | t -> smapAccumL_Type_Type typeLiftType env t

  sem typeLiftPat (env : TypeLiftEnv) =
  | t ->
    match smapAccumL_Pat_Pat typeLiftPat env t with (env, t) then
      match typeLiftType env (tyPat t) with (env, ty) then
        (env, withTypePat ty t)
      else never
    else never

  -- Lifts all records, variants and type aliases from the given expression
  -- `e`. The result is returned as an environment containing tuples of names
  -- and their corresponding types, together with a modified version of the
  -- expression `e` where:
  -- * `TmType`s and `TmConDef`s have been removed.
  -- * `TyRecord`s have been replaced with a `TyCon` whose name is
  --   contained in the resulting environment.
  -- * The constructor names and argument types have been added to the
  --   `TyVariant`s.
  sem typeLift = -- Expr -> (AssocSeq Name Type, Expr)
  | e ->

    let emptyTypeLiftEnv : TypeLiftEnv = {
      typeEnv = [],
      records = mapEmpty (mapCmp cmpType),
      labels = setEmpty (seqCmp cmpSID),
      variants = mapEmpty nameCmp
    } in

    match typeLiftExpr emptyTypeLiftEnv e with (env, t) then
      let typeEnv = _replaceVariantNamesInTypeEnv env in
      (typeEnv, t)
    else never
end

lang TypeTypeLift = TypeLift + TypeAst + VariantTypeAst + UnknownTypeAst +
                    VariantNameTypeAst + RecordTypeAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmType t ->
    let tyIdent =
      match t.tyIdent with TyUnknown _ then tyvariant_ []
      else t.tyIdent
    in
    match typeLiftType env tyIdent with (env, tyIdent) then
      let env : TypeLiftEnv = env in
      let env =
        -- Ignore any existing constructors in the variant type.
        match tyIdent with TyVariant _ then
          let variantNameTy = TyVariantName {ident = t.ident} in
          {{env with variants = mapInsert t.ident (mapEmpty nameCmp) env.variants}
                with typeEnv = assocSeqInsert t.ident variantNameTy env.typeEnv}
        else match tyIdent
        with TyRecord {fields = fields} & ty then
          let f = lam env. lam. lam ty. typeLiftType env ty in
          match mapMapAccum f env fields with (env, fields) then
            match addRecordToEnv env ty with (env, _) then
              env
            else never
          else never
        else {env with typeEnv = assocSeqInsert t.ident tyIdent env.typeEnv}
      in
      match typeLiftExpr env t.inexpr with (env, inexpr) then
        (env, inexpr)
      else never
    else never
end

lang DataTypeLift = TypeLift + DataAst + FunTypeAst + ConTypeAst + AppTypeAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmConDef t ->
    recursive let unwrapTypeVarIdent = lam ty : Type.
      match ty with TyCon t then Some t.ident
      else match ty with TyApp t then unwrapTypeVarIdent t.lhs
      else None ()
    in
    let env =
      match t.tyIdent with TyArrow {from = from, to = to} then
        match unwrapTypeVarIdent to with Some ident then
          match typeLiftType env from with (env, from) then
            let f = lam variantMap. mapInsert t.ident from variantMap in
            let err = lam.
              error (join ["Constructor ", nameGetStr t.ident,
                           " defined before referenced variant type ",
                           nameGetStr ident])
            in
            let env : TypeLiftEnv = env in
            let variantMap = mapLookupApplyOrElse f err ident env.variants in
            {env with variants = mapInsert ident variantMap env.variants}
          else never
        else env
      else env
    in
    match typeLiftExpr env t.inexpr with (env, inexpr) then
      (env, inexpr)
    else never
end

lang MatchTypeLift = TypeLift + MatchAst + RecordPat + RecordTypeAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmMatch t ->
    match typeLiftExpr env t.target with (env, target) then
      match typeLiftPat env t.pat with (env, pat) then
        match typeLiftExpr env t.thn with (env, thn) then
          match typeLiftExpr env t.els with (env, els) then
            match typeLiftType env t.ty with (env, ty) then
              (env, TmMatch {{{{{t with target = target}
                                   with pat = pat}
                                   with thn = thn}
                                   with els = els}
                                   with ty = ty})
            else never
          else never
        else never
      else never
    else never
end

-----------
-- TYPES --
-----------

lang RecordTypeTypeLift = TypeLift + RecordTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyRecord ({fields = fields} & r) & ty->
    if eqi (mapLength fields) 0 then
      (env, ty)
    else
      let f = lam env. lam. lam ty. typeLiftType env ty in
      match mapMapAccum f env fields with (env, fields) then
        addRecordToEnv env (TyRecord {r with fields = fields})
      else never
end

lang AppTypeTypeLift = TypeLift + AppTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyApp t ->
    match typeLiftType env t.lhs with (env, lhs) then
      (env, lhs)
    else never
end

lang MExprTypeLift =
  -- Compare
  MExprCmp +

  -- Default implementations (Terms)
  VarAst + AppAst + LamAst + LetAst + RecLetsAst + ConstAst + SeqAst +
  UtestAst + NeverAst + ExtAst +

  -- Default implementations (Types)
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + TensorTypeAst + VariantTypeAst + ConTypeAst +
  VariantNameTypeAst +

  -- Non-default implementations (Terms)
  TypeTypeLift + DataTypeLift + MatchTypeLift +

  -- Non-default implementations (Types)
  RecordTypeTypeLift + AppTypeTypeLift
end

lang MExprTypeLiftOrderedRecordsCmpClosed =
  MExprTypeLift + TypeLiftAddRecordToEnvOrdered + MExprCmp
lang MExprTypeLiftUnOrderedRecords =
  MExprTypeLift + TypeLiftAddRecordToEnvUnOrdered
lang MExprTypeLiftUnOrderedRecordsCmpClosed =
  MExprTypeLiftUnOrderedRecords + MExprCmp

lang TestLang =
  MExprTypeLiftUnOrderedRecordsCmpClosed + MExprSym + MExprTypeAnnot +
  MExprPrettyPrint

mexpr

use TestLang in

let fst = lam x: (a, b). x.0 in

let eqType : EqTypeEnv -> Type -> Type -> Bool =
  lam env. lam l : Type. lam r : Type.
  eqType env l r
in

let eqEnv = lam lenv : EqTypeEnv. lam renv : EqTypeEnv.
  use MExprEq in
  let elemCmp = lam l : (Name, Type). lam r : (Name, Type).
    and (nameEq l.0 r.0)
        (eqType l.1 r.1)
  in
  if eqi (length lenv) (length renv) then
    eqSeq elemCmp lenv renv
  else false
in

let unitNotLifted = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  uunit_
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
    ntycon_ treeName,
    ntycon_ treeName]) (ntycon_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntycon_ treeName)),
  uunit_
])) in
(match typeLift variant with (_, t) then
  utest t with uunit_ using eqExpr in
  ()
else never);

let lastTerm = nconapp_ branchName (urecord_ [
  ("lhs", nconapp_ leafName (int_ 1)),
  ("rhs", nconapp_ leafName (int_ 2))
]) in
let variantWithRecords = typeAnnot (symbolize (bindall_ [
  ntype_ treeName (tyvariant_ []),
  ncondef_ branchName (tyarrow_ (tyrecord_ [
    ("lhs", ntycon_ treeName),
    ("rhs", ntycon_ treeName)]) (ntycon_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntycon_ treeName)),
  lastTerm
])) in
(match typeLift variantWithRecords with (env, t) then
  let recid = fst (get env 0) in
  let expectedEnv = [
    (recid, tyrecord_ [
      ("lhs", ntycon_ treeName), ("rhs", ntycon_ treeName)
    ]),
    (treeName, tyvariant_ [
      (branchName, ntycon_ recid),
      (leafName, tyint_)
    ])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with lastTerm using eqExpr in
  ()
else never);

let nestedRecord = typeAnnot (symbolize (bindall_ [
  ulet_ "r" (urecord_ [
    ("a", urecord_ [
      ("x", int_ 2),
      ("y", float_ 3.14),
      ("z", uunit_)
    ]),
    ("b", int_ 7)
  ]),
  uunit_
])) in
(match typeLift nestedRecord with (env, t) then
  let fstid = fst (get env 0) in
  let sndid = fst (get env 1) in
  let expectedEnv = [
    (fstid, tyrecord_ [
      ("a", ntycon_ sndid),
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
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (urecord_ [("a", int_ 2), ("b", true_)]),
  uunit_
])) in
(match typeLift recordsSameFieldsDifferentTypes with (env, t) then
  let fstid = fst (get env 0) in
  let sndid = fst (get env 1) in
  let expectedEnv = [
    (fstid, tyrecord_ [("a", tyint_), ("b", tybool_)]),
    (sndid, tyrecord_ [("a", tyint_), ("b", tyint_)])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsDifferentTypes using eqExpr in
  ()
else never);

let recordsSameFieldsSameTypes = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (urecord_ [("a", int_ 3), ("b", int_ 6)]),
  uunit_
])) in
(match typeLift recordsSameFieldsSameTypes with (env, t) then
  let recid = fst (get env 0) in
  let expectedEnv = [
    (recid, tyrecord_ [("a", tyint_), ("b", tyint_)])
  ] in
  utest env with expectedEnv using eqEnv in
  utest t with recordsSameFieldsSameTypes using eqExpr in
  ()
else never);

let record = typeAnnot (symbolize (urecord_ [
  ("a", int_ 2),
  ("b", float_ 1.5)
])) in
(match typeLift record with (env, t) then
  match ty t with TyCon {ident = ident} then
    match assocSeqLookup {eq=nameEq} ident env with Some recordTy then
      utest recordTy with ty record using eqType in
      ()
    else never
  else never
else never);

let recordUpdate = typeAnnot (symbolize (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  recordupdate_ (var_ "x") "a" (int_ 2)
])) in
let recordType = tyrecord_ [("a", tyint_), ("b", tyint_)] in
(match typeLift recordUpdate with (env, t) then
  match t with TmLet {tyBody = TyCon {ident = ident}} then
    match assocSeqLookup {eq=nameEq} ident env with Some ty then
      utest ty with recordType using eqType in
      ()
    else never
  else never
else never);

let typeAliases = typeAnnot (symbolize (bindall_ [
  type_ "GlobalEnv" (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "LocalEnv" (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "Env" (tyrecord_ [
    ("global", tycon_ "GlobalEnv"),
    ("local", tycon_ "LocalEnv")
  ]),
  ulet_ "env" (urecord_ [
    ("global", seq_ [utuple_ [str_ "x", int_ 4]]),
    ("local", seq_ [utuple_ [str_ "a", int_ 0]])
  ]),
  var_ "env"
])) in
(match typeLift typeAliases with (env, t) then
  -- Note that records and variants are added to the front of the environment
  -- as they are processed, so the last record in the given term will be first
  -- in the environment.
  let ids = map (lam p: (a, b). p.0) env in
  let fstRecordId = get ids 5 in -- type Rec1 = {0 : [Char], 1 : Int}
  let globalEnvId = get ids 4 in -- type GlobalEnv = [Rec1]
  let localEnvId = get ids 3 in  -- type LocalEnv = [Rec1]
  let sndRecordId = get ids 2 in -- type Rec2 = {global : GlobalEnv, local : LocalEnv}
  let envId = get ids 1 in       -- type Env = Rec2
  let trdRecordId = get ids 0 in -- type Rec3 = {global : [Rec1], local : [Rec1]}
  let expectedEnv = [
    (trdRecordId, tyrecord_ [
      ("local", tyseq_ (ntycon_ fstRecordId)),
      ("global", tyseq_ (ntycon_ fstRecordId))
    ]),
    (envId, ntycon_ sndRecordId),
    (sndRecordId, tyrecord_ [
      ("local", ntycon_ localEnvId),
      ("global", ntycon_ globalEnvId)
    ]),
    (localEnvId, tyseq_ (ntycon_ fstRecordId)),
    (globalEnvId, tyseq_ (ntycon_ fstRecordId)),
    (fstRecordId, tytuple_ [tystr_, tyint_])
  ] in
  utest env with expectedEnv using eqEnv in
  ()
else never);

()
