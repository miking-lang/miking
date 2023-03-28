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
include "type-check.mc"
include "cmp.mc"

------------------------------
-- TYPE LIFTING ENVIRONMENT --
------------------------------

-- This type is added specifically for the type lifting to allow distinguishing
-- between variant types in the type environment before their constructors have
-- been added.
lang VariantNameTypeAst = Ast + Eq
  syn Type =
  | TyVariantName {ident : Name,
                   info : Info}

  sem tyWithInfo (info : Info) =
  | TyVariantName t -> TyVariantName {t with info = info}

  sem infoTy =
  | TyVariantName r -> r.info

  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyVariantName {ident = rid} ->
    match lhs with TyVariantName {ident = lid} then
      if nameEq lid rid then Some free else None ()
    else None ()

end

lang TypeLiftBase = MExprAst + VariantNameTypeAst
  type TypeLiftEnv = {
    -- Collects all type bindings encountered in the program in sequence.
    typeEnv: AssocSeq Name Type,

    -- Record types encountered so far. Uses intrinsic maps as this is
    -- performance critical.
    records: Map (Map SID Type) Name,

    -- Sequence types encountered so far. Uses intrinsic maps as this is
    -- performance critical.
    seqs: Map Type Name,

    -- Tensor types encountered so far.
    tensors : Map Type Name,

    -- Variant types and their constructors encountered so far.
    variants: Map Name (Map Name Type)
  }

  -- Replaces all variant type names with the variant type they represent. This
  -- function is called after going through the program, at which point all
  -- variant constructors have been identified.
  sem _replaceVariantNamesInTypeEnv =
  | env ->
    let env : TypeLiftEnv = env in
    let f = lam ty : Type.
      match ty with TyVariantName {ident = ident, info = info} then
        match mapLookup ident env.variants with Some constrs then
          TyVariant {constrs = constrs, info = info/-infoTy ty-/}
        else
          errorSingle [info] (join ["No variant type ", nameGetStr ident,
                                    " found in environment"])
      else ty
    in
    assocSeqMap f env.typeEnv
end

-- Define function for adding sequence types to environment
lang TypeLiftAddSeqToEnv = TypeLiftBase + SeqTypeAst + ConTypeAst
  sem addSeqToEnv (env: TypeLiftEnv) =
  | TySeq {info = info, ty = innerTy} & ty ->
    match mapLookup innerTy env.seqs with Some name then
      let tycon = nitycon_ name info in
      (env, tycon)
    else
      let name = nameSym "Seq" in
      let tycon = nitycon_ name info in
      let env = {{env with seqs = mapInsert innerTy name env.seqs}
                      with typeEnv = assocSeqInsert name ty env.typeEnv}
      in
      (env, tycon)
end

lang TypeLiftAddTensorToEnv = TypeLiftBase + TensorTypeAst + ConTypeAst
  sem addTensorToEnv (env : TypeLiftEnv) =
  | TyTensor {info = info, ty = innerTy} & ty ->
    match mapLookup innerTy env.tensors with Some name then
      let tycon = nitycon_ name info in
      (env, tycon)
    else
      let name = nameSym "Tensor" in
      let tycon = nitycon_ name info in
      let env = {{env with tensors = mapInsert innerTy name env.tensors}
                      with typeEnv = assocSeqInsert name ty env.typeEnv}
      in
      (env, tycon)
end

-----------
-- TERMS --
-----------

lang TypeLift = TypeLiftBase + Cmp

  sem addRecordToEnv (env : TypeLiftEnv) =
  -- Intentionally left blank

  sem typeLiftExpr (env : TypeLiftEnv) =
  | t ->
    -- Lift all sub-expressions
    match smapAccumL_Expr_Expr typeLiftExpr env t with (env, t) in
    -- Lift the contained types
    match smapAccumL_Expr_Type typeLiftType env t with (env, t) in
    -- Lift the annotated types
    smapAccumL_Expr_TypeLabel typeLiftType env t

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
      seqs = mapEmpty cmpType,
      tensors = mapEmpty cmpType,
      variants = mapEmpty nameCmp
    } in

    match typeLiftExpr emptyTypeLiftEnv e with (env, t) then
      let typeEnv = _replaceVariantNamesInTypeEnv env in
      (typeEnv, t)
    else never
end

lang TypeLiftAddRecordToEnv = TypeLift + RecordTypeAst
  sem addRecordToEnv (env : TypeLiftEnv) =
  | TyRecord {fields = fields, info = info} & ty ->
    switch mapLookup fields env.records
    case Some name then
      let tycon = nitycon_ name info in
      (env, tycon)
    case None _ then
      let name = nameSym "Rec" in
      let tycon = nitycon_ name info in
      let env = {{env
                  with records = mapInsert fields name env.records}
                  with typeEnv = assocSeqInsert name ty env.typeEnv}
      in
      (env, tycon)
    end
  -- | ty -> (env, ty) -- NOTE(dlunde,2021-10-06): I commented this out, so that it gives an error if a TyRecord is not supplied (less error-prone)
end

lang TypeTypeLift = TypeLift + TypeAst + VariantTypeAst + UnknownTypeAst +
                    VariantNameTypeAst + RecordTypeAst
  sem typeLiftExpr (env : TypeLiftEnv) =
  | TmType t ->
    let tyIdent =
      match t.tyIdent with TyUnknown t2 then tyWithInfo t2.info (tyvariant_ [])
      else t.tyIdent
    in
    match typeLiftType env tyIdent with (env, tyIdent) in
    let env : TypeLiftEnv = env in
    let env =
      -- Ignore any existing constructors in the variant type.
      match tyIdent with TyVariant {info = info} then
        let variantNameTy = TyVariantName {ident = t.ident, info = info} in
        {{env with variants = mapInsert t.ident (mapEmpty nameCmp) env.variants}
              with typeEnv = assocSeqInsert t.ident variantNameTy env.typeEnv}
      else match tyIdent
      with TyRecord {fields = fields} & ty then
        let f = lam env. lam. lam ty. typeLiftType env ty in
        match mapMapAccum f env fields with (env, _) in
        match addRecordToEnv env ty with (env, _) in
        env
      else {env with typeEnv = assocSeqInsert t.ident tyIdent env.typeEnv}
    in
    match typeLiftExpr env t.inexpr with (env, inexpr) in
    (env, inexpr)
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
      match inspectType t.tyIdent with TyArrow {from = from, to = to} then
        match unwrapTypeVarIdent to with Some ident then
          match typeLiftType env from with (env, from) then
            let f = lam variantMap. mapInsert t.ident from variantMap in
            let err = lam.
              errorSingle [t.info] (join ["Constructor ", nameGetStr t.ident,
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
    match typeLiftExpr env t.target with (env, target) in
    match typeLiftPat env t.pat with (env, pat) in
    match typeLiftExpr env t.thn with (env, thn) in
    match typeLiftExpr env t.els with (env, els) in
    match typeLiftType env t.ty with (env, ty) in
    (env, TmMatch {{{{{t with target = target}
                         with pat = pat}
                         with thn = thn}
                         with els = els}
                         with ty = ty})
end

-----------
-- TYPES --
-----------

lang RecordTypeTypeLift = TypeLift + RecordTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyRecord ({fields = fields} & r) & ty ->
    if eqi (mapLength fields) 0 then
      (env, ty)
    else
      let f = lam env. lam. lam ty. typeLiftType env ty in
      match mapMapAccum f env fields with (env, fields) then
        addRecordToEnv env (TyRecord {r with fields = fields})
      else never
end

-- Optional lifting of sequences (not added as default in MExprTypeLift)
lang SeqTypeTypeLift = TypeLift + SeqTypeAst + TypeLiftAddSeqToEnv
  sem typeLiftType (env : TypeLiftEnv) =
  | TySeq ({info = info, ty = innerTy} & r) & ty ->
    match typeLiftType env innerTy with (env, innerTy) then
      addSeqToEnv env (TySeq {r with ty = innerTy})
    else never
end

-- Type lifting, but leave strings = [char] intact (not added as default in MExprTypeLift).
lang SeqTypeNoStringTypeLift = SeqTypeTypeLift + CharTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TySeq {info = _, ty = TyChar _} & ty -> (env,ty)
end

-- Optional type lifting of tensors (not added to MExprTypeLift by default)
lang TensorTypeTypeLift = TypeLift + TensorTypeAst + TypeLiftAddTensorToEnv
  sem typeLiftType (env : TypeLiftEnv) =
  | TyTensor ({info = info, ty = innerTy} & r) ->
    match typeLiftType env innerTy with (env, innerTy) in
    addTensorToEnv env (TyTensor {r with ty = innerTy})
end

lang AppTypeTypeLift = TypeLift + AppTypeAst
  sem typeLiftType (env : TypeLiftEnv) =
  | TyApp t -> typeLiftType env t.lhs
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
  RecordTypeTypeLift + AppTypeTypeLift +

  TypeLiftAddRecordToEnv
end

lang TestLang =
  MExprTypeLift + SeqTypeTypeLift + MExprSym + MExprEq +
  MExprTypeCheck + MExprPrettyPrint
end

-- TODO(dlunde,2021-10-06): No tests for ordered records?

mexpr

use TestLang in

let fst : all a. all b. (a, b) -> a = lam x. x.0 in

let eqEnv = lam lenv. lam renv.
  use MExprEq in
  let elemCmp = lam l : (Name, Type). lam r : (Name, Type).
    and (nameEq l.0 r.0)
        (eqType l.1 r.1)
  in
  if eqi (length lenv) (length renv) then
    eqSeq elemCmp lenv renv
  else false
in

let unitNotLifted = typeCheck (symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  uunit_
])) in
match typeLift unitNotLifted with (env, t) in
utest env with [] using eqEnv in
utest t with unitNotLifted using eqExpr in

let noVariantsOrRecords = typeCheck (symbolize (bindall_ [
  ulet_ "x" (int_ 3),
  ulet_ "y" (int_ 2),
  ulet_ "z" (addi_ (var_ "x") (var_ "y")),
  var_ "z"
])) in
match typeLift noVariantsOrRecords with (env, t) in
utest env with [] using eqEnv in
utest t with noVariantsOrRecords using eqExpr in

let treeName = nameSym "Tree" in
let branchName = nameSym "Branch" in
let leafName = nameSym "Leaf" in
let variant = typeCheck (symbolize (bindall_ [
  ntype_ treeName [] (tyvariant_ []),
  ncondef_ branchName (tyarrow_ (tytuple_ [
    ntycon_ treeName,
    ntycon_ treeName]) (ntycon_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntycon_ treeName)),
  uunit_
])) in
match typeLift variant with (_, t) in
utest t with uunit_ using eqExpr in

let lastTerm =
  bind_
    (ulet_ "x" (nconapp_ branchName (urecord_ [
      ("lhs", nconapp_ leafName (int_ 1)),
      ("rhs", nconapp_ leafName (int_ 2))
    ]))) uunit_
in
let variantWithRecords = typeCheck (symbolize (bindall_ [
  ntype_ treeName [] (tyvariant_ []),
  ncondef_ branchName (tyarrow_ (tyrecord_ [
    ("lhs", ntycon_ treeName),
    ("rhs", ntycon_ treeName)]) (ntycon_ treeName)),
  ncondef_ leafName (tyarrow_ tyint_ (ntycon_ treeName)),
  lastTerm
])) in
match typeLift variantWithRecords with (env, t) in
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

let nestedRecord = typeCheck (symbolize (bindall_ [
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
match typeLift nestedRecord with (env, t) in
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

let nestedSeq = typeCheck (symbolize (bindall_ [
  ulet_ "s" (seq_ [seq_ [seq_ [int_ 2]], seq_ [seq_ [int_ 3]]]),
  uunit_
])) in
match typeLift nestedSeq with (env, t) in
let fstid = fst (get env 0) in
let sndid = fst (get env 1) in
let trdid = fst (get env 2) in
let expectedEnv = [
  (fstid, tyseq_ (ntycon_ sndid)),
  (sndid, tyseq_ (ntycon_ trdid)),
  (trdid, tyseq_ (tyint_))
] in
utest env with expectedEnv using eqEnv in
utest t with nestedSeq using eqExpr in

let recordsSameFieldsDifferentTypes = typeCheck (symbolize (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (urecord_ [("a", int_ 2), ("b", true_)]),
  uunit_
])) in
match typeLift recordsSameFieldsDifferentTypes with (env, t) in
let fstid = fst (get env 0) in
let sndid = fst (get env 1) in
let expectedEnv = [
  (fstid, tyrecord_ [("a", tyint_), ("b", tybool_)]),
  (sndid, tyrecord_ [("a", tyint_), ("b", tyint_)])
] in
utest env with expectedEnv using eqEnv in
utest t with recordsSameFieldsDifferentTypes using eqExpr in

let recordsSameFieldsSameTypes = typeCheck (symbolize (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  ulet_ "y" (urecord_ [("a", int_ 3), ("b", int_ 6)]),
  uunit_
])) in
match typeLift recordsSameFieldsSameTypes with (env, t) in
let recid = fst (get env 0) in
let expectedEnv = [
  (recid, tyrecord_ [("a", tyint_), ("b", tyint_)])
] in
utest env with expectedEnv using eqEnv in
utest t with recordsSameFieldsSameTypes using eqExpr in

let record = typeCheck (symbolize (urecord_ [
  ("a", int_ 2),
  ("b", float_ 1.5)
])) in
match typeLift record with (env, t) in
match tyTm t with TyCon {ident = ident} in
match assocSeqLookup {eq=nameEq} ident env with Some recordTy in
utest recordTy with tyTm record using eqType in

let recordUpdate = typeCheck (symbolize (bindall_ [
  ulet_ "x" (urecord_ [("a", int_ 0), ("b", int_ 1)]),
  recordupdate_ (var_ "x") "a" (int_ 2)
])) in
let recordType = tyrecord_ [("a", tyint_), ("b", tyint_)] in
match typeLift recordUpdate with (env, t) in
match t with TmLet {tyBody = TyCon {ident = ident}} in
match assocSeqLookup {eq=nameEq} ident env with Some ty in
utest ty with recordType using eqType in

let typeAliases = typeCheck (symbolize (bindall_ [
  type_ "GlobalEnv" [] (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "LocalEnv" [] (tyseq_ (tytuple_ [tystr_, tyint_])),
  type_ "Env" [] (tyrecord_ [
    ("global", tycon_ "GlobalEnv"),
    ("local", tycon_ "LocalEnv")
  ]),
  ulet_ "env" (urecord_ [
    ("global", seq_ [utuple_ [str_ "x", int_ 4]]),
    ("local", seq_ [utuple_ [str_ "a", int_ 0]])
  ]),
  var_ "env"
])) in
match typeLift typeAliases with (env, t) in
-- Note that records and variants are added to the front of the environment
-- as they are processed, so the last record in the given term will be first
-- in the environment.
let ids = map fst env in
let fstSeqId = get ids 6 in    -- type Seq1 = [Char]
let fstRecordId = get ids 5 in -- type Rec1 = {0 : Seq1, 1 : Int}
let sndSeqId = get ids 4 in    -- type Seq2 = [Rec1]
let globalEnvId = get ids 3 in -- type GlobalEnv = Seq2
let localEnvId = get ids 2 in  -- type LocalEnv = Seq2
let sndRecordId = get ids 1 in -- type Rec2 = {global : Seq2, local : Seq2}
let envId = get ids 0 in       -- type Env = Rec2
let expectedEnv = [
  (envId, ntycon_ sndRecordId),
  (sndRecordId, tyrecord_ [
    ("local", ntycon_ sndSeqId),
    ("global", ntycon_ sndSeqId)
  ]),
  (localEnvId, ntycon_ sndSeqId),
  (globalEnvId, ntycon_ sndSeqId),
  (sndSeqId, tyseq_ (ntycon_ fstRecordId)),
  (fstRecordId, tytuple_ [ntycon_ fstSeqId, tyint_]),
  (fstSeqId, tystr_)
] in
utest env with expectedEnv using eqEnv in

let tupleTy = tytuple_ [tyint_, tyint_] in
let recordTypeInBindingAnnotation = symbolize (bindall_ [
  reclet_ "gcd" (tyarrow_ tupleTy tyint_)
    (ulam_ "x" (bindall_ [
      ulet_ "a" (tupleproj_ 0 (var_ "x")),
      ulet_ "b" (tupleproj_ 1 (var_ "x")),
      if_ (eqi_ (var_ "b") (int_ 0))
        (var_ "a")
        (app_ (var_ "gcd") (utuple_ [var_ "b", modi_ (var_ "a") (var_ "b")]))])),
  app_ (var_ "gcd") (utuple_ [int_ 7, int_ 14])
]) in
match typeLift recordTypeInBindingAnnotation with (env, t) in
utest length env with 1 using eqi in

()
