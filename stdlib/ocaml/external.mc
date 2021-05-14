include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst + AppTypeAst

-- Computes the cost `Int` of marshaling data from `Type` to `Type`.
let externalMarshalCost : Type -> Type -> Int =
  use OCamlMarshalData in
  recursive let recur = lam ty1. lam ty2.
    let tt = (ty1, ty2) in
    match tt with (TyVar _, _) | (_, TyVar _) | (TyApp _, _) | (_, TyApp _)
    then 0
    else match tt with (TyInt _, TyInt _) | (TyFloat _, TyFloat _) then 0
    else match tt with (TySeq _, TySeq _) then 0
    else match tt with (OTyList _, OTyList _) then 0
    else match tt with (TySeq _, OTyList _) then 5
    else match tt with (OTyList _, TySeq _) then 5
    else match tt with (OTyArray _, OTyArray _) then 0
    else match tt with (OTyArray _, TySeq _) then 2
    else match tt with (TySeq _, OTyArray _) then 2
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then 0
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then 0
    else match tt with
      (TyTensor {ty = TyInt _}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then 2
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyInt _})
    then 1
    else match tt with
      (TyTensor {ty = TyFloat _}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then 2
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyFloat _})
    then 1
    else match tt
    with (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      addi (recur ty21 ty11) (recur ty12 ty22)
    else error "Cannot compute marshal cost"
  in
  recur

utest externalMarshalCost tyint_ tyint_ with 0
utest externalMarshalCost (otylist_ tyint_) (tyseq_ tyint_) with 3
utest
  externalMarshalCost
    (tyarrow_ (tyseq_ tyint_) (otylist_ tyint_))
    (tyarrow_ (otylist_ tyint_) (tyseq_ tyint_))
with 6
utest
  externalMarshalCost
    (tyarrows_ [tyseq_ tyint_, otylist_ tyint_, tyseq_ tyint_])
    (tyarrows_ [otylist_ tyint_, tyseq_ tyint_, otylist_ tyint_])
with 9


-- Marshals expression `Exp` of type `Type` to expression `Expr` of type
-- `Type`.
let externalMarshal : Expr -> Type -> Type -> Expr =
  use OCamlMarshalData in
  lam t. lam ty1. lam ty2.
  recursive let recur = lam t. lam ty1. lam ty2.
    let tt = (ty1, ty2) in
    match tt with (TyVar _, _) | (_, TyVar _) | (TyApp _, _) | (_, TyApp _)
    then t
    else match tt with (TyInt _, TyInt _) | (TyFloat _, TyFloat _) then t
    else match tt with (TySeq _, TySeq _) then t
    else match tt with (OTyList _, OTyList _) then t
    else match tt with (TySeq _, OTyList _) then
      app_ (intrinsicOpSeq "Helpers.to_list") t
    else match tt with (OTyList _, TySeq _) then
      app_ (intrinsicOpSeq "Helpers.of_list") t
    else match tt with (OTyArray _, OTyArray _) then t
    else match tt with (TySeq _, OTyArray _) then
      app_ (intrinsicOpSeq "Helpers.to_array") t
    else match tt with (OTyArray _, TySeq _) then
      app_ (intrinsicOpSeq "Helpers.of_array") t
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then
      t
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then
      t
    else match tt with
      (TyTensor {ty = TyInt _}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then
      app_ (intrinsicOpTensor "Helpers.to_genarray_clayout") t
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyInt _})
    then
      app_ (intrinsicOpTensor "carray_int") t
    else match tt with
      (TyTensor {ty = TyFloat _}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then
      app_ (intrinsicOpTensor "Helpers.to_genarray_clayout") t
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyFloat _})
    then
      app_ (intrinsicOpTensor "carray_float") t
    else match tt
    with (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      let n = nameSym "x" in
      let arg = recur (nvar_ n) ty21 ty11 in
      let body = recur (app_ t arg) ty12 ty22 in
      nulam_ n body
    else error "Cannot marshal data"
  in

  -- TODO(oerikss, 2021-05-07) We wrap external constants in a lambdas in order
  -- for the Obj warpping to work correctly. Ideally, this should not be
  -- necessary.
  match ty1 with TyArrow _ then
    recur t ty1 ty2
  else
    let n = nameSym "x" in
    app_ (nulam_ n (recur t ty1 ty2)) unit_


type ExternalNameMap = Map Name [ExternalImpl]

type ExternalChooseEnv = {
  -- A mapping from external string identifiers to available implementations.
  impls : ExternalMap,

  -- A mapping from external names to used implementations.
  usedImpls : ExternalNameMap ,

  -- Type aliases map
  aliases : Map Name Type
}

type ExternalGenerateEnv = {
  -- A mapping from external names to used implementations.
  usedImpls : ExternalNameMap ,

  -- Type aliases map
  aliases : Map Name Type
}

let externalInitialEnv = lam aliases : Map Name Type.
  {
    impls = globalExternalMap,
    usedImpls = mapEmpty nameCmp,
    aliases = aliases
  }

lang OCamlGenerateExternal

  -- Popluates `env` by chosing external implementations.
  sem chooseExternalImpls (env : ExternalChooseEnv) /- : Expr -> ExternalGenerateEnv -/=
  -- Intentionally left blank


  -- Generates code for externals. The resulting program should be free of
  -- `TmExt` terms.
  sem generateExternals (env : ExternalGenerateEnv) =
  -- Intentionally left blank

end

-- A naive implementation of external generation where we just pick the
-- implementation with the lowest cost with respect to the type given at the
-- external term definition.
lang OCamlGenerateExternalNaive = OCamlGenerateExternal + ExtAst
  sem _chooseExternalImpls (env : ExternalChooseEnv) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    let identStr = nameGetStr ident in
    let impls = mapLookup identStr env.impls in
    match impls with Some (![] & impls) then
      let ty = typeUnwrapAlias env.aliases ty in
      let impl =
        minOrElse
          (lam. error "impossible")
          (lam r1 : ExternalImpl. lam r2 : ExternalImpl.
             let cost1 = externalMarshalCost r1.extTy ty in
             let cost2 = externalMarshalCost r2.extTy ty in
             subi cost1 cost2)
        impls
      in
      let env = {env with usedImpls = mapInsert ident [impl] env.usedImpls} in
      _chooseExternalImpls env inexpr
    else
      error (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr _chooseExternalImpls env t

  sem chooseExternalImpls (env : ExternalChooseEnv) =
  | t ->
    let env : ExternalChooseEnv = _chooseExternalImpls env t in
    { usedImpls = env.usedImpls, aliases = env.aliases }

  sem generateExternals (env : ExternalGenerateEnv) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    let ty = typeUnwrapAlias env.aliases ty in
    match mapLookup ident env.usedImpls
    with Some r then
      let r : ExternalImpl = head r in
      let t = externalMarshal (oext_ r.extIdent) r.extTy ty in
      bind_ (nulet_ ident t) (generateExternals env inexpr)
    else
      error (join ["No implementation for external ", nameGetStr ident])
  | t -> smap_Expr_Expr (generateExternals env) t
end
