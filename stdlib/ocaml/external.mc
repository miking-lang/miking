include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst

-- Computes the cost `Int` of marshaling data from `Type` to `Type`.
let externalMarshalCost : Type -> Type -> Int =
  use OCamlMarshalData in
  recursive let recur = lam ty1. lam ty2.
    let tt = (ty1, ty2) in
    match tt with (TyVar _, _) then 0
    else match tt with (_, TyVar _) then 0
    else match tt with (TyInt _, TyInt _) then 0
    else match tt with (TyFloat _, TyFloat _) then 0
    else match tt with (TySeq _, TySeq _) then 0
    else match tt with (TyList _, TyList _) then 0
    else match tt with (TySeq _, TyList _) then 3
    else match tt with (TyList _, TySeq _) then 3
    else match tt
    with (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      addi (recur ty21 ty11) (recur ty12 ty22)
    else error "Cannot compute marshal data cost"
  in
  recur

utest externalMarshalCost tyint_ tyint_ with 0
utest externalMarshalCost (tylist_ tyint_) (tyseq_ tyint_) with 3
utest
  externalMarshalCost
    (tyarrow_ (tyseq_ tyint_) (tylist_ tyint_))
    (tyarrow_ (tylist_ tyint_) (tyseq_ tyint_))
with 6
utest
  externalMarshalCost
    (tyarrows_ [tyseq_ tyint_, tylist_ tyint_, tyseq_ tyint_])
    (tyarrows_ [tylist_ tyint_, tyseq_ tyint_, tylist_ tyint_])
with 9


-- Marshals expression `Exp` of type `Type` to expression `Expr` of type
-- `Type`.
let externalMarshal : Expr -> Type -> Type -> Expr =
  use OCamlMarshalData in
  lam t. lam ty1. lam ty2.
  recursive let recur = lam t. lam ty1. lam ty2.
    let tt = (ty1, ty2) in
    match tt with (TyVar _, _) then t
    else match tt with (_, TyVar _) then t
    else match tt with (TyInt _, TyInt _) then t
    else match tt with (TyFloat _, TyFloat _) then t
    else match tt with (TySeq _, TySeq _) then t
    else match tt with (TyList _, TyList _) then t
    else match tt with (TySeq _, TyList _) then
      app_ (intrinsicOpSeq "Helpers.to_list") t
    else match tt with (TyList _, TySeq _) then
      app_ (intrinsicOpSeq "Helpers.of_list") t
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

lang OCamlGenerateExternal

  -- Takes a map `ExternalMap` and constructs a map `ExternalNameMap` of
  -- external implementations used in a program `Expr`.
  sem buildExternalNameMap (extMap : ExternalMap) (extNameMap : ExternalNameMap) =
  -- Intentionally left blank


  -- Generates code given an map `ExternalNameMap` of external implementations
  -- in a program `Expr`. The resulting program should be free of `TmExt`
  -- terms.
  sem generateExternals (extNameMap : ExternalNameMap) =
  -- Intentionally left blank

  sem chooseAndGenerateExternals (extMap : ExternalMap) =
  | t ->
    let extNameMap = buildExternalNameMap extMap (mapEmpty nameCmp) t in
    (extNameMap, generateExternals extNameMap t)
end

-- A naive implementation of external generation where we just pick the
-- implementation with the lowest cost with respect to the type given at the
-- external term definition.
lang OCamlGenerateExternalNaive = OCamlGenerateExternal + ExtAst
  sem buildExternalNameMap (extMap : ExternalMap) (extNameMap : ExternalNameMap) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    let identStr = nameGetStr ident in
    let impls = mapLookup identStr extMap in
    match impls with Some (![] & impls) then
      let impl =
        minOrElse
          (lam. error "impossible")
          (lam r1 : ExternalImpl. lam r2 : ExternalImpl.
             let cost1 = externalMarshalCost r1.extTy ty in
             let cost2 = externalMarshalCost r2.extTy ty in
             subi cost1 cost2)
        impls
      in
      buildExternalNameMap extMap (mapInsert ident [impl] extNameMap) inexpr
    else
      error (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr (buildExternalNameMap extMap) extNameMap t

  sem generateExternals (extNameMap : ExternalNameMap) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    match mapLookup ident extNameMap
    with Some r then
      let r : ExternalImpl = head r in
      let t = externalMarshal (oext_ r.extIdent) r.extTy ty in
      bind_ (nulet_ ident t) (generateExternals extNameMap inexpr)
    else
      error (join ["No implementation for external ", nameGetStr ident])
  | t -> smap_Expr_Expr (generateExternals extNameMap) t
end
