include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/pprint.mc"

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst

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

-- let x =
-- use OCamlPrettyPrint in
-- printLn "";
-- printLn (expr2str
-- (
--   externalMarshal
--     (var_ "f")
--     (tylist_ tyint_)
--     (tyseq_ tyint_)
-- )
-- )

-- let x =
-- use OCamlPrettyPrint in
-- printLn "";
-- printLn (expr2str
-- (
--   externalMarshal
--     (var_ "f")
--     (tyarrow_ (tyint_) (tylist_ tyint_))
--     (tyarrow_ (tyint_) (tyseq_ tyint_))
-- )
-- )


-- let x =
-- use OCamlPrettyPrint in
-- printLn "";
-- printLn (expr2str
-- (
--   externalMarshal
--     (var_ "f")
--     (tyarrow_ (tylist_ tyint_) (tylist_ tyint_))
--     (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_))
-- )
-- )

-- let x =
-- use OCamlPrettyPrint in
-- printLn "";
-- printLn (expr2str
-- (
--   externalMarshal
--     (var_ "f")
--     (tyarrows_ [tylist_ tyint_, tylist_ tyint_, tylist_ tyint_])
--     (tyarrows_ [tyseq_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
-- )
-- )

-- let x =
-- use OCamlPrettyPrint in
-- printLn "";
-- printLn (expr2str
-- (
--   externalMarshal
--     (var_ "f")
--     (tyarrow_ (tyarrow_ (tylist_ tyint_) (tylist_ tyint_)) tyint_)
--     (tyarrow_ (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_)) tyint_)
-- )
-- )

-- type ExternalNameMap = Map Name ExternalImpl

-- lang OCamlGenerateExternal
--   sem buildExternalNameMap (extMap : ExternalMap) (extNameMap : ExternalNameMap) =
--   -- Intentionally left blank

--   sem generateExternals (extNameMap : ExternalNameMap) =
--   -- Intentionally left blank

--   sem buildAndGenerateExternals (extMap : ExternalMap) =
--   | t ->
--     let extNameMap = buildExternalNameMap extMap (mapEmpty nameCmp) t in
--     (extNameMap, generateExternals extNameMap t)
-- end

-- -- A naive implementation of external generation where we just pick the
-- -- implementation with the least cost with respect to the type given at the
-- -- external term definition.
-- lang OCamlGenerateExternalNaive = OCamlGenerateExternal
--   sem buildExternalNameMap (extMap : ExternalMap) (extNameMap : ExternalNameMap) =
--   | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
--     let identStr = nameGetStr ident in
--     let impls = mapLookup identStr env.externalMap in
--     match impls with Some (![] & impls) then
--       let rs =
--         map
--           (lam impl: ExternalImpl.
--             lexternalMarshal (oext_ impl.extIdent) ty impl.extTy)
--           impls
--       in
--       let r : CostExpr =
--         minOrElse
--           (lam. error "impossible")
--           (lam r1 : CostExpr. lam r2 : CostExpr.
--             subi r1.cost r2.cost)
--         rs
--       in
--       bind_ (nulet_ ident r.tm) (generate env inexpr)
--     else
--       error (join ["No implementation for external ", identStr])

--   sem generateExternal (env : ExternalEnv) =
--   | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
--     let identStr = nameGetStr ident in
--     let impls = mapLookup identStr env.externalMap in
--     match impls with Some (![] & impls) then
--       let rs =
--         map
--           (lam impl: ExternalImpl.
--             lexternalMarshal (oext_ impl.extIdent) ty impl.extTy)
--           impls
--       in
--       let r : CostExpr =
--         minOrElse
--           (lam. error "impossible")
--           (lam r1 : CostExpr. lam r2 : CostExpr.
--             subi r1.cost r2.cost)
--         rs
--       in
--       bind_ (nulet_ ident r.tm) (generate env inexpr)
--     else
--       error (join ["No implementation for external ", identStr])
-- end
