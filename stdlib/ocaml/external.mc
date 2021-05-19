include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "mexpr/type.mc"

type ExternalEnv = {

  -- A mapping from external names to used implementations.
  usedImpls : Map Name [ExternalImpl],

  -- Type aliases map
  aliases : Map Name Type,

  -- Record constructors
  constrs : Map Name Type
}

let externalInitialEnv =
  lam aliases : Map Name Type. lam constrs : Map Name Type.
  {
    usedImpls = mapEmpty nameCmp,
    aliases = aliases,
    constrs = constrs
  }

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst

let _externalMarshal : ExternalEnv -> Expr -> Type -> Type -> (Int, Expr) =
  use OCamlMarshalData in
  lam env : ExternalEnv. lam t. lam ty1. lam ty2.
  recursive let recur = lam t. lam ty1. lam ty2.
    let tt =
      (typeUnwrapAlias env.aliases ty1, typeUnwrapAlias env.aliases ty2)
    in
    match tt with
      (TyVar _, _) | (_, TyVar _) |
      (TyApp {lhs = TyVar _}, _) | (_, TyApp {lhs = TyVar _}) |
      (TyInt _, TyInt _) | (TyFloat _, TyFloat _) |
      (TySeq _, TySeq _) |
      (OTyList _, OTyList _)
    then
      (0, t)
    else match tt with (TySeq _, OTyList _) then
      (5, app_ (intrinsicOpSeq "Helpers.to_list") t)
    else match tt with (OTyList _, TySeq _) then
      (5, app_ (intrinsicOpSeq "Helpers.of_list") t)
    else match tt with (OTyArray _, OTyArray _) then
      (0, t)
    else match tt with (TySeq _, OTyArray _) then
      (2, app_ (intrinsicOpSeq "Helpers.to_array") t)
    else match tt with (OTyArray _, TySeq _) then
      (2, app_ (intrinsicOpSeq "Helpers.of_array") t)
    else match tt with (TyRecord {fields = fields}, OTyTuple {tys = []}) then
      if eqi (mapSize fields) 0  then
        (0, semi_ t ounit_)
      else error "Cannot marshal non-empty record to empty tuple"
    else match tt with (OTyTuple {tys = []}, TyRecord {fields = fields}) then
      if eqi (mapSize fields) 0  then
        (0, semi_ t uunit_)
      else error "Cannot marshal empty tuple to non-empty record"
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then
      (0, t)
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then
      (0, t)
    else match tt with
      (TyTensor {ty = TyInt _}
      ,OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
    then
      (1, app_ (intrinsicOpTensor "Helpers.to_genarray_clayout") t)
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyInt _})
    then
      (1, app_ (intrinsicOpTensor "carray_int") t)
    else match tt with
      (TyTensor {ty = TyFloat _}
      ,OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
    then
      (1, app_ (intrinsicOpTensor "Helpers.to_genarray_clayout") t)
    else match tt with
      (OTyBigArrayGenArray
        {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
      ,TyTensor {ty = TyFloat _})
    then
      (1, app_ (intrinsicOpTensor "carray_float") t)
    else match tt with (ty1, OTyLabel {label = label, ty = ty2}) then
      match recur t ty1 ty2 with (cost, t) then
        (cost, oarglabel_ label t)
      else never
    else match tt
    with (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      let n = nameSym "x" in
      match recur (nvar_ n) ty21 ty11 with (cost1, arg) then
        match recur (app_ t arg) ty12 ty22 with (cost2, body) then
          (addi cost1 cost2, nulam_ n body)
        else never
      else never
    else error "Cannot marshal data"
  in

  -- TODO(oerikss, 2021-05-07) We wrap external constants in a lambdas in order
  -- for the Obj warpping to work correctly. Ideally, this should not be
  -- necessary.
  match ty1 with TyArrow _ then
    recur t ty1 ty2
  else
    let n = nameSym "x" in
    match recur t ty1 ty2 with (cost, body) then
      (cost, app_ (nulam_ n body) uunit_)
    else never

-- Marshals expression `Exp` of type `Type` to expression `Expr` of type
-- `Type`.
let externalMarshal : ExternalEnv -> Expr -> Type -> Type -> Expr =
  lam env. lam t. lam ty1. lam ty2.
  match _externalMarshal env t ty1 ty2 with (_, t) then t
  else never

-- Computes the cost of Marshaling the expression `Exp` of type `Type` to
-- expression `Expr` of type `Type`.
let externalMarshalCost : ExternalEnv -> Type -> Type -> Int =
  lam env. lam ty1. lam ty2.
  match _externalMarshal env never_ ty1 ty2 with (cost, _) then cost
  else never

lang OCamlGenerateExternal

  -- Popluates `env` by chosing external implementations.
  sem chooseExternalImpls (impls : ExternalImplsMap)  (env : ExternalEnv) /- : Expr -> ExternalEnv -/=
  -- Intentionally left blank


  -- Generates code for externals. The resulting program should be free of
  -- `TmExt` terms.
  sem generateExternals (env : ExternalEnv) =
  -- Intentionally left blank

end

-- A naive implementation of external generation where we just pick the
-- implementation with the lowest cost with respect to the type given at the
-- external term definition.
lang OCamlGenerateExternalNaive = OCamlGenerateExternal + ExtAst
  sem chooseExternalImpls (implsMap : ExternalImplsMap) (env : ExternalEnv) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    let identStr = nameGetStr ident in
    let impls = mapLookup identStr implsMap in
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
      let env = {env with usedImpls = mapInsert ident [impl] env.usedImpls} in
      chooseExternalImpls implsMap env inexpr
    else
      error (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr (chooseExternalImpls implsMap) env t

  sem generateExternals (env : ExternalEnv) =
  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    match mapLookup ident env.usedImpls
    with Some r then
      let r : ExternalImpl = head r in
      let t = externalMarshal env (oext_ r.extIdent) r.extTy ty in
      bind_ (nulet_ ident t) (generateExternals env inexpr)
    else
      error (join ["No implementation for external ", nameGetStr ident])
  | t -> smap_Expr_Expr (generateExternals env) t
end
