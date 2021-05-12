include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst

-- Constructs a sequence of Types from a Type split at ->.
let _typesSeq : Type -> [Type] =
  use OCamlMarshalData in
  lam ty.
  recursive let recur = lam ty.
    match ty with TyArrow {from = from, to = to} then
      cons from (recur to)
    else [ty]
  in
  recur ty


-- Marshals tm of type mcoreTy to type ocamlTy,
-- returning {cost : Int, tm : Expr}, where tm is the result and cost the cost
-- of the marshaling, repsectivly.


let externalMarshal = lam tm. lam mcoreTy. lam ocamlTy.

  recursive
  let marshal : Expr -> (Type, Type) -> {cost : Int, tm : Expr} =
  use OCamlMarshalData in
  use OCamlExternal in
  lam tm. lam tt.
    match tt with (TyVar _, _) then
      {tm = tm, cost = 0}
    else match tt with (_, TyVar _) then
      {tm = tm, cost = 0}
    else match tt with (TyInt _, TyInt _) then
      {tm = tm, cost = 0}
    else match tt with (TyFloat _, TyFloat _) then
      {tm = tm, cost = 0}
    else match tt with (TySeq _, TySeq _) then
      {tm = tm, cost = 0}
    else match tt with (TyList _, TyList _) then
      {tm = tm, cost = 0}
    else match tt with (TySeq _, TyList _) then
      -- NOTE(oerikss, 2021-04-24) we would like the cost to be proportional
      -- to the length of the sequence. This applies to other types as well.
      {tm = app_ (OTmVarExt {ident = (intrinsicOpSeq "Helpers.to_list")}) tm, cost = 3}
    else match tt with (TyList _, TySeq _) then
      {tm = app_ (OTmVarExt {ident = (intrinsicOpSeq "Helpers.of_list")}) tm, cost = 3}
    else error "Cannot marshal data"

  let recur : Expr -> Type -> Type -> {cost : Int, tm : Expr} =
  lam tm. lam ty1. lam ty2.
    let tys1 = _typesSeq ty1 in
    let tys2 = _typesSeq ty2 in
    let ntys1 = length tys1 in
    if neqi ntys1 (length tys2) then
      error "From and to type have different arity"
    else if eqi ntys1 1 then
      -- TODO(oerikss, 2021-04-30) We wrap external constants in a lambdas in
      -- order for the Obj warpping to work correctly. Ideally we would like
      -- not having to do this.
      let r = marshal tm (ty2, ty1) in
      {r with tm = app_ (nulam_ (nameSym "x") r.tm) unit_}
    else
      let nargs = subi ntys1 1 in

      let names : [Name] =
        unfoldr
          (lam b. if geqi b nargs then None ()
                  else Some(nameSym (cons 'x' (int2string b)), addi b 1))
          0
      in

      let tmp : [{tm : Expr, cost : Int}] =
        let zapp = zipWith (lam f. lam x. f x) in
        let vars = map nvar_ names in
        let fs = map recur vars in
        zapp (zapp fs (init tys2)) (init tys1)
      in

      let tm = appSeq_
                    tm
                    (map (lam x : {cost : Int, tm : Expr}. x.tm) tmp)
      in

      match marshal tm (last tys2, last tys1)
      with {tm = body, cost = cost} then
        let cost =
          addi
            cost
            (foldl (lam c : Int. lam x : {cost : Int, tm : Expr}.
                      addi c x.cost)
                    0
                    tmp)
        in
        {tm = nulams_ names body, cost = cost}
      else never
  in
  recur tm mcoreTy ocamlTy

utest
  match externalMarshal
          (var_ "f")
          (tyarrow_ tyint_ tyfloat_)
          (tyarrow_ tyint_ tyfloat_)
  with {cost = cost} then cost else (negi 1)
with 0

utest
  let r =
    externalMarshal
            (var_ "f")
            (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_))
            (tyarrow_ (tylist_ tyint_) (tylist_ tyint_))
  in
  match r with {cost = cost} then cost else (negi 1)
with 6

utest
  match externalMarshal
          (var_ "f")
          (tyarrow_ (tyseq_ tyint_) tyint_)
          (tyarrow_ (tylist_ tyint_) tyint_)
   with {cost = cost} then cost else (negi 1)
with 3

utest
  let r =
    externalMarshal
      (var_ "f")
      (tyarrow_ (tyarrow_ (tyseq_ tyint_) tyint_) tyint_)
      (tyarrow_ (tyarrow_ (tylist_ tyint_) tyint_) tyint_)
  in
  match r with {cost = cost} then cost else (negi 1)
with 3
