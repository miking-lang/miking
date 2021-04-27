include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"

let cannotMashalDataMsg = "Cannot marshal data"

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


-- Marshals tm of type tt.0 to type tt.1, returning {cost : Int, tm : Expr},
-- where tm is the result of the marshaling and cost is the cost of the
-- marshaling.
recursive
let externalMarshal : Expr -> (Type, Type) -> {cost : Int, tm : Expr} =
  use OCamlMarshalData in
  lam tm : Expr. lam tt : (Type, Type).
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
      -- NOTE(oerikss, 2021-04-24) we would like the cost to be proportional to
      -- the length of the sequence. This applies to other types as well.
      {tm = app_ (intrinsicOpSeq "Helpers.to_list") tm, cost = 3}
    else match tt with (TyList _, TySeq _) then
      {tm = app_ (intrinsicOpSeq "Helpers.of_list") tm, cost = 3}
    else match tt with (TyArrow _ & from, TyArrow _ & to) then
      let fromTys = _typesSeq from in
      let toTys = _typesSeq to in
      if neqi (length fromTys) (length toTys) then
        error "From and to type have different arity"
      else
        let argtts : [(Type, Type)] =
          zipWith
            (lam from. lam to. (from, to))
            (init fromTys)
            (init toTys)
        in
        let nargs = length argtts in
        let rettt : (Type, Type) = (last toTys, last fromTys) in

        let names : [Name] =
          unfoldr
            (lam b. if geqi b nargs then None ()
                    else Some(nameSym (cons 'x' (int2string b)), addi b 1))
            0
        in

        let tmp : [{tm : Expr, cost : Int}] =
          zipWith (lam n. lam tt. externalMarshal (nvar_ n) tt) names argtts
        in

        match externalMarshal (appSeq_
                        tm
                        (map (lam x : {cost : Int, tm : Expr}. x.tm) tmp))
                      rettt
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
    else error cannotMashalDataMsg
end

utest
  match externalMarshal
          (var_ "f")
          (tyarrow_ tyint_ tyfloat_, tyarrow_ tyint_ tyfloat_)
  with {cost = cost} then cost else (negi 1)
with 0

utest
  let r =
    externalMarshal
            (var_ "f")
            (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_),
             tyarrow_ (tylist_ tyint_) (tylist_ tyint_))
  in
  match r with {cost = cost} then cost else (negi 1)
with 6

utest
  match externalMarshal
          (var_ "f")
          (tyarrow_ (tyseq_ tyint_) tyint_,
           tyarrow_ (tylist_ tyint_) tyint_)
   with {cost = cost} then cost else (negi 1)
with 3

utest
  let r =
    externalMarshal
      (var_ "f")
      (tyarrow_ (tyarrow_ (tyseq_ tyint_) tyint_) tyint_,
       tyarrow_ (tyarrow_ (tylist_ tyint_) tyint_) tyint_)
  in
  match r with {cost = cost} then cost else (negi 1)
with 3
