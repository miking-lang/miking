include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/pprint.mc"

let ocamlPPrint = use OCamlPrettyPrint in
  lam ast. expr2str ast

let cannotMashalDataMsg = "Cannot marshal data"

lang OCamlMarshalData = OCamlTypeAst + SeqTypeAst + TensorTypeAst

let typesSeq = use OCamlMarshalData in
  lam ty.
  recursive let recur = lam ty.
    match ty with TyArrow {from = from, to = to} then
      cons from (recur to)
    else [ty]
  in
  recur ty

utest typesSeq (tyint_) with [tyint_]
utest typesSeq (tyarrow_ tyint_ tyfloat_) with [tyint_, tyfloat_]
utest typesSeq (tyarrows_ [tyint_, tyfloat_, tyint_])
with [tyint_, tyfloat_, tyint_]


recursive
let marshal : Expr -> (Type, Type) -> {cost : Int, tm : Expr} =
  use OCamlMarshalData in
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
      -- NOTE(oerikss, 2021-04-24) we would like the cost to be proportional to
      -- the length of the sequence. This applies to other types as well.
      {tm = app_ (intrinsicOpSeq "Helpers.to_list") tm, cost = 3}
    else match tt with (TyList _, TySeq _) then
      {tm = app_ (intrinsicOpSeq "Helpers.of_list") tm, cost = 3}
    else match tt with (TyArrow _ & from, TyArrow _ & to) then
      let fromTys = typesSeq from in
      let toTys = typesSeq to in
      if neqi (length fromTys) (length toTys) then
        error "From and to type have different arity"
      else
        let argtts = zipWith
                      (lam from. lam to. (from, to))
                      (init fromTys)
                      (init toTys)
        in
        let nargs = length argtts in
        let rettt = (last toTys, last fromTys) in

        let names =
          unfoldr
            (lam b. if geqi b nargs then None ()
                    else Some(nameSym (cons 'x' (int2string b)), addi b 1))
            0
        in

        let tmp = zipWith (lam n. lam tt. marshal (nvar_ n) tt) names argtts in

        match marshal (appSeq_ tm (map (lam x. x.tm) tmp)) rettt
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

utest marshal (var_ "x") (tyint_, tyint_)
with {tm = (var_ "x"), cost = 0}

utest marshal (var_ "x") (tyfloat_, tyfloat_)
with {tm = (var_ "x"), cost = 0}

utest
  match marshal
          (var_ "f")
          (tyarrow_ tyint_ tyfloat_, tyarrow_ tyint_ tyfloat_)
   with {cost = cost} then cost else (negi 1)
with 0

utest
  let r =
    marshal
            (var_ "f")
            (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_),
             tyarrow_ (tylist_ tyint_) (tylist_ tyint_))
  in
  match r with {cost = cost} then cost else (negi 1)
with 6

utest
  match marshal
          (var_ "f")
          (tyarrow_ (tyseq_ tyint_) tyint_,
           tyarrow_ (tylist_ tyint_) tyint_)
   with {cost = cost} then cost else (negi 1)
with 3

utest
  let r =
    marshal
      (var_ "f")
      (tyarrow_ (tyarrow_ (tyseq_ tyint_) tyint_) tyint_,
       tyarrow_ (tyarrow_ (tylist_ tyint_) tyint_) tyint_)
  in
  match r with {cost = cost} then cost else (negi 1)
with 3

mexpr
let r =
  marshal
    (var_ "f")
    (tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                tyseq_ (tyvar_ "a"),
                tyseq_ (tyvar_ "b")],
    tyarrows_ [tyarrow_ (tyvar_ "a") (tyvar_ "b"),
                tylist_ (tyvar_ "a"),
                tylist_ (tyvar_ "b")])
in
-- printLn (ocamlPPrint r.tm);
()
