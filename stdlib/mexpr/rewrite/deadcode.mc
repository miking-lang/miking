-- Performs deadcode elimination of a PMExpr term in ANF. Also provides
-- functionality for performing it on the bodies of top-level definitions.

include "set.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/rewrite/parallel-keywords.mc"

lang MExprParallelDeadcodeElimination = MExprParallelKeywordMaker
  sem collectVariablesH (acc : Set Name) =
  | TmVar t -> setInsert t.ident acc
  | t -> sfold_Expr_Expr collectVariablesH acc t

  sem deadcodeEliminationH (used : Set Name) =
  | TmVar t -> (setInsert t.ident used, TmVar t)
  | TmLet t ->
    match deadcodeEliminationH used t.inexpr with (used, inexpr) then
      if setMem t.ident used then
        let used = collectVariablesH used t.body in
        (used, TmLet {t with inexpr = inexpr})
      else (used, inexpr)
    else never
  | TmRecLets t ->
    let deadcodeBinding : Set Name -> RecLetBinding -> (Set Name, RecLetBinding) =
      lam used. lam binding.
      match deadcodeEliminationH used binding.body with (used, body) then
        (used, {binding with body = body})
      else never
    in
    match deadcodeEliminationH used t.inexpr with (used, inexpr) then
      match mapAccumL deadcodeBinding used t.bindings with (used, bindings) then
        (used, TmRecLets {{t with bindings = bindings}
                             with inexpr = inexpr})
      else never
    else never
  | t -> smapAccumL_Expr_Expr deadcodeEliminationH used t

  sem deadcodeElimination =
  | t ->
    match deadcodeEliminationH (setEmpty nameCmp) t with (_, t) then
      t
    else never

  sem deadcodeEliminationToplevel =
  | TmLet t ->
    TmLet {{t with body = deadcodeElimination t.body}
              with inexpr = deadcodeEliminationToplevel t.inexpr}
  | TmRecLets t ->
    let bindings =
      map
        (lam bind : RecLetBinding.
          let body = deadcodeElimination bind.body in
          {bind with body = body})
        t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = deadcodeEliminationToplevel t.inexpr}
  | TmType t -> TmType {t with inexpr = deadcodeEliminationToplevel t.inexpr}
  | TmConDef t -> TmConDef {t with inexpr = deadcodeEliminationToplevel t.inexpr}
  | TmUtest t -> TmUtest {t with next = deadcodeEliminationToplevel t.next}
  | TmExt t -> TmExt {t with inexpr = deadcodeEliminationToplevel t.inexpr}
  | t -> t
end

lang TestLang = MExprParallelDeadcodeElimination + MExprEq + MExprSym

mexpr

use TestLang in

let x = nameSym "x" in
let y = nameSym "y" in
let z = nameSym "z" in 
let w = nameSym "w" in 
let t = symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  ulet_ "y" (int_ 3),
  ulet_ "z" (addi_ (var_ "x") (int_ 4)),
  ulet_ "w" (muli_ (int_ 7) (var_ "y")),
  var_ "z"
]) in
let expected = symbolize (bindall_ [
  ulet_ "x" (int_ 2),
  ulet_ "z" (addi_ (var_ "x") (int_ 4)),
  var_ "z"
]) in
utest deadcodeElimination t with expected using eqExpr in

let t = symbolize (reclets_ [
  ("fact", tyunknown_, ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (bind_ ((ulet_ "x") (int_ 0)) (int_ 1))
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))
  ))
]) in
let expected = symbolize (reclets_ [
  ("fact", tyunknown_, ulam_ "n" (
    if_ (eqi_ (var_ "n") (int_ 0))
      (int_ 1)
      (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))
  ))
]) in
utest deadcodeElimination t with expected using eqExpr in

let t = symbolize (bind_
  (ulet_ "f" (ulam_ "a" (ulam_ "b" (bindall_ [
    ulet_ "t" (addi_ (var_ "a") (var_ "b")),
    var_ "t"
  ]))))
  unit_) in
utest deadcodeEliminationToplevel t with t using eqExpr in

let t = symbolize (bind_
  (ulet_ "q" (ulam_ "x" (bindall_ [
    ulet_ "t" (seq_ []),
    ulet_ "t" (addi_ (int_ 1) (var_ "x")),
    var_ "t"
  ])))
  unit_) in
let expected = symbolize (bind_
  (ulet_ "q" (ulam_ "x" (bindall_ [
    ulet_ "t" (addi_ (int_ 1) (var_ "x")),
    var_ "t"
  ])))
  unit_) in
utest deadcodeEliminationToplevel t with expected using eqExpr in

let t = symbolize (bindall_ [
  reclets_ [
    ("fact", tyunknown_, ulam_ "n" (bindall_ [
      ulet_ "tmp" (addi_ (int_ 1) (int_ 2)),
      if_ (eqi_ (var_ "n") (int_ 0))
        (bind_ (ulet_ "tmp2" (int_ 4)) (int_ 1))
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))
    ]))
  ],
  ulet_ "x" (int_ 2),
  unit_
]) in
let expected = symbolize (bindall_ [
  reclets_ [
    ("fact", tyunknown_, ulam_ "n" (bindall_ [
      if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))
    ]))
  ],
  ulet_ "x" (int_ 2),
  unit_
]) in
utest deadcodeEliminationToplevel t with expected using eqExpr in

()
