-- Translates a PMExpr program to a MExpr compatible program by erasing all
-- uses of accelerate and demoting parallel operations to their corresponding
-- sequential operations.

include "mexpr/ast-builder.mc"
include "pmexpr/ast.mc"

lang PMExprDemote = PMExprAst
  -- Helper function to update expressions without info fields to use the info
  -- field of the original expression.
  sem _insertExprInfo (info : Info) =
  | expr ->
    let expr =
      match infoTm expr with NoInfo () then
        withInfo info expr
      else expr in
    smap_Expr_Expr (_insertExprInfo info) expr

  sem demoteParallel =
  | TmAccelerate t -> demoteParallel t.e
  | TmFlatten t ->
    let tyuk = TyUnknown {info = t.info} in
    TmApp {
      lhs = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CFoldl (), ty = tyuk, info = t.info},
          rhs = TmConst {val = CConcat (), ty = tyuk, info = t.info},
          ty = tyuk, info = t.info},
        rhs = TmSeq {tms = [], ty = TySeq {ty = tyuk, info = t.info},
                     info = t.info},
        ty = tyuk, info = t.info},
      rhs = demoteParallel t.e,
      ty = tyuk, info = t.info}
  | TmMap2 t ->
    let tyuk = TyUnknown {info = t.info} in
    let lty = match tyTm t.as with TySeq {ty = elemTy} then elemTy else tyuk in
    let rty = match tyTm t.bs with TySeq {ty = elemTy} then elemTy else tyuk in
    let tytuple = tyWithInfo t.info (tytuple_ [lty, rty]) in
    let tyseqtuple = TySeq {ty = tytuple, info = t.info} in
    let tyresult = TySeq {ty = tyuk, info = t.info} in
    let aid = nameSym "a" in
    let bid = nameSym "b" in
    let tid = nameSym "t" in
    let iid = nameSym "i" in
    let xid = nameSym "x" in
    let aExpr = TmLet {
      ident = aid, tyBody = tyTm t.as, body = demoteParallel t.as,
      inexpr = unit_, ty = tyresult, info = infoTm t.as} in
    let bExpr = TmLet {
      ident = bid, tyBody = tyTm t.bs, body = demoteParallel t.bs,
      inexpr = unit_, ty = tyresult, info = infoTm t.bs} in
    let access = lam seqId. lam seqTy. lam elemTy.
      TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CGet (), ty = tyuk, info = t.info},
          rhs = TmVar {ident = seqId, ty = seqTy, info = t.info, frozen = false},
          ty = tyuk, info = t.info},
        rhs = TmVar {ident = iid, ty = TyInt {info = t.info}, info = t.info,
                     frozen = false},
        ty = elemTy, info = t.info} in
    let tExpr = TmLet {
      ident = tid, tyBody = tyseqtuple,
      body = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CCreate (), ty = tyuk, info = t.info},
          rhs = TmApp {
            lhs = TmConst {val = CLength (), ty = tyuk, info = t.info},
            rhs = TmVar {ident = aid, ty = tyTm t.as, info = t.info,
                         frozen = false},
            ty = TyInt {info = t.info}, info = t.info},
          ty = tyuk, info = t.info},
        rhs = TmLam {
          ident = iid, tyIdent = TyInt {info = t.info},
          body = TmRecord {
            bindings = mapFromSeq cmpSID [
              (stringToSid "0", access aid (tyTm t.as) lty),
              (stringToSid "1", access bid (tyTm t.bs) rty)],
            ty = tytuple, info = t.info},
          ty = tytuple, info = t.info},
        ty = tyseqtuple, info = t.info},
      inexpr = unit_, ty = tyresult, info = t.info} in
    let projection = lam key. lam id. lam ty.
      let keySid = stringToSid key in
      let x = nameSym "x" in
      let identPat = PatNamed {ident = PName x, ty = ty, info = t.info} in
      let patBinds = mapFromSeq cmpSID [(keySid, identPat)] in
      TmMatch {
        target = TmVar {ident = id, ty = tytuple, info = t.info, frozen = false},
        pat = PatRecord {bindings = patBinds, ty = tytuple, info = t.info},
        thn = TmVar {ident = x, ty = ty, info = t.info, frozen = false},
        els = TmNever {ty = tyuk, info = t.info},
        ty = tyuk, info = t.info}
    in
    let mapExpr = TmApp {
      lhs = TmApp {
        lhs = TmConst {val = CMap (), ty = tyuk, info = t.info},
        rhs = TmLam {
          ident = xid, tyIdent = tytuple,
          body = TmApp {
            lhs = TmApp {
              lhs = demoteParallel t.f,
              rhs = projection "0" xid lty,
              ty = TyArrow {from = rty, to = tyuk, info = t.info},
              info = t.info},
            rhs = projection "1" xid rty,
            ty = tyuk, info = t.info},
          ty = TyArrow {from = tytuple, to = tyuk, info = t.info},
          info = t.info},
        ty = tyuk, info = t.info},
      rhs = TmVar {ident = tid, ty = tyseqtuple, info = t.info, frozen = false},
      ty = TySeq {ty = tyuk, info = t.info}, info = t.info} in
    bindall_ [aExpr, bExpr, tExpr, mapExpr]
  | TmParallelReduce t ->
    let tyuk = TyUnknown {info = t.info} in
    TmApp {
      lhs = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CFoldl (), ty = tyuk, info = t.info},
          rhs = demoteParallel t.f, ty = tyuk, info = t.info},
        rhs = demoteParallel t.ne, ty = tyuk, info = t.info},
      rhs = demoteParallel t.as, ty = tyuk, info = t.info}
  | t -> smap_Expr_Expr demoteParallel t
end

mexpr

use PMExprDemote in

let id = ulam_ "x" (var_ "x") in
utest demoteParallel (accelerate_ (app_ id (int_ 2)))
with app_ id (int_ 2) using eqExpr in

let s = seq_ [seq_ [int_ 1], seq_ [int_ 2]] in
let flattenSeqExpr = foldl_ (uconst_ (CConcat ())) (seq_ []) s in
utest demoteParallel (flatten_ s)
with foldl_ (uconst_ (CConcat ())) (seq_ []) s using eqExpr in

utest demoteParallel (parallelReduce_ (uconst_ (CAddi ())) (int_ 0) (seq_ []))
with foldl_ (uconst_ (CAddi ())) (int_ 0) (seq_ []) using eqExpr in

utest demoteParallel (map2_ (uconst_ (CAddi ())) (flatten_ s) (flatten_ s))
with bindall_ [
  ulet_ "a" flattenSeqExpr,
  ulet_ "b" flattenSeqExpr,
  ulet_ "t"
    (create_ (length_ (var_ "a"))
      (ulam_ "i" (utuple_ [get_ (var_ "a") (var_ "i"),
                           get_ (var_ "b") (var_ "i")]))),
  map_
    (ulam_ "x" (addi_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))
    (var_ "t")]
using eqExpr in

utest demoteParallel (parallelReduce_ (uconst_ (CAddi ())) (int_ 0) (flatten_ s))
with foldl_ (uconst_ (CAddi ())) (int_ 0) flattenSeqExpr using eqExpr in

utest demoteParallel (accelerate_ (map_ id (flatten_ s)))
with map_ id (foldl_ (uconst_ (CConcat ())) (seq_ []) s) using eqExpr in

()
