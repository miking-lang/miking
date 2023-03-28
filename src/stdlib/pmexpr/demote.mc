-- Translates a PMExpr program to a MExpr compatible program by erasing all
-- uses of accelerate and demoting parallel operations to their corresponding
-- sequential operations.

include "mexpr/ast-builder.mc"
include "pmexpr/ast.mc"
include "pmexpr/pprint.mc"

lang PMExprDemoteBase = PMExprAst
  sem _insertExprInfo (info : Info) =
  | expr ->
    let expr =
      match infoTm expr with NoInfo () then withInfo info expr
      else expr in
    smap_Expr_Expr (_insertExprInfo info) expr

  sem demoteParallel =
  | t -> smap_Expr_Expr demoteParallel t
end

lang PMExprDemoteAccelerate = PMExprDemoteBase
  sem demoteParallel =
  | TmAccelerate t -> demoteParallel t.e
end

lang PMExprDemoteFlatten = PMExprDemoteBase
  sem demoteParallel =
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
end

lang PMExprDemoteMap2 = PMExprDemoteBase
  sem demoteParallel =
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
      ident = aid, tyAnnot = tyTm t.as, tyBody = tyTm t.as, body = demoteParallel t.as,
      inexpr = unit_, ty = tyresult, info = infoTm t.as} in
    let bExpr = TmLet {
      ident = bid, tyAnnot = tyTm t.bs, tyBody = tyTm t.bs, body = demoteParallel t.bs,
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
      ident = tid, tyAnnot = tyseqtuple, tyBody = tyseqtuple,
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
          ident = iid,
          tyAnnot = TyInt {info = t.info}, tyParam = TyInt {info = t.info},
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
          ident = xid, tyAnnot = tytuple, tyParam = tytuple,
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
end

lang PMExprDemoteReduce = PMExprDemoteBase + PMExprAst
  sem demoteParallel =
  | TmParallelReduce t ->
    let tyuk = TyUnknown {info = t.info} in
    TmApp {
      lhs = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CFoldl (), ty = tyuk, info = t.info},
          rhs = demoteParallel t.f, ty = tyuk, info = t.info},
        rhs = demoteParallel t.ne, ty = tyuk, info = t.info},
      rhs = demoteParallel t.as, ty = tyuk, info = t.info}
end

lang PMExprDemoteLoop = PMExprDemoteBase + PMExprAst
  sem demoteParallel =
  | TmLoop t | TmParallelLoop t ->
    let unitTy = TyRecord {fields = mapEmpty cmpSID, info = t.info} in
    let acc = TmRecord {bindings = mapEmpty cmpSID, ty = unitTy, info = t.info} in
    let f = TmLam {
      ident = nameNoSym "", tyAnnot = unitTy, tyParam = unitTy, body = t.f,
      ty = TyArrow {from = unitTy, to = tyTm t.f, info = t.info},
      info = t.info} in
    let accLoop = TmLoopAcc {
      ne = acc, n = t.n, f = f, ty = unitTy, info = t.info} in
    demoteParallel accLoop
  | TmLoopAcc t ->
    let arrowType = lam from. lam to.
      TyArrow {
        from = tyWithInfo t.info from,
        to = tyWithInfo t.info to,
        info = t.info} in
    let loopId = nameSym "loop" in
    let accTy = tyTm t.ne in
    let loopTy = arrowType accTy (arrowType tyint_ accTy) in
    let accIdent = nameSym "acc" in
    let acc = TmVar {
      ident = accIdent, ty = accTy, info = t.info, frozen = false} in
    let iIdent = nameSym "i" in
    let i = TmVar {
      ident = iIdent, ty = TyInt {info = t.info}, info = t.info,
      frozen = false} in
    let f = demoteParallel t.f in
    let loopCompareExpr = TmApp {
      lhs = TmApp {
        lhs = TmConst {
          val = CLti (),
          ty = arrowType tyint_ (arrowType tyint_ tybool_),
          info = t.info},
        rhs = i, ty = arrowType tyint_ tybool_, info = t.info},
      rhs = t.n, ty = tybool_, info = t.info} in
    let incrementIterExpr = TmApp {
      lhs = TmApp {
        lhs = TmConst {
          val = CAddi (),
          ty = arrowType tyint_ (arrowType tyint_ tyint_),
          info = t.info},
        rhs = i, ty = arrowType tyint_ tyint_, info = t.info},
      rhs = TmConst {
        val = CInt {val = 1},
        ty = TyInt {info = t.info},
        info = t.info},
      ty = tyint_, info = t.info} in
    let tIdent = nameSym "t" in
    let tVar = TmVar {ident = tIdent, ty = accTy, info = t.info, frozen = false} in
    let thnExpr = TmLet {
      ident = tIdent,
      tyAnnot = accTy,
      tyBody = accTy,
      body = TmApp {
        lhs = TmApp {
          lhs = f, rhs = acc, ty = arrowType tyint_ accTy, info = t.info},
        rhs = i, ty = accTy, info = t.info},
      inexpr = TmApp {
        lhs = TmApp {
          lhs = TmVar {ident = loopId, ty = loopTy, info = t.info, frozen = false},
          rhs = tVar, ty = arrowType tyint_ accTy, info = t.info},
        rhs = incrementIterExpr,
        ty = accTy, info = t.info},
      ty = accTy, info = t.info} in
    let loopBindingDef = {
      ident = loopId, tyAnnot = loopTy, tyBody = loopTy, info = t.info,
      body = TmLam {
        ident = accIdent, tyAnnot = accTy, tyParam = accTy,
        body = TmLam {
          ident = iIdent,
          tyAnnot = TyInt {info = t.info}, tyParam = TyInt {info = t.info},
          body = TmMatch {
            target = loopCompareExpr,
            pat = PatBool {val = true, ty = TyBool {info = t.info}, info = t.info},
            thn = thnExpr,
            els = acc,
            ty = accTy, info = t.info},
          ty = arrowType tyint_ accTy, info = t.info},
        ty = loopTy, info = t.info}} in
    TmRecLets {
      bindings = [loopBindingDef],
      inexpr = TmApp {
        lhs = TmApp {
          lhs = TmVar {
            ident = loopId, ty = loopTy, info = t.info, frozen = false},
          rhs = t.ne,
          ty = arrowType tyint_ accTy, info = t.info},
        rhs = TmConst {
          val = CInt {val = 0}, ty = TyInt {info = t.info}, info = t.info},
        ty = accTy, info = t.info},
      ty = accTy, info = t.info}
end

lang PMExprDemotePrintFloat = PMExprDemoteBase
  sem demoteParallel =
  | TmPrintFloat t ->
    let tyuk = TyUnknown {info = t.info} in
    TmApp {
      lhs = TmConst {val = CPrint (), ty = tyuk, info = t.info},
      rhs = TmApp {
        lhs = TmConst {val = CFloat2string (), ty = tyuk, info = t.info},
        rhs = t.e, ty = tyuk, info = t.info},
      ty = tyuk, info = t.info}
end

lang PMExprDemote =
  PMExprDemoteAccelerate + PMExprDemoteFlatten + PMExprDemoteMap2 +
  PMExprDemoteReduce + PMExprDemoteLoop + PMExprDemotePrintFloat
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

let acc = int_ 0 in
let n = int_ 10 in
let f = ulam_ "" unit_ in
let foldlFn = ulam_ "acc" (ulam_ "x" (addi_ (var_ "acc") (var_ "x"))) in
let loopRecLet = lam fn.
  ureclet_ "loop" (ulam_ "acc" (ulam_ "i"
    (if_ (lti_ (var_ "i") (int_ 10))
      (bind_
        (ulet_ "t" (appf2_ fn (var_ "acc") (var_ "i")))
        (appf2_ (var_ "loop") (var_ "t") (addi_ (var_ "i") (int_ 1))))
      (var_ "acc")))) in

let accLoopDef = bindall_ [
  loopRecLet foldlFn,
  appf2_ (var_ "loop") acc (int_ 0)] in
utest demoteParallel (loopAcc_ acc n foldlFn) with accLoopDef using eqExpr in

let loopDef = bindall_ [
  loopRecLet (ulam_ "" f),
  appf2_ (var_ "loop") unit_ (int_ 0)] in
utest demoteParallel (loop_ n f) with loopDef using eqExpr in
utest demoteParallel (parallelLoop_ n f) with loopDef using eqExpr in

()
