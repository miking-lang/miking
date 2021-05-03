include "ast.mc"
include "map.mc"
include "name.mc"
include "stringid.mc"

-- Expressions --

recursive let futBind_ = use FutharkAst in
  lam letexpr. lam expr.
  match letexpr with FELet t then
    FELet {t with inexpr = futBind_ t.inexpr expr}
  else expr
end

let nFutVar_ = use FutharkAst in
  lam n.
  FEVar {ident = n}

let futVar_ = use FutharkAst in
  lam str.
  nFutVar_ (nameNoSym str)

let futRecord_ = use FutharkAst in
  lam fieldSeq.
  FERecord {fields = mapFromList cmpSID (map
                       (lam kv : (String, FutExpr). (stringToSid kv.0, kv.1))
                       fieldSeq)}

let futUnit_ = use FutharkAst in
  futRecord_ []

let futRecordProj_ = use FutharkAst in
  lam rec. lam field.
  FERecordProj {rec = rec, key = stringToSid field}

let futArray_ = use FutharkAst in
  lam tms.
  FEArray {tms = tms}

let futConst_ = use FutharkAst in
  lam c.
  FEConst {val = c}

let nFutLams_ = use FutharkAst in
  lam nargs. lam body.
  FELam {idents = nargs, body = body}

let futLams_ = use FutharkAst in
  lam args. lam body.
  FELam {idents = map nameNoSym args, body = body}

let nFutLam_ = use FutharkAst in
  lam n. lam body.
  FELam {idents = [n], body = body}

let futLam_ = use FutharkAst in
  lam str. lam body.
  nFutLam_ (nameNoSym str) body

let futApp_ = use FutharkAst in
  lam lhs. lam rhs.
  FEApp {lhs = lhs, rhs = rhs}

let futAppSeq_ = use FutharkAst in
  lam f. lam seq.
  foldl futApp_ f seq

let futBinop_ = use FutharkAst in
  lam op. lam a. lam b.
  futAppSeq_ op [a, b]

let nFutLet_ = use FutharkAst in
  lam n. lam ty. lam body.
  FELet {ident = n, ty = ty, body = body, inexpr = futUnit_}

let futLet_ = use FutharkAst in
  lam str. lam ty. lam body.
  nFutLet_ (nameNoSym str) ty body

-- Constants --

let futInt_ = use FutharkAst in
  lam n.
  futConst_ (FCInt {val = n})

let futFloat_ = use FutharkAst in
  lam f.
  futConst_ (FCFloat {val = f})

let futAdd_ = use FutharkAst in
  futBinop_ (futConst_ (FCAdd ()))

let futSub_ = use FutharkAst in
  futBinop_ (futConst_ (FCSub ()))

let futMul_ = use FutharkAst in
  futBinop_ (futConst_ (FCMul ()))

let futDiv_ = use FutharkAst in
  futBinop_ (futConst_ (FCDiv ()))

let futMap_ = use FutharkAst in
  lam f. lam array.
  futAppSeq_ (futConst_ (FCMap ())) [f, array]

let futMap2_ = use FutharkAst in
  lam f. lam a1. lam a2.
  futAppSeq_ (futConst_ (FCMap2 ())) [f, a1, a2]

-- Types --

let futIntTy_ = use FutharkAst in
  FTyIdent {ident = nameSym "i64"}

let futFloatTy_ = use FutharkAst in
  FTyIdent {ident = nameSym "f64"}

let futSizedArrayTy_ = use FutharkAst in
  lam elemTy. lam sz.
  FTyArray {elem = elemTy, dim = Some sz}

let futUnsizedArrayTy_ = use FutharkAst in
  lam elemTy.
  FTyArray {elem = elemTy, dim = None ()}

let futRecordTy_ = use FutharkAst in
  lam fieldSeq.
  FTyRecord {fields = mapFromList cmpSID (map
                        (lam kv : (String, FutType). (stringToSid kv.0, kv.1))
                        fieldSeq)}
