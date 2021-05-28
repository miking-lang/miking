include "ast.mc"
include "map.mc"
include "name.mc"
include "stringid.mc"

-- Types --

let futIntTy_ = use FutharkAst in
  FTyInt {}

let futFloatTy_ = use FutharkAst in
  FTyFloat {}

let nFutIdentTy_ = use FutharkAst in
  lam n.
  FTyIdent {ident = n}

let futIdentTy_ = lam str.
  nFutIdentTy_ (nameNoSym str)

let futSizedArrayTy_ = use FutharkAst in
  lam sz. lam elemTy.
  FTyArray {elem = elemTy, dim = Some sz}

let futUnsizedArrayTy_ = use FutharkAst in
  lam elemTy.
  FTyArray {elem = elemTy, dim = None ()}

let futRecordTy_ = use FutharkAst in
  lam fieldSeq.
  FTyRecord {fields = mapFromList cmpSID (map
                        (lam kv : (String, FutType). (stringToSid kv.0, kv.1))
                        fieldSeq)}

let futUnitTy_ = lam. futRecordTy_ []

-- Expressions --

recursive let futBind_ = use FutharkAst in
  lam letexpr. lam expr.
  match letexpr with FELet t then
    FELet {t with inexpr = futBind_ t.inexpr expr}
  else expr
end

let futBindall_ = lam exprs. foldr1 futBind_ exprs

let nFutVar_ = use FutharkAst in
  lam n.
  FEVar {ident = n}

let futVar_ = lam str. nFutVar_ (nameNoSym str)

let futRecord_ = use FutharkAst in
  lam fieldSeq.
  FERecord {fields = mapFromList cmpSID (map
                       (lam kv : (String, FutExpr). (stringToSid kv.0, kv.1))
                       fieldSeq)}

let futUnit_ = lam. futRecord_ []

let futRecordProj_ = use FutharkAst in
  lam rec. lam field.
  FERecordProj {rec = rec, key = stringToSid field}

let futArray_ = use FutharkAst in
  lam tms.
  FEArray {tms = tms}

let futArrayAccess_ = use FutharkAst in
  lam array. lam index.
  FEArrayAccess {array = array, index = index}

let futArrayUpdate_ = use FutharkAst in
  lam array. lam index. lam value.
  FEArrayUpdate {array = array, index = index, value = value}

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

let futLam_ = lam str. lam body.
  nFutLam_ (nameNoSym str) body

let futApp_ = use FutharkAst in
  lam lhs. lam rhs.
  FEApp {lhs = lhs, rhs = rhs}

let futAppSeq_ = lam f. lam seq.
  foldl futApp_ f seq

let futBinop_ = lam op. lam a. lam b.
  futAppSeq_ op [a, b]

let nFutLet_ = use FutharkAst in
  lam n. lam ty. lam body.
  FELet {ident = n, tyBody = Some ty, body = body, inexpr = futUnit_ ()}

let nuFutLet_ = use FutharkAst in
  lam n. lam body.
  FELet {ident = n, tyBody = None (), body = body, inexpr = futUnit_ ()}

let uFutLet_ = lam str. lam body.
  nuFutLet_ (nameNoSym str) body

let futLet_ = lam str. lam ty. lam body.
  nFutLet_ (nameNoSym str) ty body

let futIf_ = use FutharkAst in
  lam cond. lam thn. lam els.
  FEIf {cond = cond, thn = thn, els = els}

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
  lam f. lam as.
  futAppSeq_ (futConst_ (FCMap ())) [f, as]

let futMap2_ = use FutharkAst in
  lam f. lam as. lam bs.
  futAppSeq_ (futConst_ (FCMap2 ())) [f, as, bs]

let futReduce_ = use FutharkAst in
  lam f. lam ne. lam as.
  futAppSeq_ (futConst_ (FCReduce ())) [f, ne, as]

let futScan_ = use FutharkAst in
  lam f. lam ne. lam as.
  futAppSeq_ (futConst_ (FCScan ())) [f, ne, as]

let futFilter_ = use FutharkAst in
  lam p. lam as.
  futAppSeq_ (futConst_ (FCFilter ())) [p, as]

let futPartition_ = use FutharkAst in
  lam p. lam as.
  futAppSeq_ (futConst_ (FCPartition ())) [p, as]

let futAll_ = use FutharkAst in
  lam p. lam as.
  futAppSeq_ (futConst_ (FCAll ())) [p, as]

let futAny_ = use FutharkAst in
  lam p. lam as.
  futAppSeq_ (futConst_ (FCAny ())) [p, as]
