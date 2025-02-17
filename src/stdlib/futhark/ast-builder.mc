include "ast.mc"
include "map.mc"
include "name.mc"
include "stringid.mc"

-- Types --

let futUnknownTy_ = use FutharkAst in
  FTyUnknown {info = NoInfo ()}

let futIntTy_ = use FutharkAst in
  FTyInt {info = NoInfo (), sz = I64 ()}

let futFloatTy_ = use FutharkAst in
  FTyFloat {info = NoInfo (), sz = F64 ()}

let futBoolTy_ = use FutharkAst in
  FTyBool {info = NoInfo ()}

let nFutIdentTy_ = use FutharkAst in
  lam n.
  FTyIdent {ident = n, info = NoInfo ()}

let futIdentTy_ = lam str.
  nFutIdentTy_ (nameNoSym str)

let futSizedArrayTy_ = use FutharkAst in
  lam elemTy. lam szId.
  FTyArray {elem = elemTy, dim = Some (NamedDim szId), info = NoInfo ()}

let futUnsizedArrayTy_ = use FutharkAst in
  lam elemTy.
  FTyArray {elem = elemTy, dim = None (), info = NoInfo ()}

let futRecordTy_ = use FutharkAst in
  lam fieldSeq.
  FTyRecord {fields = mapFromSeq cmpSID (map
                        (lam kv : (String, FutType). (stringToSid kv.0, kv.1))
                        fieldSeq),
             info = NoInfo ()}

let futTupleTy_ = use FutharkAst in
  lam fields.
  futRecordTy_ (create (length fields) (lam i. (int2string i, get fields i)))

let futProjTy_ = use FutharkAst in
  lam target. lam label.
  FTyProj {target = target, label = stringToSid label, info = NoInfo ()}

let futUnitTy_ = lam. futRecordTy_ []

let futArrowTy_ = use FutharkAst in
  lam fromTy. lam toTy.
  FTyArrow {from = fromTy, to = toTy, info = NoInfo ()}

-- Patterns --

let nFutPvar_ = use FutharkAst in
  lam n : Name.
  FPNamed {ident = PName n, ty = futUnknownTy_, info = NoInfo ()}

let futPvarw_ = use FutharkAst in
  lam.
  FPNamed {ident = PWildcard (), ty = futUnknownTy_, info = NoInfo ()}

let futPint_ = use FutharkAst in
  lam i : Int.
  FPInt {val = i, ty = futUnknownTy_, info = NoInfo ()}

let futPbool_ = use FutharkAst in
  lam b : Bool.
  FPBool {val = b, ty = futUnknownTy_, info = NoInfo ()}

let futPrecord_ = use FutharkAst in
  lam bindings : [(String, FutPat)].
  let bindingMapFunc = lam b : (String, FutPat). (stringToSid b.0, b.1) in
  FPRecord {bindings = mapFromSeq cmpSID (map bindingMapFunc bindings),
            ty = futUnknownTy_, info = NoInfo ()}

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
  FEVar {ident = n, ty = futUnknownTy_, info = NoInfo ()}

let futVar_ = lam str. nFutVar_ (nameNoSym str)

let futVarExt_ = use FutharkAst in
  lam str.
  FEVarExt {ident = str, ty = futUnknownTy_, info = NoInfo ()}

let futSizeCoercion_ = use FutharkAst in
  lam e. lam ty.
  FESizeCoercion {e = e, ty = ty, info = NoInfo ()}

let futSizeEquality_ = use FutharkAst in
  lam x1. lam d1. lam x2. lam d2.
  FESizeEquality {x1 = x1, d1 = d1, x2 = x2, d2 = d2,
                  ty = FTyUnknown {info = NoInfo ()}, info = NoInfo ()}

let futProj_ = use FutharkAst in
  lam target. lam label.
  FEProj {target = target, label = stringToSid label, ty = futUnknownTy_,
          info = NoInfo ()}

let futRecord_ = use FutharkAst in
  lam fieldSeq.
  FERecord {fields = mapFromSeq cmpSID (map
                       (lam kv : (String, FutExpr). (stringToSid kv.0, kv.1))
                       fieldSeq),
            ty = futUnknownTy_, info = NoInfo ()}

let futTuple_ = use FutharkAst in
  lam fields.
  futRecord_ (create (length fields) (lam i. (int2string i, get fields i)))

let futUnit_ = lam. futRecord_ []

let futRecordProj_ = futProj_

let futRecordUpdate_ = use FutharkAst in
  lam rec. lam field. lam v.
  FERecordUpdate {rec = rec, key = stringToSid field, value = v,
                  ty = futUnknownTy_, info = NoInfo ()}

let futArray_ = use FutharkAst in
  lam tms.
  FEArray {tms = tms, ty = futUnknownTy_, info = NoInfo ()}

let futArrayAccess_ = use FutharkAst in
  lam array. lam index.
  FEArrayAccess {array = array, index = index, ty = futUnknownTy_,
                 info = NoInfo ()}

let futArrayUpdate_ = use FutharkAst in
  lam array. lam index. lam value.
  FEArrayUpdate {array = array, index = index, value = value,
                 ty = futUnknownTy_, info = NoInfo ()}

let futArraySlice_ = use FutharkAst in
  lam array. lam startIdx. lam endIdx.
  FEArraySlice {array = array, startIdx = startIdx, endIdx = endIdx,
                ty = futUnknownTy_, info = NoInfo ()}

let futConst_ = use FutharkAst in
  lam c.
  FEConst {val = c, ty = futUnknownTy_, info = NoInfo ()}

let nFutLam_ = use FutharkAst in
  lam n. lam body.
  FELam {ident = n, body = body, ty = futUnknownTy_, info = NoInfo ()}

let futLam_ = lam str. lam body.
  nFutLam_ (nameNoSym str) body

let futApp_ = use FutharkAst in
  lam lhs. lam rhs.
  FEApp {lhs = lhs, rhs = rhs, ty = futUnknownTy_, info = NoInfo ()}

let futAppSeq_ = lam f. lam seq.
  foldl futApp_ f seq

let futBinop_ = lam op. lam a. lam b.
  futAppSeq_ op [a, b]

let nFutLet_ = use FutharkAst in
  lam n. lam ty. lam body.
  FELet {ident = n, tyBody = ty, body = body, inexpr = futUnit_ (),
         ty = futUnknownTy_, info = NoInfo ()}

let nuFutLet_ =
  lam n. lam body.
  nFutLet_ n futUnknownTy_ body

let uFutLet_ = lam str. lam body.
  nuFutLet_ (nameNoSym str) body

let futLet_ = lam str. lam ty. lam body.
  nFutLet_ (nameNoSym str) ty body

let futIf_ = use FutharkAst in
  lam cond. lam thn. lam els.
  FEIf {cond = cond, thn = thn, els = els, ty = futUnknownTy_, info = NoInfo ()}

let futForEach_ = use FutharkAst in
  lam param : (FutPat, FutExpr). lam loopVar. lam seq. lam body.
  FEForEach {param = param, loopVar = loopVar, seq = seq, body = body,
             ty = futUnknownTy_, info = NoInfo ()}

let futMatch_ = use FutharkAst in
  lam target. lam cases : [(FutPat, FutExpr)].
  FEMatch {target = target, cases = cases, ty = futUnknownTy_, info = NoInfo ()}

-- Constants --

let futInt_ = use FutharkAst in
  lam n.
  futConst_ (FCInt {val = n, sz = Some (I64 ())})

let futFloat_ = use FutharkAst in
  lam f.
  futConst_ (FCFloat {val = f, sz = Some (F64 ())})

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

let futFlatten_ = use FutharkAst in
  lam s.
  futApp_ (futConst_ (FCFlatten ())) s

let futIndices_ = use FutharkAst in
  lam s.
  futApp_ (futConst_ (FCIndices ())) s

let futIota_ = use FutharkAst in
  lam n.
  futApp_ (futConst_ (FCIota ())) n

let futReplicate_ = use FutharkAst in
  lam n. lam e.
  futAppSeq_ (futConst_ (FCReplicate ())) [n, e]

let futTabulate_ = use FutharkAst in
  lam n. lam f.
  futAppSeq_ (futConst_ (FCTabulate ())) [n, f]

let futCopy_ = use FutharkAst in
  lam s.
  futApp_ (futConst_ (FCCopy ())) s

let futLength_ = use FutharkAst in
  lam s.
  futApp_ (futConst_ (FCLength ())) s
