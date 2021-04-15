-- Helper functions for creating AST nodes.
-- Functions for types are defined in ast.mc

include "mexpr/ast.mc"
include "assoc.mc"
include "info.mc"
include "stringid.mc"
include "map.mc"

-- Patterns --

let npvar_ = use MExprAst in
  lam n : Name.
  PatNamed {ident = PName n, info = NoInfo ()}

let pvar_ = use MExprAst in
  lam s.
  npvar_ (nameNoSym s)

let pvarw_ = use MExprAst in
  PatNamed {ident = PWildcard (), info = NoInfo()}

let punit_ = use MExprAst in
  PatRecord { bindings = mapEmpty cmpSID, info = NoInfo() }

let pint_ = use MExprAst in
  lam i.
  PatInt {val = i, info = NoInfo()}

let pchar_ = use MExprAst in
  lam c.
  PatChar {val = c, info = NoInfo()}

let ptrue_ = use MExprAst in
  PatBool {val = true, info = NoInfo()}

let pfalse_ = use MExprAst in
  PatBool {val = false, info = NoInfo()}

let npcon_ = use MExprAst in
  lam n. lam cp.
  PatCon {ident = n, subpat = cp, info = NoInfo()}

let pcon_ = use MExprAst in
  lam cs. lam cp.
  npcon_ (nameNoSym cs) cp

let prec_ = use MExprAst in
  lam bindings.
  let bindingMapFunc = lam b : (String, a). (stringToSid b.0, b.1) in
  PatRecord {
    bindings =
      mapFromList cmpSID (map bindingMapFunc bindings),
    info = NoInfo()
    }

let ptuple_ = use MExprAst in
  lam ps.
  prec_ (mapi (lam i. lam p. (int2string i,p)) ps)

let pseqtot_ = use MExprAst in
  lam ps.
  PatSeqTot {pats = ps, info = NoInfo()}

let pseqedgew_ = use MExprAst in
  lam pre. lam post.
  PatSeqEdge {prefix = pre, middle = PWildcard (), postfix = post, info = NoInfo()}

let pseqedgen_ = use MExprAst in
  lam pre. lam middle : Name. lam post.
  PatSeqEdge {prefix = pre, middle = PName middle, postfix = post, info = NoInfo()}

let pseqedge_ = use MExprAst in
  lam pre. lam middle. lam post.
  pseqedgen_ pre (nameNoSym middle) post

let pand_ = use MExprAst in
  lam l. lam r.
  PatAnd {lpat = l, rpat = r, info = NoInfo()}

let por_ = use MExprAst in
  lam l. lam r.
  PatOr {lpat = l, rpat = r, info = NoInfo()}

let pnot_ = use MExprAst in
  lam p.
  PatNot {subpat = p, info = NoInfo()}

-- Types --

let tyint_ = use IntTypeAst in
  TyInt {info = NoInfo ()}

let tyfloat_ = use FloatTypeAst in
  TyFloat {info = NoInfo ()}

let tybool_ = use BoolTypeAst in
  TyBool {info = NoInfo ()}

let tychar_ = use CharTypeAst in
  TyChar {info = NoInfo ()}

let tyunknown_ = use UnknownTypeAst in
  TyUnknown {info = NoInfo ()}

let tyseq_ = use SeqTypeAst in
  lam ty.
  TySeq {ty = ty, info = NoInfo ()}

let tystr_ = tyseq_ tychar_

let tyarrow_ = use FunTypeAst in
  lam from. lam to.
  TyArrow {from = from, to = to, info = NoInfo ()}

let tyarrows_ = use FunTypeAst in
  lam tys.
  foldr1 (lam e. lam acc. TyArrow {from = e, to = acc, info = NoInfo ()}) tys

let tyrecord_ = use RecordTypeAst in
  lam fields.
  let fieldMapFunc = lam b : (String, a). (stringToSid b.0, b.1) in
  TyRecord {
    fields = mapFromList cmpSID (map fieldMapFunc fields),
    info = NoInfo ()
  }

let tytuple_ = lam tys.
  tyrecord_ (mapi (lam i. lam ty. (int2string i, ty)) tys)

let tyunit_ = tyrecord_ []

let tyvariant_ = use VariantTypeAst in
  lam constrs.
  TyVariant {
    constrs = mapFromList nameCmp constrs,
    info = NoInfo ()
  }

let tyapp_ = use AppTypeAst in
  lam lhs. lam rhs.
  TyApp {lhs = lhs, rhs = rhs, info = NoInfo ()}

let ntyvar_ = use VarTypeAst in
  lam n.
  TyVar {ident = n, info = NoInfo ()}

let tyvar_ = lam s.
  ntyvar_ (nameNoSym s)

-- Terms --
-- Methods of binding an expression into a chain of lets/reclets/condefs --

recursive let bind_ = use MExprAst in
  lam letexpr. lam expr.
  match letexpr with TmLet t then
    TmLet {t with inexpr = bind_ t.inexpr expr}
  else match letexpr with TmRecLets t then
    TmRecLets {t with inexpr = bind_ t.inexpr expr}
  else match letexpr with TmConDef t then
    TmConDef {t with inexpr = bind_ t.inexpr expr}
  else match letexpr with TmType t then
    TmType {t with inexpr = bind_ t.inexpr expr}
  else
    expr -- Insert at the end of the chain
end

let bindall_ = use MExprAst in
  lam exprs.
  foldr1 bind_ exprs

let unit_ = use MExprAst in
  TmRecord {bindings = mapEmpty cmpSID, ty = tyunknown_, info = NoInfo ()}

let nlet_ = use MExprAst in
  lam n. lam ty. lam body.
  TmLet {ident = n, tyBody = ty, body = body,
  inexpr = unit_, ty = tyunknown_, info = NoInfo ()}

let let_ = use MExprAst in
  lam s. lam ty. lam body.
  nlet_ (nameNoSym s) ty body

let nulet_ = use MExprAst in
  lam n. lam body.
  nlet_ n tyunknown_ body

let ulet_ = use MExprAst in
  lam s. lam body.
  let_ s tyunknown_ body

let ntype_ = use MExprAst in
  lam n. lam ty.
  TmType {ident = n, tyIdent = ty, ty = tyunknown_, inexpr = unit_, info = NoInfo ()}

let type_ = use MExprAst in
  lam s. lam ty.
  ntype_ (nameNoSym s) ty

let nreclets_ = use MExprAst in
  lam bs.
  let bindingMapFunc = lam t : (Name, Type, Expr).
    { ident = t.0
    , tyBody = t.1
    , body = t.2
    , ty = tyunknown_
    , info = NoInfo ()
    }
  in
  TmRecLets {bindings = map bindingMapFunc bs,
             inexpr = unit_, ty = tyunknown_, info = NoInfo ()}

let reclets_ = use MExprAst in
  lam bs.
  let bindingMapFunc = lam b : (String, Type, Expr).
    (nameNoSym b.0, b.1, b.2)
  in
  nreclets_ (map bindingMapFunc bs)

let nureclets_ = use MExprAst in
  lam bs.
  let bindingMapFunc = lam b : (Name, Expr).
    (b.0, tyunknown_, b.1)
  in
  nreclets_ (map bindingMapFunc bs)

let ureclets_ = use MExprAst in
  lam bs.
  let bindingMapFunc = lam b : (String, Expr).
    (b.0, tyunknown_, b.1)
  in
  reclets_ (map bindingMapFunc bs)

let reclet_ = use MExprAst in
  lam s. lam ty. lam body.
  reclets_ [(s, ty, body)]

let ureclet_ = use MExprAst in
  lam s. lam body.
  ureclets_ [(s, body)]

let reclets_empty = use MExprAst in
  reclets_ []

let nreclets_add = use MExprAst in
  lam n. lam ty. lam body. lam reclets.
  match reclets with TmRecLets t then
    let newbind = {ident = n, tyBody = ty, body = body, ty = tyunknown_, info = NoInfo ()} in
    TmRecLets {t with bindings = cons newbind t.bindings}
  else
    error "reclets is not a TmRecLets construct"

let reclets_add = use MExprAst in
  lam s. lam ty. lam body. lam reclets.
  nreclets_add (nameNoSym s) ty body reclets

let nureclets_add = use MExprAst in
  lam n. lam body. lam reclets.
  nreclets_add n tyunknown_ body reclets

let ureclets_add = use MExprAst in
  lam s. lam body. lam reclets.
  reclets_add s tyunknown_ body reclets

let ncondef_ = use MExprAst in
  lam n. lam ty.
  TmConDef {ident = n, tyIdent = ty, ty = tyunknown_,
            inexpr = unit_, info = NoInfo ()}

let condef_ = use MExprAst in
  lam s. lam ty.
  ncondef_ (nameNoSym s) ty

let nucondef_ = use MExprAst in
  lam n.
  ncondef_ n tyunknown_

let ucondef_ = use MExprAst in
  lam s.
  condef_ s tyunknown_

let nvar_ = use MExprAst in
  lam n.
  TmVar {ident = n, ty = tyunknown_, info = NoInfo ()}

let var_ = use MExprAst in
  lam s.
  nvar_ (nameNoSym s)

let nconapp_ = use MExprAst in
  lam n. lam b.
  TmConApp {ident = n, body = b, ty = tyunknown_, info = NoInfo ()}

let conapp_ = use MExprAst in
  lam s. lam b.
  nconapp_ (nameNoSym s) b

let const_ = use MExprAst in
  lam c.
  TmConst {val = c, ty = tyunknown_, info = NoInfo ()}

let nlam_ = use MExprAst in
  lam n. lam ty. lam body.
  TmLam {ident = n, tyIdent = ty, ty = tyunknown_, body = body, info = NoInfo ()}

let lam_ = use MExprAst in
  lam s. lam ty. lam body.
  nlam_ (nameNoSym s) ty body

let nulam_ = use MExprAst in
  lam n. lam body.
  nlam_ n tyunknown_ body

let ulam_ = use MExprAst in
  lam s. lam body.
  lam_ s tyunknown_ body

let lams_ = use MExprAst in
  lam params. lam body.
  foldr (lam p : (String, Expr). lam acc. lam_ p.0 p.1 acc) body params

let ulams_ = use MExprAst in
  lam idents. lam body.
  foldr (lam s. lam acc. ulam_ s acc) body idents

let nulams_ = use MExprAst in
  lam names. lam body.
  foldr (lam n. lam acc. nulam_ n acc) body names

let if_ = use MExprAst in
  lam cond. lam thn. lam els.
  TmMatch {target = cond, pat = ptrue_, thn = thn,
           els = els, ty = tyunknown_, info = NoInfo ()}

let match_ = use MExprAst in
  lam target. lam pat. lam thn. lam els.
  TmMatch {target = target, pat = pat, thn = thn, els = els,
           ty = tyunknown_, info = NoInfo ()}

let seq_ = use MExprAst in
  lam tms.
  TmSeq {tms = tms, ty = tyunknown_, info = NoInfo ()}

let record_ = use MExprAst in
  lam bindings.
  let bindingMapFunc = lam b : (String, Expr). (stringToSid b.0, b.1) in
  TmRecord {
    bindings = mapFromList cmpSID (map bindingMapFunc bindings),
    ty = tyunknown_,
    info = NoInfo ()
  }

let tuple_ = use MExprAst in
  lam tms.
  record_ (mapi (lam i. lam t. (int2string i,t)) tms)

let record_empty = unit_

let record_add = use MExprAst in
  lam key. lam value. lam record.
  match record with TmRecord t then
      TmRecord {t with bindings = mapInsert (stringToSid key) value t.bindings}
  else
      error "record is not a TmRecord construct"

let record_add_bindings = lam bindings. lam record.
  foldl (lam recacc. lam b : (k, v). record_add b.0 b.1 recacc) record bindings

let never_ = use MExprAst in
  TmNever {ty = tyunknown_, info = NoInfo ()}

let nrecordproj_ = use MExprAst in
  lam name. lam key. lam r.
  -- It is fine to use any variable name here. It doesn't matter if it
  -- overwrites a previous binding, since that binding will never be used in
  -- the then clause in any case.
  match_ r (prec_ [(key,npvar_ name)]) (nvar_ name) never_

let recordproj_ = use MExprAst in
  lam key. lam r.
  nrecordproj_ (nameNoSym "x") key r

let ntupleproj_ = use MExprAst in
  lam name. lam i. lam t.
  nrecordproj_ name (int2string i) t

let tupleproj_ = use MExprAst in
  lam i. lam t.
  recordproj_ (int2string i) t

let recordupdate_ = use MExprAst in
  lam rec. lam key. lam value.
  TmRecordUpdate {
    rec = rec,
    key = stringToSid key,
    value = value,
    ty = tyunknown_,
    info = NoInfo ()
  }

let app_ = use MExprAst in
  lam l. lam r.
  TmApp {lhs = l, rhs = r, ty = tyunknown_, info = NoInfo ()}

let appSeq_ = use MExprAst in
  lam f. lam seq.
  foldl app_ f seq

let appf1_ = use MExprAst in
  lam f. lam a1.
  app_ f a1

let appf2_ = use MExprAst in
  lam f. lam a1. lam a2.
  app_ (appf1_ f a1) a2

let appf3_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3.
  app_ (appf2_ f a1 a2) a3

let appf4_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3. lam a4.
  app_ (appf3_ f a1 a2 a3) a4

let appf5_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3. lam a4. lam a5.
  app_ (appf4_ f a1 a2 a3 a4) a5

let appf6_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3. lam a4. lam a5. lam a6.
  app_ (appf5_ f a1 a2 a3 a4 a5) a6

let appf7_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3. lam a4. lam a5. lam a6. lam a7.
  app_ (appf6_ f a1 a2 a3 a4 a5 a6) a7

let appf8_ = use MExprAst in
  lam f. lam a1. lam a2. lam a3. lam a4. lam a5. lam a6. lam a7. lam a8.
  app_ (appf7_ f a1 a2 a3 a4 a5 a6 a7) a8

let utestu_ = use MExprAst in
  lam t. lam e. lam n. lam u.
  TmUtest {test = t, expected = e, next = n, tusing = Some u, ty = tyunknown_, info = NoInfo ()}

let utest_ = use MExprAst in
  lam t. lam e. lam n.
  TmUtest {test = t, expected = e, next = n, tusing = None (), ty = tyunknown_, info = NoInfo ()}

-- Ascription
let asc_ = use MExprAst in
  lam ty. lam expr.
  bind_ (let_ "x" ty expr) (var_ "x")

-- Constants --

let int_ = use MExprAst in
  lam i.
  const_ (CInt {val = i})

let float_ = use MExprAst in
  lam f.
  const_ (CFloat {val = f})

let true_ = use MExprAst in
  const_ (CBool {val = true})

let false_ = use MExprAst in
  const_ (CBool {val = false})

let bool_ = use MExprAst in
  lam v.
  const_ (CBool {val = v})

let char_ = use MExprAst in
  lam c.
  const_ (CChar {val = c})

let str_ = use MExprAst in
  lam s.
  TmSeq {tms = map char_ s, ty = tyunknown_, info = NoInfo ()}

let symb_ = use MExprAst in
  lam c.
  const_ (CSymb {val = c})

let addi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CAddi ())) a b

let subi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CSubi ())) a b

let muli_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CMuli ())) a b

let divi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CDivi ())) a b

let modi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CModi ())) a b

let negi_ = use MExprAst in
  lam n.
  appf1_ (const_ (CNegi ())) n

let addf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CAddf ())) a b

let subf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CSubf ())) a b

let mulf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CMulf ())) a b

let divf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CDivf ())) a b

let negf_ = use MExprAst in
  lam a.
  appf1_ (const_ (CNegf ())) a

let floorfi_ = use MExprAst in
  lam x.
  appf1_ (const_ (CFloorfi ())) x

let ceilfi_ = use MExprAst in
  lam x.
  appf1_ (const_ (CCeilfi ())) x

let roundfi_ = use MExprAst in
  lam x.
  appf1_ (const_ (CRoundfi ())) x

let int2float_ = use MExprAst in
  lam x.
  appf1_ (const_ (CInt2float ())) x

let eqi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CEqi ())) a b

let neqi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CNeqi ())) a b

let lti_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLti ())) a b

let gti_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CGti ())) a b

let leqi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLeqi ())) a b

let geqi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CGeqi ())) a b

let eqc_ = use MExprAst in
  lam c1. lam c2.
  appf2_ (const_ (CEqc ())) c1 c2

let int2char_ = use MExprAst in
  lam i.
  app_ (const_ (CInt2Char ())) i

let char2int_ = use MExprAst in
  lam c.
  app_ (const_ (CChar2Int ())) c

let string2float_ = use MExprAst in
  lam s.
  app_ (const_ (CString2float ())) s

let eqf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CEqf ())) a b

let ltf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLtf ())) a b

let leqf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLeqf ())) a b

let gtf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CGtf ())) a b

let geqf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CGeqf ())) a b

let neqf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CNeqf ())) a b

let slli_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CSlli ())) a b

let srli_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CSrli ())) a b

let srai_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CSrai ())) a b

let get_ = use MExprAst in
  lam s. lam i.
  appf2_ (const_ (CGet ())) s i

let set_ = use MExprAst in
  lam s. lam i. lam v.
  appf3_ (const_ (CSet ())) s i v

let empty_ = use MExprAst in
  seq_ []

let cons_ = use MExprAst in
  lam x. lam s.
  appf2_ (const_ (CCons ())) x s

let snoc_ = use MExprAst in
  lam s. lam x.
  appf2_ (const_ (CSnoc ())) s x

let concat_ = use MExprAst in
  lam s1. lam s2.
  appf2_ (const_ (CConcat ())) s1 s2

let length_ = use MExprAst in
  lam s.
  appf1_ (const_ (CLength ())) s

let reverse_ = use MExprAst in
  lam s.
  appf1_ (const_ (CReverse ())) s

let splitat_ = use MExprAst in
  lam s. lam n.
  appf2_ (const_ (CSplitAt ())) s n

let create_ = use MExprAst in
  lam n. lam f.
  appf2_ (const_ (CCreate ())) n f

let subsequence_ = use MExprAst in
  lam s. lam off. lam n.
  appf3_ (const_ (CSubsequence ())) s off n

-- Short circuit logical expressions
let and_ = use MExprAst in
  lam a. lam b. if_ a b false_

let or_ = use MExprAst in
  lam a. lam b. if_ a true_ b

let not_ = use MExprAst in
  lam b. if_ b false_ true_

-- Symbol operations
let gensym_ = use MExprAst in
  lam u. appf1_ (const_ (CGensym ())) u

let eqsym_ = use MExprAst in
  lam s1. lam s2.
  appf2_ (const_ (CEqsym ())) s1 s2

let sym2hash_ = use MExprAst in
  lam s.
  appf1_ (const_ (CSym2hash ())) s

-- References
let ref_ = use MExprAst in
  lam v. appf1_ (const_ (CRef ())) v

let deref_ = use MExprAst in
  lam r. appf1_ (const_ (CDeRef ())) r

let modref_ = use MExprAst in
  lam r. lam v. appf2_ (const_ (CModRef ())) r v

-- File operations
let readFile_ = use MExprAst in
  lam f. appf1_ (const_ (CFileRead ())) f

let writeFile_ = use MExprAst in
  lam f. lam d. appf2_ (const_ (CFileWrite ())) f d

let fileExists_ = use MExprAst in
  lam f. appf1_ (const_ (CFileExists ())) f

let deleteFile_ = use MExprAst in
  lam f. appf1_ (const_ (CFileDelete ())) f

-- I/O operations
let print_ = use MExprAst in
  lam s. app_ (const_ (CPrint ())) s

let dprint_ = use MExprAst in
  lam s. app_ (const_ (CDPrint ())) s

let readLine_ = use MExprAst in
  lam u. app_ (const_ (CReadLine ())) u

-- Random number generation
let randIntU_ = use MExprAst in
  lam lo. lam hi. appf2_ (const_ (CRandIntU ())) lo hi

let randSetSeed_ = use MExprAst in
  lam s. appf1_ (const_ (CRandSetSeed ())) s

-- Error
let error_ = use MExprAst in
  lam s. appf1_ (const_ (CError ())) s

-- Exit
let exit_ = use MExprAst in
  lam n. appf1_ (const_ (CExit ())) n

-- Argv
let argv_ = use MExprAst in
  const_ (CArgv ())

-- Command
let command_ = use MExprAst in
  lam s. appf1_ (const_ (CCommand ())) s

-- Time operations
let wallTimeMs_ = use MExprAst in
  lam u. appf1_ (const_ (CWallTimeMs ())) u

let sleepMs_ = use MExprAst in
  lam n. appf1_ (const_ (CSleepMs ())) n

-- Tensors
let tensorCreate_ = use MExprAst in
  lam s. lam f.
  appf2_ (const_ (CTensorCreate ())) s f

let tensorGetExn_ = use MExprAst in
  lam t. lam is.
  appf2_ (const_ (CTensorGetExn ())) t is

let tensorSetExn_ = use MExprAst in
  lam t. lam is. lam v.
  appf3_ (const_ (CTensorSetExn ())) t is v

let tensorRank_ = use MExprAst in
  lam t.
  appf1_ (const_ (CTensorRank ())) t

let tensorShape_ = use MExprAst in
  lam t.
  appf1_ (const_ (CTensorShape ())) t

let tensorReshapeExn_ = use MExprAst in
  lam t. lam s.
  appf2_ (const_ (CTensorReshapeExn ())) t s

let tensorCopyExn_ = use MExprAst in
  lam t1. lam t2.
  appf2_ (const_ (CTensorCopyExn ())) t1 t2

let tensorSliceExn_ = use MExprAst in
  lam t. lam s.
  appf2_ (const_ (CTensorSliceExn ())) t s

let tensorSubExn_ = use MExprAst in
  lam t. lam ofs. lam len.
  appf3_ (const_ (CTensorSubExn ())) t ofs len

let tensorIteri_ = use MExprAst in
  lam f. lam t.
  appf2_ (const_ (CTensorIteri ())) f t

-- Bootparser
let bootParserParseMExprString_ = use MExprAst in
  lam str. appf1_ (const_ (CBootParserParseMExprString ())) str

let bootParserGetId_ = use MExprAst in
  lam pt. appf1_ (const_ (CBootParserGetId ())) pt

let bootParserGetTerm_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetTerm ())) pt n

let bootParserGetString_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetString ())) pt n

let bootParserGetInt_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetInt ())) pt n

let bootParserGetFloat_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetFloat ())) pt n

let bootParserGetListLength_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetListLength ())) pt n

let bootParserGetConst_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetConst ())) pt n

let bootParserGetPat_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetPat ())) pt n

let bootParserGetInfo_ = use MExprAst in
  lam pt. lam n.
  appf2_ (const_ (CBootParserGetInfo ())) pt n

let mapEmpty_ = use MExprAst in
  lam cmp.
  appf1_ (const_ (CMapEmpty ())) cmp

let mapInsert_ = use MExprAst in
  lam k. lam v. lam m.
  appf3_ (const_ (CMapInsert ())) k v m

let mapRemove_ = use MExprAst in
  lam k. lam m.
  appf2_ (const_ (CMapRemove ())) k m

let mapFindWithExn_ = use MExprAst in
  lam k. lam m.
  appf2_ (const_ (CMapFindWithExn ())) k m

let mapFindOrElse_ = use MExprAst in
  lam f. lam k. lam m.
  appf3_ (const_ (CMapFindOrElse ())) f k m

let mapFindApplyOrElse_ = use MExprAst in
  lam f. lam felse. lam k. lam m.
  appf4_ (const_ (CMapFindApplyOrElse ())) f felse k m

let mapBindings_ = use MExprAst in
  lam m.
  appf1_ (const_ (CMapBindings ())) m

let mapSize_ = use MExprAst in
  lam m.
  appf1_ (const_ (CMapSize ())) m

let mapMem_ = use MExprAst in
  lam k. lam m.
  appf2_ (const_ (CMapMem ())) k m

let mapAny_ = use MExprAst in
  lam p. lam m.
  appf2_ (const_ (CMapAny ())) p m

let mapMap_ = use MExprAst in
  lam f. lam m.
  appf2_ (const_ (CMapMap ())) f m

let mapMapWithKey_ = use MExprAst in
  lam f. lam m.
  appf2_ (const_ (CMapMapWithKey ())) f m

let mapFoldWithKey_ = use MExprAst in
  lam f. lam z. lam m.
  appf3_ (const_ (CMapFoldWithKey ())) f z m

let mapEq_ = use MExprAst in
  lam veq. lam m1. lam m2.
  appf3_ (const_ (CMapEq ())) veq m1 m2

let mapCmp_ = use MExprAst in
  lam vcmp. lam m1. lam m2.
  appf3_ (const_ (CMapCmp ())) vcmp m1 m2

let mapGetCmpFun_ = use MExprAst in
  lam m.
  appf1_ (const_ (CMapGetCmpFun ())) m

-- Sequencing (;)
let semi_ = lam expr1. lam expr2. bind_ (ulet_ "" expr1) expr2
