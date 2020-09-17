include "mexpr/ast.mc"
include "assoc.mc"

-- Patterns --

let npvar_ = use MExprAst in
  lam n.
  PVar {ident = PName n}

let pvar_ = use MExprAst in
  lam s.
  npvar_ (nameNoSym s)

let pvarw_ = use MExprAst in
  PVar {ident = PWildcard ()}

let pwild_ = use MExprAst in
  PWildcard ()

let punit_ = use MExprAst in
  PRecord { bindings = assocEmpty }

let pint_ = use MExprAst in
  lam i.
  PInt {val = i}

let pchar_ = use MExprAst in
  lam c.
  PChar {val = c}

let ptrue_ = use MExprAst in
  PBool {val = true}

let pfalse_ = use MExprAst in
  PBool {val = false}

let npcon_ = use MExprAst in
  lam n. lam cp.
  PCon {ident = n, subpat = cp}

let pcon_ = use MExprAst in
  lam cs. lam cp.
  npcon_ (nameNoSym cs) cp

let prec_ = use MExprAst in
  lam bindings.
  PRecord {bindings = bindings}

let ptuple_ = use MExprAst in
  lam ps.
  prec_ (mapi (lam i. lam p. (int2string i,p)) ps)

let pseqtot_ = use MExprAst in
  lam ps.
  PSeqTot {pats = ps}

let pseqedge_ = use MExprAst in
  lam pre. lam middle. lam post.
  PSeqEdge {prefix = pre, middle = middle, postfix = post}

let pand_ = use MExprAst in
  lam l. lam r.
  PAnd {lpat = l, rpat = r}

let por_ = use MExprAst in
  lam l. lam r.
  POr {lpat = l, rpat = r}

let pnot_ = use MExprAst in
  lam p.
  PNot {subpat = p}

-- Types --
let tyarrow_ = use MExprAst in
  lam from. lam to.
  TyArrow {from = from, to = to}

let tyarrows_ = use MExprAst in
  lam tpes.
  foldr1 (lam e. lam acc. TyArrow {from = e, to = acc}) tpes

let tydyn_ = use MExprAst in
  TyDyn ()

let tyunit_ = use MExprAst in
  TyUnit ()

let tyint_ = use MExprAst in
  TyInt ()

let tybool_ = use MExprAst in
  TyBool ()

let tychar_ = use MExprAst in
  TyChar ()

let tystr_ = use MExprAst in
  TyString ()

let tyseq_ = use MExprAst in
  lam tpe.
  TySeq {tpe = tpe}

let typrod_ = use MExprAst in
  lam tpes.
  TyProd {tpes = tpes}

let tyrecord_ = use MExprAst in
  lam tpes.
  TyRecord {tpes = tpes}

let tyrecord_fromtups = use MExprAst in
  lam tpetups.
  tyrecord_ (map (lam t. {ident = t.0, tpe = t.1}) tpetups)

let tycon_ = use MExprAst in
  lam ident.
  TyCon {ident = ident}

let tyapp_ = use MExprAst in
  lam lhs. lam rhs.
  TyApp {lhs = lhs, rhs = rhs}

let tyvar_ = use MExprAst in
  lam ident.
  TyVar {ident = ident}


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
  else
    expr -- Insert at the end of the chain
end

let bindall_ = use MExprAst in
  lam exprs.
  foldl1 bind_ exprs

let unit_ = use MExprAst in
  TmRecord {bindings = assocEmpty}

let nlet_ = use MExprAst in
  lam n. lam body.
  TmLet {ident = n, body = body, inexpr = unit_}

let let_ = use MExprAst in
  lam s. lam body.
  nlet_ (nameNoSym s) body

let nreclets_ = use MExprAst in
  lam bs.
  TmRecLets {bindings = map (lam t. {ident = t.0, body = t.1}) bs,
             inexpr = unit_}

let reclets_ = use MExprAst in
  lam bs.
  nreclets_ (map (lam b. (nameNoSym b.0, b.1)) bs)

let reclet_ = use MExprAst in
  lam s. lam body.
  reclets_ [(s, body)]

let reclets_empty = use MExprAst in
  reclets_ []

let nreclets_add = use MExprAst in
  lam n. lam body. lam reclets.
  match reclets with TmRecLets t then
    let newbind = {ident = n, body = body} in
    TmRecLets {t with bindings = cons newbind t.bindings}
  else
    error "reclets is not a TmRecLets construct"

let reclets_add = use MExprAst in
  lam s. lam body. lam reclets.
  nreclets_add (nameNoSym s) body reclets

let ncondef_ = use MExprAst in
  lam n. lam tpe.
  TmConDef {ident = n, tpe = tpe, inexpr = unit_}

let condef_ = use MExprAst in
  lam s. lam tpe.
  ncondef_ (nameNoSym s) tpe

let nucondef_ = use MExprAst in
  lam n.
  ncondef_ n tydyn_

let ucondef_ = use MExprAst in
  lam s.
  condef_ s tydyn_

let nvar_ = use MExprAst in
  lam n.
  TmVar {ident = n}

let var_ = use MExprAst in
  lam s.
  nvar_ (nameNoSym s)

let nconapp_ = use MExprAst in
  lam n. lam b.
  TmConApp {ident = n, body = b}

let conapp_ = use MExprAst in
  lam s. lam b.
  nconapp_ (nameNoSym s) b

let const_ = use MExprAst in
  lam c.
  TmConst {val = c}

let nlam_ = use MExprAst in
  lam n. lam tpe. lam body.
  TmLam {ident = n, tpe = tpe, body = body}

let lam_ = use MExprAst in
  lam s. lam tpe. lam body.
  nlam_ (nameNoSym s) tpe body

let nulam_ = use MExprAst in
  lam n. lam body.
  nlam_ n tydyn_ body

let ulam_ = use MExprAst in
  lam s. lam body.
  lam_ s tydyn_ body

let ulams_ = use MExprAst in
  lam idents. lam body.
  foldr (lam s. lam acc. ulam_ s acc) body idents

let if_ = use MExprAst in
  lam cond. lam thn. lam els.
  TmMatch {target = cond, pat = ptrue_, thn = thn, els = els}

let match_ = use MExprAst in
  lam target. lam pat. lam thn. lam els.
  TmMatch {target = target, pat = pat, thn = thn, els = els}

let seq_ = use MExprAst in
  lam tms.
  TmSeq {tms = tms}

let record_ = use MExprAst in
  lam bindings.
  TmRecord {bindings = bindings}

let tuple_ = use MExprAst in
  lam tms.
  record_ (mapi (lam i. lam t. (int2string i,t)) tms)

let record_empty = unit_

let record_add = use MExprAst in
  lam key. lam value. lam record.
  match record with TmRecord t then
      TmRecord {t with bindings = cons (key, value) t.bindings}
  else
      error "record is not a TmRecord construct"

let record_add_bindings = lam bindings. lam record.
  foldl (lam recacc. lam b. record_add b.0 b.1 recacc) record bindings

let never_ = use MExprAst in
  TmNever {}

let nrecordproj_ = use MExprAst in
  lam name. lam key. lam r.
  -- It is fine to use any variable name here. It doesn't matter if it
  -- overwrites a previous binding, since that binding will never be used in
  -- the then clause in any case.
  match_ r (prec_ [(key,npvar_ name)]) (nvar_ name) never_

let recordproj_ = use MExprAst in
  lam key. lam r.
  nrecordproj_ (nameNoSym "x") key r

let tupleproj_ = use MExprAst in
  lam i. lam t.
  recordproj_ (int2string i) t

let recordupdate_ = use MExprAst in
  lam rec. lam key. lam value.
  TmRecordUpdate {rec = rec, key = key, value = value}

let app_ = use MExprAst in
  lam l. lam r.
  TmApp {lhs = l, rhs = r}

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

let utest_ = use MExprAst in
  lam t. lam e. lam n.
  TmUtest {test = t, expected = e, next = n}

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

let char_ = use MExprAst in
  lam c.
  const_ (CChar {val = c})

let str_ = use MExprAst in
  lam s.
  TmSeq {tms = map char_ s}

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

let not_ = use MExprAst in
  lam a.
  appf1_ (const_ (CNot ())) a

let eqi_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CEqi ())) a b

let lti_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLti ())) a b

let eqf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CEqf ())) a b

let eqs_ = use MExprAst in
  lam s1. lam s2.
  appf2_ (const_ (CEqs ())) s1 s2

let ltf_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CLtf ())) a b

let nth_ = use MExprAst in
  lam s. lam i.
  appf2_ (const_ (CGet ())) s i

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

let head_ = use MExprAst in
  lam s.
  appf1_ (const_ (CHead ())) s

let tail_ = use MExprAst in
  lam s.
  appf1_ (const_ (CTail ())) s

let null_ = use MExprAst in
  lam s.
  appf1_ (const_ (CNull ())) s

let reverse_ = use MExprAst in
  lam s.
  appf1_ (const_ (CReverse ())) s
