-- Convenience functions for manually constructing ASTs

include "ast.mc"

-- Methods of binding an expression into a chain of lets --
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


-- Constant values --
let const_ = use MExprAst in
  lam c.
  TmConst {val = c}

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

let var_ = use MExprAst in
  lam s.
  TmVar {ident = s}

let conapp_ = use MExprAst in
  lam s. lam b.
  TmConApp {ident = s, body = b}

-- Never term
let never_ = use MExprAst in
  TmNever {}

-- Patterns --
let pvar_ = use MExprAst in
  lam s.
  PVar {ident = s}

let punit_ = use MExprAst in
  PRecord { bindings = [] }

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

let pcon_ = use MExprAst in
  lam cs. lam cp.
  PCon {ident = cs, subpat = cp}

let prec_ = use MExprAst in
  lam bindings.
  PRecord {bindings = bindings}

let ptuple_ = use MExprAst in
  lam ps.
  prec_ (mapi (lam i. lam p. (int2string i,p)) ps)

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

-- Control flows --
let lam_ = use MExprAst in
  lam ident. lam tpe. lam body.
  TmLam {ident = ident, tpe = tpe, body = body}

let ulam_ = use MExprAst in
  lam ident. lam body.
  lam_ ident tydyn_ body

let ulams_ = use MExprAst in
  lam idents. lam body.
  foldr (lam ident. lam acc. ulam_ ident acc) body idents

let if_ = use MExprAst in
  lam cond. lam thn. lam els.
  TmMatch {target = cond, pat = ptrue_, thn = thn, els = els}

let match_ = use MExprAst in
  lam target. lam pat. lam thn. lam els.
  TmMatch {target = target, pat = pat, thn = thn, els = els}

-- Sequence, tuple, and record
let seq_ = use MExprAst in
  lam tms.
  TmSeq {tms = tms}

let record_ = use MExprAst in
  lam bindings.
  TmRecord {bindings = bindings}

let tuple_ = use MExprAst in
  lam tms.
  record_ (mapi (lam i. lam t. (int2string i,t)) tms)

let record_empty = use MExprAst in
  TmRecord {bindings = []}

let unit_ = record_empty

let record_add = use MExprAst in
  lam key. lam value. lam record.
  match record with TmRecord t then
      TmRecord {t with bindings = cons (key, value) t.bindings}
  else
      error "record is not a TmRecord construct"

let record_add_bindings = lam bindings. lam record.
  foldl (lam recacc. lam b. record_add b.0 b.1 recacc) record bindings

let recordproj_ = use MExprAst in
  lam key. lam r.
  -- It is fine to use any variable name here. It doesn't matter if it
  -- overwrites a previous binding, since that binding will never be used in
  -- the then clause in any case (TODO double check this).
  match_ r (prec_ [(key,pvar_ "x")]) (var_ "x") never_

let tupleproj_ = use MExprAst in
  lam i. lam t.
  recordproj_ (int2string i) t

let recordupdate_ = use MExprAst in
  lam key. lam value. lam rec.
  TmRecordUpdate {rec = rec, key = key, value = value}



-- Application helpers --
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


-- Application of built-in functions --
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

let and_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (CAnd ())) a b

let or_ = use MExprAst in
  lam a. lam b.
  appf2_ (const_ (COr ())) a b

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


-- Let expressions (use bind_ or bindall_ to set inexpr) --
let let_ = use MExprAst in
  lam ident. lam tpe. lam body.
  TmLet {ident = ident, tpe = tpe, body = body, inexpr = unit_}

let ulet_ = use MExprAst in
  lam ident. lam body.
  let_ ident tydyn_ body

let reclets_ = use MExprAst in
  lam bindings.
  TmRecLets {bindings = bindings, inexpr = unit_}

let reclet_ = use MExprAst in
  lam ident. lam tpe. lam body.
  reclets_ [{ident = ident, tpe = tpe, body = body}]

let ureclet_ = use MExprAst in
  lam ident. lam body.
  reclet_ ident tydyn_ body

let reclets_empty = use MExprAst in
  TmRecLets {bindings = [], inexpr = unit_}

let reclets_add = use MExprAst in
  lam ident. lam tpe. lam body. lam reclets.
  match reclets with TmRecLets t then
    let newbind = {ident = ident, tpe = tpe, body = body} in
    TmRecLets {t with bindings = cons newbind t.bindings}
  else
    error "reclets is not a TmRecLets construct"

let condef_ = use MExprAst in
  lam s. lam tpe.
  TmConDef {ident = s, tpe = tpe, inexpr = unit_}


