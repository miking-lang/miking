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

let unit_ = use MExprAst in
  const_ (CUnit ())

let int_ = use MExprAst in
  lam i.
  const_ (CInt {val = i})

let true_ = use MExprAst in
  const_ (CBool {val = true})

let false_ = use MExprAst in
  const_ (CBool {val = false})

let char_ = use MExprAst in
  lam c.
  const_ (CChar {val = c})

let str_ = use MExprAst in
  lam s.
  const_ (CSeq {tms = map char_ s})

let var_ = use MExprAst in
  lam s.
  TmVar {ident = s}

let confun_ = use MExprAst in
  lam s.
  TmConFun {ident = s}


-- Sequence, tuple, and record
let seq_ = use MExprAst in
  lam tms.
  TmSeq {tms = tms}

let tuple_ = use MExprAst in
  lam tms.
  TmTuple {tms = tms}

let proj_ = use MExprAst in
  lam tup. lam idx.
  TmProj {tup = tup, idx = idx}

let record_empty = use MExprAst in
  TmRecord {bindings = []}

let record_add = use MExprAst in
  lam key. lam value. lam record.
  match record with TmRecord t then
      TmRecord {t with bindings = cons {key = key, value = value} t.bindings}
  else
      error "record is not a TmRecord construct"

let recordproj_ = use MExprAst in
  lam key. lam rec.
  TmRecordProj {rec = rec, key = key}

let recordupdate_ = use MExprAst in
  lam key. lam value. lam rec.
  TmRecordUpdate {rec = rec, key = key, value = value}


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


-- Application helpers --
let app_ = use MExprAst in
  lam l. lam r.
  TmApp {lhs = l, rhs = r}

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

let nth_ = use MExprAst in
  lam s. lam i.
  appf2_ (const_ (CGet ())) s i


-- Patterns --
let pvar_ = use MExprAst in
  lam s.
  PVar {ident = s}

let punit_ = use MExprAst in
  PUnit ()

let pint_ = use MExprAst in
  lam i.
  PInt {val = i}

let ptrue_ = use MExprAst in
  PBool {val = true}

let pfalse_ = use MExprAst in
  PBool {val = false}

let ptuple_ = use MExprAst in
  lam pats.
  PTuple {pats = pats}

let pcon_ = use MExprAst in
  lam cs. lam cp.
  PCon {ident = cs, subpat = cp}


-- Let expressions (use bind_ or bindall_ to set inexpr) --
let let_ = use MExprAst in
  lam ident. lam tpe. lam body.
  TmLet {ident = ident, tpe = tpe, body = body, inexpr = unit_}

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


-- Control flows --
let lam_ = use MExprAst in
  lam ident. lam tpe. lam body.
  TmLam {ident = ident, tpe = tpe, body = body}

let if_ = use MExprAst in
  lam cond. lam thn. lam els.
  TmIf {cond = cond, thn = thn, els = els}

let match_ = use MExprAst in
  lam target. lam pat. lam thn. lam els.
  TmMatch {target = target, pat = pat, thn = thn, els = els}
