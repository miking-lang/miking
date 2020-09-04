-- Language fragments of MExpr

include "string.mc"
include "name.mc"
include "assoc.mc"

-----------
-- TERMS --
-----------

lang VarAst
  syn Expr =
  | TmVar {ident : Name}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmVar t -> TmVar t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmVar t -> acc
end

lang AppAst
  syn Expr =
  | TmApp {lhs : Expr,
           rhs : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmApp t -> TmApp {lhs = f t.lhs, rhs = f t.rhs}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmApp t -> f (f acc t.lhs) t.rhs
end

lang FunAst = VarAst + AppAst
  syn Expr =
  | TmLam {ident : Name,
           tpe   : Option,
           body  : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLam t -> TmLam {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLam t -> f acc t.body
end

lang RecordAst
  syn Expr =
  | TmRecord {bindings : AssocMap String Expr}
  | TmRecordUpdate {rec   : Expr,
                    key   : String,
                    value : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecord t -> TmRecord {bindings = map (lam b. (b.0, f b.1)) t.bindings}
  | TmRecordUpdate t -> TmRecordUpdate {{t with rec = f t.rec}
                                           with value = f t.value}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecord t -> foldl f acc (map (lam b. b.1) t.bindings)
  | TmRecordUpdate t -> f (f acc t.rec) t.value
end

lang LetAst = VarAst
  syn Expr =
  | TmLet {ident  : Name,
           body   : Expr,
           inexpr : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLet t -> TmLet {{t with body = f t.body} with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLet t -> f (f acc t.body) t.inexpr
end

lang RecLetsAst = VarAst
  syn Expr =
  | TmRecLets {bindings : [{ident : Name,
                            body  : Expr}],
               inexpr   : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecLets t ->
    TmRecLets {{t with bindings = map (lam b. {b with body = f b.body})
                                      t.bindings}
                  with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecLets t -> f (foldl f acc (map (lam b. b.body) t.bindings)) t.inexpr
end

lang ConstAst
  syn Const =

  syn Expr =
  | TmConst {val : Const}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConst t -> TmConst t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConst t -> acc
end

lang DataAst
  syn Expr =
  | TmConDef {ident  : Name,
              tpe    : Option,
              inexpr : Expr}
  | TmConApp {ident : Name,
              body : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConDef t -> TmConDef {t with inexpr = f t.inexpr}
  | TmConApp t -> TmConApp {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConDef t -> f acc t.inexpr
  | TmConApp t -> f acc t.body
end

lang MatchAst
  syn Expr =
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr}

  syn Pat =

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmMatch t -> TmMatch {{{t with target = f t.target}
                              with thn = f t.thn}
                              with els = f t.els}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmMatch t -> f (f (f acc t.target) t.thn) t.els
end

lang UtestAst
  syn Expr =
  | TmUtest {test     : Expr,
             expected : Expr,
             next     : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmUtest t -> TmUtest {{{t with test = f t.test}
                              with expected = f t.expected}
                              with next = f t.next}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmUtest t -> f (f (f acc t.test) t.expected) t.next
end

lang SeqAst
  syn Expr =
  | TmSeq {tms : [Expr]}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmSeq t -> TmSeq {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmSeq t -> foldl f acc t.tms
end

lang NeverAst
  syn Expr =
  | TmNever {}

  -- TODO smap, sfold?
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

lang IntAst = ConstAst
  syn Const =
  | CInt {val : Int}
end

lang ArithIntAst = ConstAst + IntAst
  syn Const =
  | CAddi {}
  | CSubi {}
  | CMuli {}
end

lang FloatAst = ConstAst
  syn Const =
  | CFloat {val : Float}
end

lang ArithFloatAst = ConstAst + FloatAst
  syn Const =
  | CAddf {}
  | CSubf {}
  | CMulf {}
  | CDivf {}
  | CNegf {}
end

lang BoolAst = ConstAst
  syn Const =
  | CBool {val : Bool}
  | CNot {}
end

lang CmpIntAst = IntAst + BoolAst
  syn Const =
  | CEqi {}
  | CLti {}
end

lang CmpFloatAst = FloatAst + BoolAst
  syn Const =
  | CEqf {}
  | CLtf {}
end

lang CharAst = ConstAst
  syn Const =
  | CChar {val : Char}
end

lang SymbAst = ConstAst
  syn Const =
  | CSymb {val : Symb}
end

lang CmpSymbAst = SymbAst + BoolAst
  syn Const =
  | CEqs {}
end

-- TODO Remove constants no longer available in boot?
lang SeqOpAst = SeqAst
  syn Const =
  | CGet {}
  | CCons {}
  | CSnoc {}
  | CConcat {}
  | CLength {}
  | CHead {}
  | CTail {}
  | CNull {}
  | CReverse {}
end

--------------
-- PATTERNS --
--------------

type PatName
con PName     : Name -> PatName
con PWildcard : ()   -> PatName
lang VarPat
  syn Pat =
  | PVar {ident : PatName}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PVar p -> PVar p

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PVar _ -> acc
end

lang SeqTotPat
  syn Pat =
  | PSeqTot { pats : [Pat] }

  sem smap_Pat_Pat (f : Pat -> a) =
  | PSeqTot p -> PSeqTot {p with pats = map f p.pats}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PSeqTot {pats = pats} -> foldl f acc pats
end

lang SeqEdgePat
  syn Pat =
  | PSeqEdge {prefix : [Pat], postfix : [Pat]}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PSeqEdge p -> PSeqEdge {{p with prefix = map f p.prefix} with postfix = map f p.postfix}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PSeqEdge {prefix = pre, postfix = post} -> foldl f (foldl f acc pre) post
end

lang RecordPat
  syn Pat =
  | PRecord {bindings : AssocMap String Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PRecord b -> PRecord {b with bindings = map (lam b. (b.0, f b.1)) b.bindings}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PRecord {bindings = bindings} -> foldl f acc (map (lam b. b.1) bindings)
end

lang DataPat = DataAst
  syn Pat =
  | PCon {ident  : Name,
          subpat : Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PCon c -> PCon {c with subpat = f c.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PCon {subpat = subpat} -> f acc subpat
end

lang IntPat = IntAst
  syn Pat =
  | PInt {val : Int}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PInt v -> PInt v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PInt _ -> acc
end

lang CharPat
  syn Pat =
  | PChar {val : Char}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PChar v -> PChar v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PChar _ -> acc
end

lang BoolPat = BoolAst
  syn Pat =
  | PBool {val : Bool}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PBool v -> PBool v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PBool _ -> acc
end

lang AndPat
  syn Pat =
  | PAnd {lpat : Pat, rpat : Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PAnd p -> PAnd {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PAnd {lpat = l, rpat = r} -> f (f acc l) r
end

lang OrPat
  syn Pat =
  | POr {lpat : Pat, rpat : Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | POr p -> POr {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | POr {lpat = l, rpat = r} -> f (f acc l) r
end

lang NotPat
  syn Pat =
  | PNot {subpat : Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PNot p -> PNot {p with subpat = f p.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PNot {subpat = p} -> f acc p
end

-----------
-- TYPES --
-----------
-- TODO Update (also not up to date in boot?)

lang FunTypeAst
  syn Type =
  | TyArrow {from : Type,
             to   : Type}
end

lang DynTypeAst
  syn Type =
  | TyDyn {}
end

lang UnitTypeAst
  syn Type =
  | TyUnit {}
end

lang CharTypeAst
  syn Type =
  | TyChar {}
  | TyString {}
end

lang SeqTypeAst
  syn Type =
  | TySeq {tpe : Type}
end

lang TupleTypeAst
  syn Type =
  | TyProd {tpes : [Type]}
end

lang RecordTypeAst
  syn Type =
  | TyRecord {tpes : [{ident : String,
                       tpe   : Type}]}
end

lang DataTypeAst
  syn Type =
  | TyCon {ident : String}
end

lang ArithTypeAst
  syn Type =
  | TyInt {}
end

lang BoolTypeAst
  syn Type =
  | TyBool {}
end

lang AppTypeAst
  syn Type =
  | TyApp {lhs : Type, rhs : Type}
end

------------------------
-- MEXPR AST FRAGMENT --
------------------------

lang MExprAst =

  -- Terms
  VarAst + AppAst + FunAst + RecordAst + LetAst + RecLetsAst + ConstAst +
  DataAst + MatchAst + UtestAst + SeqAst + NeverAst

  -- Constants
  + IntAst + ArithIntAst + FloatAst + ArithFloatAst + BoolAst +
  CmpIntAst + CmpFloatAst + CharAst + SymbAst + CmpSymbAst + SeqOpAst

  -- Patterns
  + VarPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat

  -- Types
  + FunTypeAst + DynTypeAst + UnitTypeAst + CharTypeAst + SeqTypeAst +
  TupleTypeAst + RecordTypeAst + DataTypeAst + ArithTypeAst + BoolTypeAst +
  AppTypeAst

-----------------------
-- BUILDER FUNCTIONS --
-----------------------
-- Duplicates of required function in ast-builder.mc, since we cannot include
-- it (circularity). TODO Merge with ast-mc?

let app_ = use MExprAst in
  lam l. lam r.
  TmApp {lhs = l, rhs = r}

let const_ = use MExprAst in
  lam c.
  TmConst {val = c}

let char_ = use MExprAst in
  lam c.
  const_ (CChar {val = c})

let utest_ = use MExprAst in
  lam t. lam e. lam n.
  TmUtest {test = t, expected = e, next = n}

let punit_ = use MExprAst in
  PRecord { bindings = assocEmpty }

let match_ = use MExprAst in
  lam target. lam pat. lam thn. lam els.
  TmMatch {target = target, pat = pat, thn = thn, els = els}

let nconapp_ = use MExprAst in
  lam n. lam b.
  TmConApp {ident = n, body = b}

let conapp_ = use MExprAst in
  lam s. lam b.
  nconapp_ (nameNoSym s) b

let unit_ = use MExprAst in
  TmRecord {bindings = assocEmpty }

let ncondef_ = use MExprAst in
  lam n. lam tpe.
  TmConDef {ident = n, tpe = tpe, inexpr = unit_}

let condef_ = use MExprAst in
  lam s. lam tpe.
  ncondef_ (nameNoSym s) tpe

let tydyn_ = use MExprAst in
  TyDyn ()

let nucondef_ = use MExprAst in
  lam n.
  ncondef_ n tydyn_

let ucondef_ = use MExprAst in
  lam s.
  condef_ s tydyn_

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

let recordupdate_ = use MExprAst in
  lam rec. lam key. lam value.
  TmRecordUpdate {rec = rec, key = key, value = value}

let record_ = use MExprAst in
  lam bindings.
  TmRecord {bindings = bindings}

let seq_ = use MExprAst in
  lam tms.
  TmSeq {tms = tms}

let true_ = use MExprAst in
  const_ (CBool {val = true})

let false_ = use MExprAst in
  const_ (CBool {val = false})

let int_ = use MExprAst in
  lam i.
  const_ (CInt {val = i})

let pbool_ = use MExprAst in
  lam v.
  PBool {val = v}

let ptrue_ = use MExprAst in
  pbool_ true

let pfalse_ = use MExprAst in
  pbool_ false

let if_ = use MExprAst in
  lam cond. lam thn. lam els.
  TmMatch {target = cond, pat = ptrue_, thn = thn, els = els}

let nreclets_ = use MExprAst in
  lam bs.
  TmRecLets {bindings = map (lam t. {ident = t.0, body = t.1}) bs,
             inexpr = unit_}

let reclets_ = use MExprAst in
  lam bs.
  nreclets_ (map (lam b. (nameNoSym b.0, b.1)) bs)

let nlet_ = use MExprAst in
  lam n. lam body.
  TmLet {ident = n, body = body, inexpr = unit_}

let let_ = use MExprAst in
  lam s. lam body.
  nlet_ (nameNoSym s) body

let tydyn_ = use MExprAst in
  TyDyn ()

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

let nvar_ = use MExprAst in
  lam n.
  TmVar {ident = n}

let var_ = use MExprAst in
  lam s.
  nvar_ (nameNoSym s)

let npvar_ = use MExprAst in
  lam n.
  PVar {ident = PName n}

let pvar_ = use MExprAst in
  lam s.
  npvar_ (nameNoSym s)

let pwild_ = use MExprAst in
  PVar {ident = PWildcard ()}

let pseqtot_ = use MExprAst in
  lam pats.
  PSeqTot {pats = pats}

-----------
-- TESTS --
-----------

mexpr
use MExprAst in

-- smap and sfold tests

let tmVarX = (var_ "x") in
let tmVarY = (var_ "y") in
let tmVarZ = (var_ "z") in
let tmVarU = (var_ "u") in
let tmVarW = (var_ "w") in
let map2varX = lam x. tmVarX in
let fold2seq = lam a. lam e. cons e a in

utest smap_Expr_Expr map2varX tmVarY with tmVarY in
utest sfold_Expr_Expr fold2seq [] tmVarY with [] in

let tmApp = app_ tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmApp with app_ tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmApp with [tmVarZ, tmVarY] in


let tmLam = ulam_ "x" tmApp in

utest smap_Expr_Expr map2varX tmLam with ulam_ "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLam with [tmApp] in


let tmLet = bind_ (let_ "y" tmLam) tmVarY in

utest smap_Expr_Expr map2varX tmLet with bind_ (let_ "y" tmVarX) tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLet with [tmVarY, tmLam] in


let tmRecLets = bind_ (reclets_ [("x", tmApp), ("u", tmVarW)]) tmVarU in

utest smap_Expr_Expr map2varX tmRecLets
with
bind_ (reclets_ [("x", tmVarX), ("u", tmVarX)])
  tmVarX
in
utest sfold_Expr_Expr fold2seq [] tmRecLets with [tmVarU, tmVarW, tmApp] in


let tmConst1 = int_ 1 in
let tmConst2 = int_ 2 in
let tmConst3 = int_ 3 in
let tmApp11 = app_ tmConst1 tmConst2 in

utest smap_Expr_Expr (lam x. 0) tmConst1 with tmConst1 in
utest sfold_Expr_Expr fold2seq [] tmConst1 with [] in


let ite1 = if_ true_ true_ false_ in
let ite2 = if_ false_ false_ true_ in
let ite3 = if_ false_ (int_ 1) (int_ 4) in
let negateBool = lam tm. match tm with TmConst c then
                           match c.val with CBool v then
                             match v.val with true then false_ else true_
                           else tm
                         else tm
in
let countConsts = lam tm. match tm with TmConst _ then 1 else 0 in

utest smap_Expr_Expr negateBool ite1 with ite2 in
utest sfold_Expr_Expr addi 0 (smap_Expr_Expr countConsts ite3) with 3 in

let tmSeq = seq_ [tmApp11, tmConst2, tmConst3] in

utest smap_Expr_Expr map2varX tmSeq with seq_ [tmVarX, tmVarX, tmVarX] in
utest sfold_Expr_Expr fold2seq [] tmSeq with [tmConst3, tmConst2, tmApp11] in

let mkTmRecordXY = lam x. lam y. record_ [("x", x), ("y", y)] in
let tmRecordI = mkTmRecordXY tmApp11 tmConst3 in

utest smap_Expr_Expr map2varX tmRecordI
with record_ [("x", tmVarX), ("y", tmVarX)] in

utest sfold_Expr_Expr fold2seq [] tmRecordI with [tmConst3, tmApp11] in

let tmRecordUpdate = recordupdate_ tmRecordI "x" tmVarY in

utest smap_Expr_Expr map2varX tmRecordUpdate with recordupdate_ tmVarX "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmRecordUpdate with [tmVarY, tmRecordI] in


let tmCon = bind_ (ucondef_ "y") tmApp in

utest smap_Expr_Expr map2varX tmCon with bind_ (ucondef_ "y") tmVarX in
utest sfold_Expr_Expr fold2seq [] tmCon with [tmApp] in


let tmConApp = conapp_ "y" tmApp in

utest smap_Expr_Expr map2varX tmConApp with conapp_ "y" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmConApp with [tmApp] in


let tmMatch = match_ tmApp punit_ tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmMatch
with match_ tmVarX punit_ tmVarX tmVarX in

utest sfold_Expr_Expr fold2seq [] tmMatch with [tmVarZ, tmVarY, tmApp] in

let tmUtest = utest_ tmApp tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmUtest with utest_ tmVarX tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmUtest with [tmVarZ, tmVarY, tmApp] in

let pSeqTot = pseqtot_ [ptrue_, pfalse_] in

utest smap_Pat_Pat (lam x. pseqtot_ [x]) pSeqTot
with pseqtot_ [pseqtot_ [ptrue_], pseqtot_ [pfalse_]] in

-- recursive schemes tests
let tmConst1C = char_ (int2char 1) in
let tmConst2C = char_ (int2char 2) in
let tmConst3C = char_ (int2char 3) in
let tmApp11C = app_ tmConst1C tmConst2C in
let tmRecordC = mkTmRecordXY tmApp11C tmConst3C in

let cInt2cChar =
lam e. match e with TmConst t then
         match t.val with CInt i
           then TmConst {val = CChar {val = int2char i.val}}
         else e
       else e
in

recursive let bottomUp = lam f.
  compose f (smap_Expr_Expr (lam e. bottomUp f e))
in

recursive let topDown = lam f.
  compose (smap_Expr_Expr (lam e. topDown f e)) f
in

let countNodes = bottomUp (sfold_Expr_Expr addi 1) in

utest bottomUp identity tmVarX with tmVarX in
utest bottomUp cInt2cChar tmRecordI with tmRecordC in
utest countNodes tmVarX with 1 in
utest countNodes tmApp11C with 3 in
utest countNodes tmRecordC with 5 in

recursive let foldi = lam f. lam a. lam e.
  compose (lam a. sfold_Expr_Expr (foldi f) a e) (f a) e
in

utest foldi fold2seq [] tmVarX with [tmVarX] in
utest foldi fold2seq [] tmApp11C with [tmConst2C, tmConst1C, tmApp11C] in
utest foldi fold2seq [] tmRecordC
with [tmConst3C, tmConst2C, tmConst1C, tmApp11C, tmRecordC] in
()
