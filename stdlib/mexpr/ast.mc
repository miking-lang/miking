include "string.mc"

lang VarAst
  syn Expr =
  | TmVar {ident : String}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmVar t -> TmVar t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmVar t -> acc
end

lang VarPat
  syn Pat =
  | PVar {ident : String}
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
  syn Type =
  | TyArrow {from : Type,
             to   : Type}
  syn Expr =
  | TmLam {ident : String,
           tpe   : Option,
           body  : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLam t -> TmLam {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLam t -> f acc t.body
end


lang LetAst = VarAst
  syn Expr =
  | TmLet {ident  : String,
           tpe    : Option,
           body   : Expr,
           inexpr : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLet t -> TmLet {{t with body = f t.body} with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLet t -> f (f acc t.body) t.inexpr
end


lang RecLetsAst = VarAst
  syn Type =
  syn Expr =
  | TmRecLets {bindings : [{ident : String,
                            tpe   : Option,
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


lang UnitAst = ConstAst
  syn Const =
  | CUnit {}
end

lang UnitPat = UnitAst
  syn Pat =
  | PUnit {}
end


lang IntAst = ConstAst
  syn Const =
  | CInt {val : Int}
end

lang IntPat = IntAst
  syn Pat =
  | PInt {val : Int}
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

lang BoolAst
  syn Const =
  | CBool {val : Bool}
  | CNot {}
  | CAnd {}
  | COr {}

  syn Expr =
  | TmIf {cond : Expr,
          thn  : Expr,
          els  : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmIf t -> TmIf {cond = f t.cond, thn = f t.thn, els = f t.els}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmIf t -> f (f (f acc t.cond) t.thn) t.els
end

lang BoolPat = BoolAst
  syn Pat =
  | PBool {val : Bool}
end


lang CmpAst = IntAst + BoolAst
  syn Const =
  | CEqi {}
  | CLti {}
end


lang CharAst = ConstAst
  syn Const =
  | CChar {val : Char}
end


lang SeqAst = IntAst
  syn Const =
  | CSeq {tms : [Expr]}
  | CGet {}

  syn Expr =
  | TmSeq {tms : [Expr]}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmSeq t -> TmSeq {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmSeq t -> foldl f acc t.tms
end


lang TupleAst
  syn Expr =
  | TmTuple {tms : [Expr]}
  | TmProj {tup : Expr,
            idx : Int}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmTuple t -> TmTuple {t with tms = map f t.tms}
  | TmProj t -> TmProj {t with tup = f t.tup}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmTuple t -> foldl f acc t.tms
  | TmProj t -> f acc t.tup
end

lang TuplePat = TupleAst
  syn Pat =
  | PTuple {pats : [Pat]}
end


lang RecordAst
  syn Expr =
  | TmRecord {bindings : [{key   : String,
                           value : Expr}]}
  | TmRecordProj {rec : Expr,
                  key : String}
  | TmRecordUpdate {rec   : Expr,
                    key   : String,
                    value : Expr}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecord t -> TmRecord {t with
                            bindings = map (lam b. {b with value = f b.value})
                                           t.bindings}

  | TmRecordProj t -> TmRecordProj {t with rec = f t.rec}
  | TmRecordUpdate t -> TmRecordUpdate {{t with rec = f t.rec}
                                           with value = f t.value}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecord t -> foldl f acc (map (lam b. b.value) t.bindings)
  | TmRecordProj t -> f acc t.rec
  | TmRecordUpdate t -> f (f acc t.rec) t.value
end


lang DataAst
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef {ident  : String,
              tpe    : Option,
              inexpr : Expr}
  | TmConFun {ident : String}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConDef t -> TmConDef {t with inexpr = f t.inexpr}
  | TmConFun t -> TmConFun t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConDef t -> f acc t.inexpr
  | TmConFun t -> acc
end

lang DataPat = DataAst
  syn Pat =
  | PCon {ident  : String,
          subpat : Pat}
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


lang MExprAst =
  VarAst + AppAst + FunAst + LetAst + RecLetsAst + ConstAst +
  UnitAst + UnitPat + IntAst + IntPat + FloatAst + ArithFloatAst +
  ArithIntAst + BoolAst + BoolPat + CmpAst + CharAst + SeqAst +
  TupleAst + TuplePat + DataAst + DataPat + MatchAst + VarPat + UtestAst +
  RecordAst +
  DynTypeAst + UnitTypeAst + CharTypeAst + SeqTypeAst + TupleTypeAst +
  RecordTypeAst + DataTypeAst + ArithTypeAst + BoolTypeAst +
  AppTypeAst

mexpr
use MExprAst in

-- smap and sfold tests

let var_ = lam v. TmVar {ident = v} in
let tmVarX = (var_ "x") in
let tmVarY = (var_ "y") in
let tmVarZ = (var_ "z") in
let tmVarU = (var_ "u") in
let tmVarW = (var_ "w") in
let map2varX = lam x. tmVarX in
let fold2seq = lam a. lam e. cons e a in

utest smap_Expr_Expr map2varX tmVarY with tmVarY in
utest sfold_Expr_Expr fold2seq [] tmVarY with [] in

let app_ = lam l. lam r. TmApp {lhs = l, rhs = r} in
let tmApp = app_ tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmApp with app_ tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmApp with [tmVarZ, tmVarY] in


let lam_ = lam id. lam b. TmLam {ident = id, tpe = None (), body = b} in
let tmLam = lam_ "x" tmApp in

utest smap_Expr_Expr map2varX tmLam with lam_ "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLam with [tmApp] in


let let_ = lam id. lam b. lam ine.
  TmLet {ident = id, tpe = None (), body = b, inexpr = ine}
in
let tmLet = let_ "y" tmLam tmVarY in

utest smap_Expr_Expr map2varX tmLet with let_ "y" tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLet with [tmVarY, tmLam] in


let bind_ = lam id. lam b. {ident = id, tpe = None (), body = b} in
let reclet_ = lam bs. lam ine.
  TmRecLets {bindings = bs, inexpr = ine}
in
let tmRecLets = reclet_ [bind_ "x" tmApp, bind_ "u" tmVarW] tmVarU in

utest smap_Expr_Expr map2varX tmRecLets
with reclet_ [bind_ "x" tmVarX, bind_ "u" tmVarX] tmVarX in
utest sfold_Expr_Expr fold2seq [] tmRecLets with [tmVarU, tmVarW, tmApp] in


let int_ = lam i. TmConst {value = CInt {value = i}} in
let tmConst1 = int_ 1 in
let tmConst2 = int_ 2 in
let tmConst3 = int_ 3 in
let tmApp11 = app_ tmConst1 tmConst2 in

utest smap_Expr_Expr (lam x. 0) tmConst1 with tmConst1 in
utest sfold_Expr_Expr fold2seq [] tmConst1 with [] in

let if_ = lam cond. lam thn. lam els. TmIf {cond = cond, thn = thn, els = els} in
let true_ = TmConst {val = (CBool {val = true})} in
let false_ = TmConst {val = (CBool {val = false})} in
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

let seq_ = lam tms. TmSeq {tms = tms} in
let tmSeq = seq_ [tmApp11, tmConst2, tmConst3] in

utest smap_Expr_Expr map2varX tmSeq with seq_ [tmVarX, tmVarX, tmVarX] in
utest sfold_Expr_Expr fold2seq [] tmSeq with [tmConst3, tmConst2, tmApp11] in


let tup_ = lam tms. TmTuple {tms = tms} in
let tmTup = (tup_ [tmApp11, tmConst2, tmConst3]) in

utest smap_Expr_Expr map2varX tmTup with tup_ [tmVarX, tmVarX, tmVarX] in
utest sfold_Expr_Expr fold2seq [] tmTup with [tmConst3, tmConst2, tmApp11] in


let proj_ = lam t. lam i. TmProj {tup = t, idx = i} in
let tmProj = proj_ tmTup 1 in
utest smap_Expr_Expr map2varX tmProj with proj_ tmVarX 1 in
utest sfold_Expr_Expr fold2seq [] tmProj with [tmTup] in


let rb_ = lam k. lam v. {key = k, value = v} in
let rec_ = lam bs. TmRecord {bindings = bs} in
let mkTmRecordXY = lam x. lam y. rec_ [rb_ "x" x, rb_ "y" y] in
let tmRecordI = mkTmRecordXY tmApp11 tmConst3 in

utest smap_Expr_Expr map2varX tmRecordI
with rec_ [rb_ "x" tmVarX, rb_ "y" tmVarX] in

utest sfold_Expr_Expr fold2seq [] tmRecordI with [tmConst3, tmApp11] in


let recProj_ = lam r. lam k. TmRecordProj {rec = r, key = k} in
let tmRecordProj = recProj_ tmRecordI "x" in

utest smap_Expr_Expr map2varX tmRecordProj with recProj_ tmVarX "x" in
utest sfold_Expr_Expr fold2seq [] tmRecordProj with [tmRecordI] in


let recUpd_ = lam r. lam k. lam v.
  TmRecordUpdate {rec = r, key = k, value = v}
in
let tmRecordUpdate = recUpd_ tmRecordI "x" tmVarY in

utest smap_Expr_Expr map2varX tmRecordUpdate with recUpd_ tmVarX "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmRecordUpdate with [tmVarY, tmRecordI] in


let con_ = lam id. lam ine.
  TmConDef {ident = id, tpe = None (), inexpr = ine}
in
let tmCon = con_ "y" tmApp in

utest smap_Expr_Expr map2varX tmCon with con_ "y" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmCon with [tmApp] in


let confun_ = lam id. TmConFun {ident = id} in
let tmConFun = confun_ "y" in

utest smap_Expr_Expr map2varX tmConFun with tmConFun in
utest sfold_Expr_Expr fold2seq [] tmConFun with [] in


let match_ = lam t. lam p. lam thn. lam els.
  TmMatch {target = t, pat = p, thn = thn, els = els}
in
let tmMatch = match_ tmApp (PUnit ()) tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmMatch
with match_ tmVarX (PUnit ()) tmVarX tmVarX in

utest sfold_Expr_Expr fold2seq [] tmMatch with [tmVarZ, tmVarY, tmApp] in


let utest_ = lam t. lam e. lam n.
  TmUtest {test = t, expected = e, next = n}
in
let tmUtest = utest_ tmApp tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmUtest with utest_ tmVarX tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmUtest with [tmVarZ, tmVarY, tmApp] in

-- recursive schemes tests
let char_ = lam c. TmConst {value = CChar {value = c}} in
let tmConst1C = char_ (int2char 1) in
let tmConst2C = char_ (int2char 2) in
let tmConst3C = char_ (int2char 3) in
let tmApp11C = app_ tmConst1C tmConst2C in
let tmRecordC = mkTmRecordXY tmApp11C tmConst3C in

let cInt2cChar =
lam e. match e with TmConst t then
         match t.value with CInt i
           then TmConst {value = CChar {value = int2char i.value}}
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
