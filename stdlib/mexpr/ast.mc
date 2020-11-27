-- Language fragments of MExpr

include "string.mc"
include "name.mc"
include "assoc.mc"
include "mexpr/info.mc"

-----------
-- TERMS --
-----------

lang VarAst
  syn Expr =
  | TmVar {ident : Name, fi: Info}

  sem info =
  | TmVar r -> r.fi

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmVar t -> TmVar t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmVar t -> acc
end

lang AppAst
  syn Expr =
  | TmApp {lhs : Expr, rhs : Expr, fi: Info}

  sem info =
  | TmApp r -> r.fi

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmApp t -> TmApp {lhs = f t.lhs, rhs = f t.rhs}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmApp t -> f (f acc t.lhs) t.rhs

end

lang FunAst = VarAst + AppAst
  syn Expr =
  | TmLam {ident : Name,
           ty    : Type,
           body  : Expr,
           fi    : Info}

  sem info =
  | TmLam r -> r.fi

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
  | TmRecord t -> TmRecord {bindings = assocMap {eq=eqString} f t.bindings}
  | TmRecordUpdate t -> TmRecordUpdate {{t with rec = f t.rec}
                                           with value = f t.value}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecord t -> assocFold {eq=eqString} (lam acc. lam _k. lam v. f acc v) acc t.bindings
  | TmRecordUpdate t -> f (f acc t.rec) t.value
end

lang LetAst = VarAst
  syn Expr =
  | TmLet {ident  : Name,
           ty     : Type,
           body   : Expr,
           inexpr : Expr,
	   fi     : Info}

  sem info =
  | TmLet r -> r.fi

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLet t -> TmLet {{t with body = f t.body} with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLet t -> f (f acc t.body) t.inexpr
end

lang RecLetsAst = VarAst
  syn Expr =
  | TmRecLets {bindings : [{ident : Name,
                            ty    : Type,
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
  | TmConst {val : Const, fi: Info}

  sem info =
  | TmConst r -> r.fi

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConst t -> TmConst t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConst t -> acc
end

lang DataAst
  syn Expr =
  | TmConDef {ident  : Name,
              ty     : Type,
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
             els    : Expr,
             fi     : Info}

  syn Pat =

  sem info =
  | TmMatch r -> r.fi

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
  | TmSeq {tms : [Expr], fi: Info}

  sem info =
  | TmSeq r -> r.fi

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmSeq t -> TmSeq {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmSeq t -> foldl f acc t.tms
end

lang NeverAst
  syn Expr =
  | TmNever {fi: Info}

  sem info =
  | TmNever r -> r.fi

  -- TODO(dlunde,2020-09-29): smap, sfold
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
  | CNot {} -- TODO(dlunde,2020-09-29): This constant does not exist in boot. Remove?
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
  | CEqsym {}
end

-- TODO(dlunde,2020-09-29): Remove constants no longer available in boot?
lang SeqOpAst = SeqAst
  syn Const =
  | CSet {}
  | CGet {}
  | CCons {}
  | CSnoc {}
  | CConcat {}
  | CLength {}
  | CReverse {}
  | CMakeSeq {}
  | CSplitAt {}
end

--------------
-- PATTERNS --
--------------

type PatName
con PName     : Name -> PatName
con PWildcard : ()   -> PatName

lang NamedPat
  syn Pat =
  | PNamed {ident : PatName}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PNamed p -> PNamed p

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PNamed _ -> acc
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
  | PSeqEdge {prefix : [Pat], middle: PatName, postfix : [Pat]}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PSeqEdge p -> PSeqEdge {{p with prefix = map f p.prefix} with postfix = map f p.postfix}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PSeqEdge {prefix = pre, postfix = post} -> foldl f (foldl f acc pre) post
end

lang RecordPat
  syn Pat =
  | PRecord {bindings : AssocMap String Pat}

  sem smap_Pat_Pat (f : Pat -> a) =
  | PRecord b -> PRecord {b with bindings = assocMap {eq=eqString} (lam b. (b.0, f b.1)) b.bindings}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PRecord {bindings = bindings} -> assocFold {eq=eqString} (lam acc. lam _k. lam v. f acc v) acc bindings
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
  | PBool {val : Bool, fi : Info}

  sem info =
  | PBool r -> r.fi

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

lang UnitTypeAst
  syn Type =
  | TyUnit {}
end

lang UnknownTypeAst
  syn Type =
  | TyUnknown {}
end

lang BoolTypeAst
  syn Type =
  | TyBool {}
end

lang IntTypeAst
  syn Type =
  | TyInt {}
end

lang FloatTypeAst
  syn Type =
  | TyFloat {}
end

lang CharTypeAst
  syn Type =
  | TyChar {}
end

lang FunTypeAst
  syn Type =
  | TyArrow {from : Type,
             to   : Type}
end

lang SeqTypeAst
  syn Type =
  | TySeq {ty : Type}
end

lang TupleTypeAst
  syn Type =
  | TyTuple {tys : [Type]}
end

lang RecordTypeAst
  syn Type =
  | TyRecord {fields : [{ident : String,
                         ty    : Type}]}
end

lang DataTypeAst
  syn Type =
  | TyCon {ident : Name}
end

lang AppTypeAst
  syn Type =
  | TyApp {lhs : Type, rhs : Type}
end

lang StringTypeAst
  syn Type =
  | TyString {}
end

lang TypeVarAst
  syn Type =
  | TyVar {ident : Name}
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
  + NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat

  -- Types
  + FunTypeAst + UnknownTypeAst + UnitTypeAst + CharTypeAst + StringTypeAst +
  SeqTypeAst + TupleTypeAst + RecordTypeAst + DataTypeAst + IntTypeAst +
  FloatTypeAst + BoolTypeAst + AppTypeAst + TypeVarAst
