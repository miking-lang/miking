-- Language fragments of MExpr

include "string.mc"
include "name.mc"
include "assoc.mc"
include "info.mc"
include "mexpr/info.mc"

-----------
-- TERMS --
-----------

-- TmVar --
lang VarAst
  syn Expr =
  | TmVar {ident : Name,
           ty: Type,
           info: Info}

  sem info =
  | TmVar r -> r.info

  sem ty =
  | TmVar t -> t.ty

  sem withType (ty : Type) =
  | TmVar t -> TmVar {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmVar t -> TmVar t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmVar t -> acc
end


-- TmAst --
lang AppAst
  syn Expr =
  | TmApp {lhs : Expr,
           rhs : Expr,
           ty: Type,
           info: Info}

  sem info =
  | TmApp r -> r.info

  sem ty =
  | TmApp t -> t.ty

  sem withType (ty : Type) =
  | TmApp t -> TmApp {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmApp t -> TmApp {{t with lhs = f t.lhs}
                         with rhs = f t.rhs}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmApp t -> f (f acc t.lhs) t.rhs

end


-- TmLam -- 
lang LamAst = VarAst + AppAst
  syn Expr =
  | TmLam {ident : Name,
           body : Expr,
           ty : Type,
           info : Info}

  sem info =
  | TmLam r -> r.info

  sem ty =
  | TmLam t -> t.ty

  sem withType (ty : Type) =
  | TmLam t -> TmLam {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLam t -> TmLam {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLam t -> f acc t.body
end


-- TmLet --
lang LetAst = VarAst
  syn Expr =
  | TmLet {ident : Name,
           tyBody : Type,
           body : Expr,
           inexpr : Expr,
           ty : Type,
           info : Info}

  sem info =
  | TmLet r -> r.info

  sem ty =
  | TmLet t -> t.ty

  sem withType (ty : Type) =
  | TmLet t -> TmLet {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLet t -> TmLet {{t with body = f t.body} with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLet t -> f (f acc t.body) t.inexpr
end


-- TmRecLets --
lang RecLetsAst = VarAst
  syn Expr =
  | TmRecLets {bindings : [{ident : Name,
                            ty : Type,
                            body : Expr,
                            info : Info}],
               inexpr : Expr,
               ty : Type,
               info : Info}

  sem info =
  | TmRecLets r -> r.info

  sem ty =
  | TmRecLets t -> t.ty

  sem withType (ty : Type) =
  | TmRecLets t -> TmRecLets {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecLets t ->
    TmRecLets {{t with bindings = map (lam b. {b with body = f b.body})
                                      t.bindings}
                  with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecLets t -> f (foldl f acc (map (lam b. b.body) t.bindings)) t.inexpr
end


-- TmConst --
lang ConstAst
  syn Const =

  syn Expr =
  | TmConst {val : Const,
             ty: Type,
             info: Info}

  sem info =
  | TmConst r -> r.info

  sem ty =
  | TmConst t -> t.ty

  sem withType (ty : Type) =
  | TmConst t -> TmConst {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConst t -> TmConst t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConst t -> acc
end

-- TmSeq --
lang SeqAst
  syn Expr =
  | TmSeq {tms : [Expr],
           ty: Type,
           info: Info}

  sem info =
  | TmSeq r -> r.info

  sem ty =
  | TmSeq t -> t.ty

  sem withType (ty : Type) =
  | TmSeq t -> TmSeq {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmSeq t -> TmSeq {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmSeq t -> foldl f acc t.tms
end


-- TmRecord and TmRecorsUpdate -- 
lang RecordAst
  syn Expr =
  | TmRecord {bindings : AssocMap String Expr,
              ty : Type, 
              info : Info}
  | TmRecordUpdate {rec : Expr,
                    key : String,
                    value : Expr,
                    ty : Type,
                    info : Info}

  sem info =
  | TmRecord r -> r.info
  | TmRecordUpdate r -> r.info

  sem ty =
  | TmRecord t -> t.ty
  | TmRecordUpdate t -> t.ty

  sem withType (ty : Type) =
  | TmRecord t -> TmRecord {t with ty = ty}
  | TmRecordUpdate t -> TmRecordUpdate {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecord t -> TmRecord {t with bindings = assocMap {eq=eqString} f t.bindings}
  | TmRecordUpdate t -> TmRecordUpdate {{t with rec = f t.rec}
                                           with value = f t.value}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecord t -> assocFold {eq=eqString} (lam acc. lam _k. lam v. f acc v) acc t.bindings
  | TmRecordUpdate t -> f (f acc t.rec) t.value
end

-- TmType -- 
lang TypeAst
  syn Expr =
  | TmType {ident : Name,
            ty : Type,
            inexpr : Expr,
            info : Info}

  sem info =
  | TmType r -> r.info

  sem ty =
  | TmType t -> t.ty

  sem withType (ty : Type) =
  | TmType t -> TmType {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmType t -> TmType {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmType t -> f acc t.inexpr
end

-- TmCondef and TmConApp --
lang DataAst
  syn Expr =
  | TmConDef {ident : Name,
              ty : Type,
              inexpr : Expr,
              info : Info}
  | TmConApp {ident : Name,
              body : Expr,
              ty : Type,
              info: Info}

  sem info =
  | TmConDef r -> r.info
  | TmConApp r -> r.info

  sem ty =
  | TmConDef t -> t.ty
  | TmConApp t -> t.ty

  sem withType (ty : Type) =
  | TmConDef t -> TmConDef {t with ty = ty}
  | TmConApp t -> TmConApp {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConDef t -> TmConDef {t with inexpr = f t.inexpr}
  | TmConApp t -> TmConApp {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConDef t -> f acc t.inexpr
  | TmConApp t -> f acc t.body
end

-- TmMatch --
lang MatchAst
  syn Expr =
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr,
             ty     : Type,
             info     : Info}

  syn Pat =

  sem info =
  | TmMatch r -> r.info

  sem ty =
  | TmMatch t -> t.ty

  sem withType (ty : Type) =
  | TmMatch t -> TmMatch {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmMatch t -> TmMatch {{{t with target = f t.target}
                              with thn = f t.thn}
                              with els = f t.els}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmMatch t -> f (f (f acc t.target) t.thn) t.els
end


-- TmUtest --
lang UtestAst
  syn Expr =
  | TmUtest {test : Expr,
             expected : Expr,
             next : Expr,   
             ty : Type,
             info : Info} 

  sem info =
  | TmUtest r -> r.info

  sem ty =
  | TmUtest t -> t.ty

  sem withType (ty : Type) =
  | TmUtest t -> TmUtest {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmUtest t -> TmUtest {{{t with test = f t.test}
                              with expected = f t.expected}
                              with next = f t.next}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmUtest t -> f (f (f acc t.test) t.expected) t.next
end


-- TmNever --
lang NeverAst
  syn Expr =
  | TmNever {ty: Type,
            info: Info}

  sem info =
  | TmNever r -> r.info

  sem ty =
  | TmNever t -> t.ty

  sem withType (ty : Type) =
  | TmNever t -> TmNever {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmNever _ & t -> t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmNever _ & t -> acc
end


-- TmRef --
-- TODO (dbro, 2020-02-16): this term should be moved into an evaluation term
-- in the same way as for closures. Eventually, this should be a rank 0 tensor.
lang RefAst
  syn Expr =
  | TmRef {ref : Ref}

  sem info =
  | TmRef r -> NoInfo ()

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRef t -> TmRef t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRef t -> acc
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
  | CDivi {}
  | CNegi {}
  | CModi {}
end

lang ShiftIntAst = ConstAst + IntAst
  syn Const =
  | CSlli {}
  | CSrli {}
  | CSrai {}
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

lang FloatIntConversionAst = IntAst + FloatAst
  syn Const =
  | CFloorfi {}
  | CCeilfi {}
  | CRoundfi {}
  | CInt2float {}
end

lang BoolAst = ConstAst
  syn Const =
  | CBool {val : Bool}
end

lang CmpIntAst = IntAst + BoolAst
  syn Const =
  | CEqi {}
  | CNeqi {}
  | CLti {}
  | CGti {}
  | CLeqi {}
  | CGeqi {}
end

lang CmpFloatAst = FloatAst + BoolAst
  syn Const =
  | CEqf {}
  | CLtf {}
  | CLeqf {}
  | CGtf {}
  | CGeqf {}
  | CNeqf {}
end

lang CharAst = ConstAst
  syn Const =
  | CChar {val : Char}
end

lang CmpCharAst = CharAst + BoolAst
  syn Const =
  | CEqc {}
end

lang IntCharConversionAst = IntAst + CharAst
  syn Const =
  | CInt2Char {}
  | CChar2Int {}
end

lang FloatStringConversionAst = SeqAst + FloatAst
  syn Const =
  | CString2float {}
end

lang SymbAst = ConstAst
  syn Const =
  | CSymb {val : Symb}
  | CGensym {}
  | CSym2hash {}
end

lang CmpSymbAst = SymbAst + BoolAst
  syn Const =
  | CEqsym {}
end

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

lang FileOpAst = ConstAst
  syn Const =
  | CFileRead {}
  | CFileWrite {}
  | CFileExists {}
  | CFileDelete {}
end

lang IOAst = ConstAst
  syn Const =
  | CPrintString {}
  | CReadLine {}
  | CReadBytesAsString {}
end

lang RandomNumberGeneratorAst = ConstAst
  syn Const =
  | CRandIntU {}
  | CRandSetSeed {}
end

lang SysAst = ConstAst
  syn Const =
  | CExit {}
  | CError {}
  | CArgv {}
end

lang TimeAst = ConstAst
  syn Const =
  | CWallTimeMs {}
  | CSleepMs {}
end

lang RefOpAst = ConstAst + RefAst
  syn Const =
  | CRef {}
  | CModRef {}
  | CDeRef {}
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

lang RecordTypeAst
  syn Type =
  | TyRecord {fields : AssocMap String Type}
end

lang VariantTypeAst
  syn Type =
  | TyVariant {constrs : [Name]}
end

lang VarTypeAst
  syn Type =
  | TyVar {ident : Name}
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
  VarAst + AppAst + LamAst + RecordAst + LetAst + TypeAst + RecLetsAst +
  ConstAst + DataAst + MatchAst + UtestAst + SeqAst + NeverAst + RefAst +

  -- Constants
  IntAst + ArithIntAst + ShiftIntAst + FloatAst + ArithFloatAst + BoolAst +
  CmpIntAst + IntCharConversionAst + CmpFloatAst + CharAst + CmpCharAst +
  SymbAst + CmpSymbAst + SeqOpAst + FileOpAst + IOAst +
  RandomNumberGeneratorAst + SysAst + FloatIntConversionAst +
  FloatStringConversionAst + TimeAst + RefOpAst +

  -- Patterns
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat +

  -- Types
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + RecordTypeAst + VariantTypeAst + VarTypeAst +
  AppTypeAst
