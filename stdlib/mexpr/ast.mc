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


-- TmApp --
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
           tyIdent : Type,
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


-- TmRecord and TmRecordUpdate --
lang RecordAst
  syn Expr =
  | TmRecord {bindings : Map SID Expr,
              ty : Type,
              info : Info}
  | TmRecordUpdate {rec : Expr,
                    key : SID,
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
  | TmRecord t -> TmRecord {t with bindings = mapMap f t.bindings}
  | TmRecordUpdate t -> TmRecordUpdate {{t with rec = f t.rec}
                                           with value = f t.value}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecord t -> mapFoldWithKey (lam acc. lam _k. lam v. f acc v) acc t.bindings
  | TmRecordUpdate t -> f (f acc t.rec) t.value
end

-- TmType --
lang TypeAst
  syn Expr =
  | TmType {ident : Name,
            tyIdent : Type,
            inexpr : Expr,
            ty : Type,
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

-- TmConDef and TmConApp --
lang DataAst
  syn Expr =
  | TmConDef {ident : Name,
              tyIdent : Type,
              inexpr : Expr,
              ty : Type,
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
  | CCreate {}
  | CSplitAt {}
  | CSubsequence {}
end

lang FileOpAst = ConstAst
  syn Const =
  | CFileRead {}
  | CFileWrite {}
  | CFileExists {}
  | CFileDelete {}
end

lang TensorOpAst
  syn Const =
  | CTensorCreate {}
  | CTensorGetExn {}
  | CTensorSetExn {}
  | CTensorRank {}
  | CTensorShape {}
  | CTensorReshapeExn {}
  | CTensorCopyExn {}
  | CTensorSliceExn {}
  | CTensorSubExn {}
  | CTensorIteri {}
end

lang IOAst = ConstAst
  syn Const =
  | CPrint {}
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

lang MapAst = ConstAst
  syn Const =
  | CMapEmpty {}
  | CMapInsert {}
  | CMapRemove {}
  | CMapFindWithExn {}
  | CMapFindOrElse {}
  | CMapFindApplyOrElse {}
  | CMapBindings {}
  | CMapSize {}
  | CMapMem {}
  | CMapAny {}
  | CMapMap {}
  | CMapMapWithKey {}
  | CMapFoldWithKey {}
  | CMapEq {}
  | CMapCmp {}
  | CMapGetCmpFun {}
end

lang TensorAst = ConstAst
  syn Const =
  | CTensorCreate {}
  | CTensorGetExn {}
  | CTensorSetExn {}
  | CTensorRank {}
  | CTensorShape {}
  | CTensorReshapeExn {}
  | CTensorCopyExn {}
  | CTensorSliceExn {}
  | CTensorSubExn {}
  | CTensorIteri {}
end

lang BootParserAst = ConstAst
  syn Const =
  | CBootParserParseMExprString {}
  | CBootParserParseMCoreFile {}
  | CBootParserGetId {}
  | CBootParserGetTerm {}
  | CBootParserGetType ()
  | CBootParserGetString {}
  | CBootParserGetInt {}
  | CBootParserGetFloat {}
  | CBootParserGetListLength {}
  | CBootParserGetConst {}
  | CBootParserGetPat {}
  | CBootParserGetInfo {}
end

--------------
-- PATTERNS --
--------------

type PatName
con PName : Name -> PatName
con PWildcard : () -> PatName

lang NamedPat
  syn Pat =
  | PatNamed {ident : PatName,
              info : Info}

  sem info =
  | PatNamed r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatNamed p -> PatNamed p

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatNamed _ -> acc
end

lang SeqTotPat
  syn Pat =
  | PatSeqTot {pats : [Pat],
               info : Info}

  sem info =
  | PatSeqTot r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatSeqTot p -> PatSeqTot {p with pats = map f p.pats}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatSeqTot {pats = pats} -> foldl f acc pats
end

lang SeqEdgePat
  syn Pat =
  | PatSeqEdge {prefix : [Pat],
                middle: PatName,
                postfix : [Pat],
                info: Info}

  sem info =
  | PatSeqEdge r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatSeqEdge p ->
      PatSeqEdge {{p with prefix = map f p.prefix} with postfix = map f p.postfix}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatSeqEdge {prefix = pre, postfix = post} -> foldl f (foldl f acc pre) post
end

lang RecordPat
  syn Pat =
  | PatRecord {bindings : Map SID Pat,
               info: Info}

  sem info =
  | PatRecord r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatRecord b ->
      PatRecord {b with bindings = mapMap f b.bindings}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatRecord {bindings = bindings} ->
      mapFoldWithKey (lam acc. lam _k. lam v. f acc v) acc bindings
end

lang DataPat = DataAst
  syn Pat =
  | PatCon {ident : Name,
            subpat : Pat,
            info : Info}

  sem info =
  | PatCon r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatCon c -> PatCon {c with subpat = f c.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatCon {subpat = subpat} -> f acc subpat
end

lang IntPat = IntAst
  syn Pat =
  | PatInt {val : Int,
          info : Info}

  sem info =
  | PatInt r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatInt v -> PatInt v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatInt _ -> acc
end

lang CharPat
  syn Pat =
  | PatChar {val : Char,
             info : Info}

  sem info =
  | PatChar r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatChar v -> PatChar v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatChar _ -> acc
end

lang BoolPat = BoolAst
  syn Pat =
  | PatBool {val : Bool,
             info : Info}

  sem info =
  | PatBool r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatBool v -> PatBool v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatBool _ -> acc
end

lang AndPat
  syn Pat =
  | PatAnd {lpat : Pat,
            rpat : Pat,
            info : Info}

  sem info =
  | PatAnd r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatAnd p -> PatAnd {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatAnd {lpat = l, rpat = r} -> f (f acc l) r
end

lang OrPat
  syn Pat =
  | PatOr {lpat : Pat,
           rpat : Pat,
           info : Info}

  sem info =
  | PatOr r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatOr p -> PatOr {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatOr {lpat = l, rpat = r} -> f (f acc l) r
end

lang NotPat
  syn Pat =
  | PatNot {subpat : Pat,
            info : Info}

  sem info =
  | PatNot r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatNot p -> PatNot {p with subpat = f p.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatNot {subpat = p} -> f acc p
end

-----------
-- TYPES --
-----------

lang UnknownTypeAst
  syn Type =
  | TyUnknown {info : Info}

  sem info =
  | TyUnknown r -> r.info
end

lang BoolTypeAst
  syn Type =
  | TyBool {info  : Info}

  sem info =
  | TyBool r -> r.info
end

lang IntTypeAst
  syn Type =
  | TyInt {info : Info}

  sem info =
  | TyInt r -> r.info
end

lang FloatTypeAst
  syn Type =
  | TyFloat {info : Info}

  sem info =
  | TyFloat r -> r.info
end

lang CharTypeAst
  syn Type =
  | TyChar {info  : Info}

  sem info =
  | TyChar r -> r.info
end

lang FunTypeAst
  syn Type =
  | TyArrow {info : Info,
             from : Type,
             to   : Type}
  sem info =
  | TyArrow r -> r.info
end

lang SeqTypeAst
  syn Type =
  | TySeq {info : Info,
           ty   : Type}
  sem info =
  | TySeq r -> r.info
end

lang RecordTypeAst
  syn Type =
  | TyRecord {info    : Info,
              fields  : Map SID Type}
  sem info =
  | TyRecord r -> r.info
end

lang VariantTypeAst
  syn Type =
  | TyVariant {info     : Info,
               constrs  : Map Name Type}
  sem info =
  | TyVariant r -> r.info
end

lang VarTypeAst
  syn Type =
  | TyVar {info   : Info,
           ident  : Name}
  sem info =
  | TyVar r -> r.info
end

lang AppTypeAst
  syn Type =
  | TyApp {info : Info,
           lhs  : Type,
           rhs  : Type}
  sem info =
  | TyApp r -> r.info
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
  FloatStringConversionAst + TimeAst + RefOpAst + MapAst + TensorAst +
  TensorOpAst + BootParserAst +

  -- Patterns
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat +

  -- Types
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + RecordTypeAst + VariantTypeAst + VarTypeAst +
  AppTypeAst
