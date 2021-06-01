-- Language fragments of MExpr

include "info.mc"
include "assoc.mc"
include "info.mc"
include "name.mc"
include "string.mc"

-----------
-- TERMS --
-----------

-- Shared fragment
lang Ast

  syn Expr =
  -- Intentionally left blank

  syn Type =
  -- Intentionally left blank

end

-- TmVar --
lang VarAst = Ast
  syn Expr =
  | TmVar {ident : Name,
           ty: Type,
           info: Info}

  sem infoTm =
  | TmVar r -> r.info

  sem ty =
  | TmVar t -> t.ty

  sem withInfo (info : Info) =
  | TmVar t -> TmVar {t with info = info}

  sem withType (ty : Type) =
  | TmVar t -> TmVar {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmVar t -> TmVar t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmVar t -> acc
end


-- TmApp --
lang AppAst = Ast
  syn Expr =
  | TmApp {lhs : Expr,
           rhs : Expr,
           ty: Type,
           info: Info}

  sem infoTm =
  | TmApp r -> r.info

  sem ty =
  | TmApp t -> t.ty

  sem withInfo (info : Info) =
  | TmApp t -> TmApp {t with info = info}

  sem withType (ty : Type) =
  | TmApp t -> TmApp {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmApp t -> TmApp {{t with lhs = f t.lhs}
                         with rhs = f t.rhs}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmApp t -> f (f acc t.lhs) t.rhs

end


-- TmLam --
lang LamAst = Ast + VarAst + AppAst
  syn Expr =
  | TmLam {ident : Name,
           tyIdent : Type,
           body : Expr,
           ty : Type,
           info : Info}

  sem infoTm =
  | TmLam r -> r.info

  sem ty =
  | TmLam t -> t.ty

  sem withInfo (info : Info) =
  | TmLam t -> TmLam {t with info = info}

  sem withType (ty : Type) =
  | TmLam t -> TmLam {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLam t -> TmLam {t with body = f t.body}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLam t -> f acc t.body
end


-- TmLet --
lang LetAst = Ast + VarAst
  syn Expr =
  | TmLet {ident : Name,
           tyBody : Type,
           body : Expr,
           inexpr : Expr,
           ty : Type,
           info : Info}

  sem infoTm =
  | TmLet r -> r.info

  sem ty =
  | TmLet t -> t.ty

  sem withInfo (info : Info) =
  | TmLet t -> TmLet {t with info = info}

  sem withType (ty : Type) =
  | TmLet t -> TmLet {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLet t -> TmLet {{t with body = f t.body} with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLet t -> f (f acc t.body) t.inexpr
end

type RecLetBinding =
  { ident : Name
  , tyBody : Type
  , body : Expr
  , ty : Type
  , info : Info }

-- TmRecLets --
lang RecLetsAst = Ast + VarAst
  syn Expr =
  | TmRecLets {bindings : [RecLetBinding],
               inexpr : Expr,
               ty : Type,
               info : Info}

  sem infoTm =
  | TmRecLets r -> r.info

  sem ty =
  | TmRecLets t -> t.ty

  sem withInfo (info : Info) =
  | TmRecLets t -> TmRecLets {t with info = info}

  sem withType (ty : Type) =
  | TmRecLets t -> TmRecLets {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmRecLets t ->
    let bindingMapFunc =
      lam b : RecLetBinding.
        {b with body = f b.body}
    in
    TmRecLets {{t with bindings = map bindingMapFunc t.bindings}
                  with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmRecLets t ->
    let bindingMapFunc =
      lam b : RecLetBinding.
        b.body
    in
    f (foldl f acc (map bindingMapFunc t.bindings)) t.inexpr
end


-- TmConst --
lang ConstAst = Ast
  syn Const =

  syn Expr =
  | TmConst {val : Const,
             ty: Type,
             info: Info}

  sem infoTm =
  | TmConst r -> r.info

  sem ty =
  | TmConst t -> t.ty

  sem withInfo (info : Info) =
  | TmConst t -> TmConst {t with info = info}

  sem withType (ty : Type) =
  | TmConst t -> TmConst {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmConst t -> TmConst t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmConst t -> acc
end

-- TmSeq --
lang SeqAst = Ast
  syn Expr =
  | TmSeq {tms : [Expr],
           ty: Type,
           info: Info}

  sem infoTm =
  | TmSeq r -> r.info

  sem ty =
  | TmSeq t -> t.ty

  sem withInfo (info : Info) =
  | TmSeq t -> TmSeq {t with info = info}

  sem withType (ty : Type) =
  | TmSeq t -> TmSeq {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmSeq t -> TmSeq {t with tms = map f t.tms}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmSeq t -> foldl f acc t.tms
end


-- TmRecord and TmRecordUpdate --
lang RecordAst = Ast
  syn Expr =
  | TmRecord {bindings : Map SID Expr,
              ty : Type,
              info : Info}
  | TmRecordUpdate {rec : Expr,
                    key : SID,
                    value : Expr,
                    ty : Type,
                    info : Info}

  sem infoTm =
  | TmRecord r -> r.info
  | TmRecordUpdate r -> r.info

  sem ty =
  | TmRecord t -> t.ty
  | TmRecordUpdate t -> t.ty

  sem withInfo (info : Info) =
  | TmRecord t -> TmRecord {t with info = info}
  | TmRecordUpdate t -> TmRecordUpdate {t with info = info}

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
lang TypeAst = Ast
  syn Expr =
  | TmType {ident : Name,
            tyIdent : Type,
            inexpr : Expr,
            ty : Type,
            info : Info}

  sem infoTm =
  | TmType r -> r.info

  sem ty =
  | TmType t -> t.ty

  sem withInfo (info : Info) =
  | TmType t -> TmType {t with info = info}

  sem withType (ty : Type) =
  | TmType t -> TmType {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmType t -> TmType {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmType t -> f acc t.inexpr
end

-- TmConDef and TmConApp --
lang DataAst = Ast
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

  sem infoTm =
  | TmConDef r -> r.info
  | TmConApp r -> r.info

  sem ty =
  | TmConDef t -> t.ty
  | TmConApp t -> t.ty

  sem withInfo (info : Info) =
  | TmConDef t -> TmConDef {t with info = info}
  | TmConApp t -> TmConApp {t with info = info}

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
lang MatchAst = Ast
  syn Expr =
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr,
             ty     : Type,
             info     : Info}

  syn Pat =
  -- Intentionally left blank

  sem infoTm =
  | TmMatch r -> r.info

  sem ty =
  | TmMatch t -> t.ty

  sem withInfo (info : Info) =
  | TmMatch t -> TmMatch {t with info = info}

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
lang UtestAst = Ast
  syn Expr =
  | TmUtest {test : Expr,
             expected : Expr,
             next : Expr,
             tusing : Option Expr,
             ty : Type,
             info : Info}

  sem infoTm =
  | TmUtest r -> r.info

  sem ty =
  | TmUtest t -> t.ty

  sem withInfo (info : Info) =
  | TmUtest t -> TmUtest {t with info = info}

  sem withType (ty : Type) =
  | TmUtest t -> TmUtest {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmUtest t -> let tusing = optionMap f t.tusing in
                 TmUtest {{{{t with test = f t.test}
                              with expected = f t.expected}
                              with next = f t.next}
                              with tusing = tusing}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmUtest t ->
    let acc = f (f (f acc t.test) t.expected) t.next in
    optionMapOrElse (lam. acc) (f acc) t.tusing
end


-- TmNever --
lang NeverAst = Ast
  syn Expr =
  | TmNever {ty: Type,
            info: Info}

  sem infoTm =
  | TmNever r -> r.info

  sem ty =
  | TmNever t -> t.ty

  sem withInfo (info : Info) =
  | TmNever t -> TmNever {t with info = info}

  sem withType (ty : Type) =
  | TmNever t -> TmNever {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmNever _ & t -> t

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmNever _ & t -> acc
end

-- TmExt --
lang ExtAst = Ast + VarAst
  syn Expr =
  | TmExt {ident : Name,
           inexpr : Expr,
           effect : Bool,
           ty : Type,
           info : Info}

  sem infoTm =
  | TmExt r -> r.info

  sem ty =
  | TmExt t -> t.ty

  sem withInfo (info : Info) =
  | TmExt t -> TmExt {t with info = info}

  sem withType (ty : Type) =
  | TmExt t -> TmExt {t with ty = ty}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmExt t -> TmExt {t with inexpr = f t.inexpr}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmExt t -> f acc t.inexpr
end

---------------
-- CONSTANTS --
---------------

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
  | CFloat2string {}
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
  | CTail {}
  | CNull {}
  | CCreate {}
  | CCreateFingerTree {}
  | CCreateList {}
  | CCreateRope {}
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

lang IOAst = ConstAst
  syn Const =
  | CPrint {}
  | CDPrint {}
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
  | CCommand {}
end

lang TimeAst = ConstAst
  syn Const =
  | CWallTimeMs {}
  | CSleepMs {}
end

lang RefOpAst = ConstAst
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

lang TensorOpAst = ConstAst
  syn Const =
  | CTensorCreateInt {}
  | CTensorCreateFloat {}
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

lang NamedPat = MatchAst
  syn Pat =
  | PatNamed {ident : PatName,
              info : Info}

  sem infoPat =
  | PatNamed r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatNamed p -> PatNamed p

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatNamed _ -> acc
end

lang SeqTotPat = MatchAst
  syn Pat =
  | PatSeqTot {pats : [Pat],
               info : Info}

  sem infoPat =
  | PatSeqTot r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatSeqTot p -> PatSeqTot {p with pats = map f p.pats}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatSeqTot {pats = pats} -> foldl f acc pats
end

lang SeqEdgePat = MatchAst
  syn Pat =
  | PatSeqEdge {prefix : [Pat],
                middle: PatName,
                postfix : [Pat],
                info: Info}

  sem infoPat =
  | PatSeqEdge r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatSeqEdge p ->
      PatSeqEdge {{p with prefix = map f p.prefix} with postfix = map f p.postfix}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatSeqEdge {prefix = pre, postfix = post} -> foldl f (foldl f acc pre) post
end

lang RecordPat = MatchAst
  syn Pat =
  | PatRecord {bindings : Map SID Pat,
               info: Info}

  sem infoPat =
  | PatRecord r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatRecord b ->
      PatRecord {b with bindings = mapMap f b.bindings}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatRecord {bindings = bindings} ->
      mapFoldWithKey (lam acc. lam _k. lam v. f acc v) acc bindings
end

lang DataPat = MatchAst + DataAst
  syn Pat =
  | PatCon {ident : Name,
            subpat : Pat,
            info : Info}

  sem infoPat =
  | PatCon r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatCon c -> PatCon {c with subpat = f c.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatCon {subpat = subpat} -> f acc subpat
end

lang IntPat = MatchAst + IntAst
  syn Pat =
  | PatInt {val : Int,
          info : Info}

  sem infoPat =
  | PatInt r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatInt v -> PatInt v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatInt _ -> acc
end

lang CharPat = MatchAst
  syn Pat =
  | PatChar {val : Char,
             info : Info}

  sem infoPat =
  | PatChar r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatChar v -> PatChar v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatChar _ -> acc
end

lang BoolPat = MatchAst + BoolAst
  syn Pat =
  | PatBool {val : Bool,
             info : Info}

  sem infoPat =
  | PatBool r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatBool v -> PatBool v

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatBool _ -> acc
end

lang AndPat = MatchAst
  syn Pat =
  | PatAnd {lpat : Pat,
            rpat : Pat,
            info : Info}

  sem infoPat =
  | PatAnd r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatAnd p -> PatAnd {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatAnd {lpat = l, rpat = r} -> f (f acc l) r
end

lang OrPat = MatchAst
  syn Pat =
  | PatOr {lpat : Pat,
           rpat : Pat,
           info : Info}

  sem infoPat =
  | PatOr r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatOr p -> PatOr {{p with lpat = f p.lpat} with rpat = f p.rpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatOr {lpat = l, rpat = r} -> f (f acc l) r
end

lang NotPat = MatchAst
  syn Pat =
  | PatNot {subpat : Pat,
            info : Info}

  sem infoPat =
  | PatNot r -> r.info

  sem smap_Pat_Pat (f : Pat -> a) =
  | PatNot p -> PatNot {p with subpat = f p.subpat}

  sem sfold_Pat_Pat (f : a -> b -> a) (acc : a) =
  | PatNot {subpat = p} -> f acc p
end

-----------
-- TYPES --
-----------

lang UnknownTypeAst = Ast
  syn Type =
  | TyUnknown {info : Info}

  sem tyWithInfo (info : Info) =
  | TyUnknown t -> TyUnknown {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyUnknown t -> TyUnknown t

  sem infoTy =
  | TyUnknown r -> r.info
end

lang BoolTypeAst = Ast
  syn Type =
  | TyBool {info  : Info}

  sem tyWithInfo (info : Info) =
  | TyBool t -> TyBool {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyBool t -> TyBool t

  sem infoTy =
  | TyBool r -> r.info
end

lang IntTypeAst = Ast
  syn Type =
  | TyInt {info : Info}

  sem tyWithInfo (info : Info) =
  | TyInt t -> TyInt {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyInt t -> TyInt t

  sem infoTy =
  | TyInt r -> r.info
end

lang FloatTypeAst = Ast
  syn Type =
  | TyFloat {info : Info}

  sem tyWithInfo (info : Info) =
  | TyFloat t -> TyFloat {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyFloat t -> TyFloat t

  sem infoTy =
  | TyFloat r -> r.info
end

lang CharTypeAst = Ast
  syn Type =
  | TyChar {info  : Info}

  sem tyWithInfo (info : Info) =
  | TyChar t -> TyChar {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyChar t -> TyChar t

  sem infoTy =
  | TyChar r -> r.info
end

lang FunTypeAst = Ast
  syn Type =
  | TyArrow {info : Info,
             from : Type,
             to   : Type}

  sem tyWithInfo (info : Info) =
  | TyArrow t -> TyArrow {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyArrow t -> TyArrow {{t with from = f t.from} with to = f t.to}

  sem infoTy =
  | TyArrow r -> r.info
end

lang SeqTypeAst = Ast
  syn Type =
  | TySeq {info : Info,
           ty   : Type}

  sem tyWithInfo (info : Info) =
  | TySeq t -> TySeq {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TySeq t -> TySeq {t with ty = f t.ty}

  sem infoTy =
  | TySeq r -> r.info
end

lang TensorTypeAst = Ast
  syn Type =
  | TyTensor {info : Info,
              ty   : Type}

  sem tyWithInfo (info : Info) =
  | TyTensor t -> TyTensor {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyTensor t -> TyTensor {t with ty = f t.ty}

  sem infoTy =
  | TyTensor r -> r.info
end

lang RecordTypeAst = Ast
  syn Type =
  | TyRecord {info    : Info,
              fields  : Map SID Type,
              labels  : [SID]}

  sem tyWithInfo (info : Info) =
  | TyRecord t -> TyRecord {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyRecord t -> TyRecord {t with fields = mapMap f t.fields}

  sem infoTy =
  | TyRecord r -> r.info
end

lang VariantTypeAst = Ast
  syn Type =
  | TyVariant {info     : Info,
               constrs  : Map Name Type}

  sem tyWithInfo (info : Info) =
  | TyVariant t -> TyVariant {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyVariant t -> TyVariant {t with constrs = mapMap f t.constrs}

  sem infoTy =
  | TyVariant r -> r.info
end

lang VarTypeAst = Ast
  syn Type =
  | TyVar {info   : Info,
           ident  : Name}

  sem tyWithInfo (info : Info) =
  | TyVar t -> TyVar {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyVar t -> TyVar t

  sem infoTy =
  | TyVar r -> r.info
end

lang AppTypeAst = Ast
  syn Type =
  | TyApp {info : Info,
           lhs  : Type,
           rhs  : Type}

  sem tyWithInfo (info : Info) =
  | TyApp t -> TyApp {t with info = info}

  sem smap_Type_Type (f : Type -> a) =
  | TyApp t -> TyApp {{t with lhs = f t.lhs} with rhs = f t.rhs}

  sem infoTy =
  | TyApp r -> r.info
end

------------------------
-- MEXPR AST FRAGMENT --
------------------------

lang MExprAst =

  -- Terms
  VarAst + AppAst + LamAst + RecordAst + LetAst + TypeAst + RecLetsAst +
  ConstAst + DataAst + MatchAst + UtestAst + SeqAst + NeverAst + ExtAst +

  -- Constants
  IntAst + ArithIntAst + ShiftIntAst + FloatAst + ArithFloatAst + BoolAst +
  CmpIntAst + IntCharConversionAst + CmpFloatAst + CharAst + CmpCharAst +
  SymbAst + CmpSymbAst + SeqOpAst + FileOpAst + IOAst +
  RandomNumberGeneratorAst + SysAst + FloatIntConversionAst +
  FloatStringConversionAst + TimeAst + RefOpAst + MapAst + TensorOpAst +
  BootParserAst +

  -- Patterns
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat +

  -- Types
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + RecordTypeAst + VariantTypeAst + VarTypeAst +
  AppTypeAst + TensorTypeAst
