-- Language fragments of MExpr

include "info.mc"
include "assoc.mc"
include "info.mc"
include "name.mc"
include "string.mc"
include "map.mc"

-----------
-- TERMS --
-----------

-- Shared fragment
lang Ast

  syn Expr =
  -- Intentionally left blank

  syn Type =
  -- Intentionally left blank

  syn Pat =
  -- Intentionally left blank

  sem infoTm =
  -- Intentionally left blank

  sem ty =
  -- Intentionally left blank

  sem withType (ty : Type) =
  -- Intentionally left blank

  sem tyPat =
  -- Intentionally left blank

  sem withTypePat (ty : Type) =
  -- Intentionally left blank

  -- TODO(vipa, 2021-05-27): Replace smap and sfold with smapAccumL for Expr and Type as well
  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | p -> (acc, p)

  sem smap_Expr_Expr (f : a -> b) =
  | p ->
    let res: ((), Expr) = smapAccumL_Expr_Expr (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Expr_Expr (f : acc -> a -> acc) (acc : acc) =
  | p ->
    let res: (acc, Expr) = smapAccumL_Expr_Expr (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  -- NOTE(vipa, 2021-05-28): This function *does not* touch the `ty`
  -- field. It only covers nodes in the AST, so to speak, not
  -- annotations thereof.
  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | p -> (acc, p)

  sem smap_Expr_Type (f : a -> b) =
  | p ->
    let res: ((), Expr) = smapAccumL_Expr_Type (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Expr_Type (f : acc -> a -> acc) (acc : acc) =
  | p ->
    let res: (acc, Expr) = smapAccumL_Expr_Type (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | p -> (acc, p)

  sem smap_Type_Type (f : a -> b) =
  | p ->
    let res: ((), Type) = smapAccumL_Type_Type (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Type_Type (f : acc -> a -> acc) (acc : acc) =
  | p ->
    let res: (acc, Type) = smapAccumL_Type_Type (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | p -> (acc, p)

  sem smap_Pat_Pat (f : a -> b) =
  | p ->
    let res: ((), Pat) = smapAccumL_Pat_Pat (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Pat_Pat (f : acc -> a -> acc) (acc : acc) =
  | p ->
    let res: (acc, Pat) = smapAccumL_Pat_Pat (lam acc. lam a. (f acc a, a)) acc p in
    res.0
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmApp t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, TmApp {{t with lhs = lhs} with rhs = rhs})
      else never
    else never
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

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmLam t ->
    match f acc t.tyIdent with (acc, tyIdent) then
      (acc, TmLam {t with tyIdent = tyIdent})
    else never

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmLam t ->
    match f acc t.body with (acc, body) then
      (acc, TmLam {t with body = body})
    else never
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

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmLet t ->
    match f acc t.tyBody with (acc, tyBody) then
      (acc, TmLet {t with tyBody = tyBody})
    else never

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmLet t ->
    match f acc t.body with (acc, body) then
      match f acc t.inexpr with (acc, inexpr) then
        (acc, TmLet {{t with body = body} with inexpr = inexpr})
      else never
    else never
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmRecLets t ->
    let bindingFunc = lam acc. lam b: RecLetBinding.
      match f acc b.body with (acc, body) then
        (acc, {b with body = body})
      else never in
    match mapAccumL bindingFunc acc t.bindings with (acc, bindings) then
      match f acc t.inexpr with (acc, inexpr) then
        (acc, TmRecLets {{t with bindings = bindings} with inexpr = inexpr})
      else never
    else never
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmSeq t ->
    match mapAccumL f acc t.tms with (acc, tms) then
      (acc, TmSeq {t with tms = tms})
    else never
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings with (acc, bindings) then
      (acc, TmRecord {t with bindings = bindings})
    else never
  | TmRecordUpdate t ->
    match f acc t.rec with (acc, rec) then
      match f acc t.value with (acc, value) then
        (acc, TmRecordUpdate {{t with rec = rec} with value = value})
      else never
    else never
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

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmType t ->
    match f acc t.tyIdent with (acc, tyIdent) then
      (acc, TmType {t with tyIdent = tyIdent})
    else never

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmType t ->
    match f acc t.inexpr with (acc, inexpr) then
      (acc, TmType {t with inexpr = inexpr})
    else never
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

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmConDef t ->
    match f acc t.tyIdent with (acc, tyIdent) then
      (acc, TmConDef {t with tyIdent = tyIdent})
    else never

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmConDef t ->
    match f acc t.inexpr with (acc, inexpr) then
      (acc, TmConDef {t with inexpr = inexpr})
    else never
  | TmConApp t ->
    match f acc t.body with (acc, body) then
      (acc, TmConApp {t with body = body})
    else never
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmMatch t ->
    match f acc t.target with (acc, target) then
      match f acc t.thn with (acc, thn) then
        match f acc t.els with (acc, els) then
          (acc, TmMatch {{{t with target = target} with thn = thn} with els = els})
        else never
      else never
    else never
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

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmUtest t ->
    match f acc t.test with (acc, test) then
      match f acc t.expected with (acc, expected) then
        match f acc t.next with (acc, next) then
          match optionMapAccum f acc t.tusing with (acc, tusing) then
            ( acc
            , TmUtest
              {{{{t with test = test}
                    with expected = expected}
                    with next = next}
                    with tusing = tusing}
            )
          else never
        else never
      else never
    else never
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
end

-- TmExt --
lang ExtAst = Ast + VarAst
  syn Expr =
  | TmExt {ident : Name,
           tyIdent : Type,
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

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmExt t ->
    match f acc t.tyIdent with (acc, tyIdent) then
      (acc, TmExt {t with tyIdent = tyIdent})
    else never

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmExt t ->
    match f acc t.inexpr with (acc, inexpr) then
      (acc, TmExt {t with inexpr = inexpr})
    else never
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
  | CHead {}
  | CTail {}
  | CNull {}
  | CMap {}
  | CMapi {}
  | CIter {}
  | CIteri {}
  | CFoldl {}
  | CFoldr {}
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
  | CFlushStdout {}
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
  | CTensorTransposeExn {}
  | CTensorSliceExn {}
  | CTensorSubExn {}
  | CTensorIterSlice {}
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
              info : Info,
              ty : Type}

  sem infoPat =
  | PatNamed r -> r.info

  sem tyPat =
  | PatNamed r -> r.ty

  sem withTypePat (ty : Type) =
  | PatNamed r -> PatNamed {r with ty = ty}
end

lang SeqTotPat = MatchAst
  syn Pat =
  | PatSeqTot {pats : [Pat],
               info : Info,
               ty : Type}

  sem infoPat =
  | PatSeqTot r -> r.info

  sem tyPat =
  | PatSeqTot r -> r.ty

  sem withTypePat (ty : Type) =
  | PatSeqTot r -> PatSeqTot {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatSeqTot r ->
    match mapAccumL f acc r.pats with (acc, pats) then
      (acc, PatSeqTot {r with pats = pats})
    else never
end

lang SeqEdgePat = MatchAst
  syn Pat =
  | PatSeqEdge {prefix : [Pat],
                middle: PatName,
                postfix : [Pat],
                info: Info,
                ty: Type}

  sem infoPat =
  | PatSeqEdge r -> r.info

  sem tyPat =
  | PatSeqEdge r -> r.ty

  sem withTypePat (ty : Type) =
  | PatSeqEdge r -> PatSeqEdge {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatSeqEdge p ->
    match mapAccumL f acc p.prefix with (acc, prefix) then
      match mapAccumL f acc p.postfix with (acc, postfix) then
        (acc, PatSeqEdge {{p with prefix = prefix} with postfix = postfix})
      else never
    else never
end

lang RecordPat = MatchAst
  syn Pat =
  | PatRecord {bindings : Map SID Pat,
               info: Info,
               ty: Type}

  sem infoPat =
  | PatRecord r -> r.info

  sem tyPat =
  | PatRecord r -> r.ty

  sem withTypePat (ty : Type) =
  | PatRecord r -> PatRecord {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatRecord p ->
    match mapMapAccum (lam acc. lam. lam p. f acc p) acc p.bindings with (acc, bindings) then
      (acc, PatRecord {p with bindings = bindings})
    else never
end

lang DataPat = MatchAst + DataAst
  syn Pat =
  | PatCon {ident : Name,
            subpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat =
  | PatCon r -> r.info

  sem tyPat =
  | PatCon r -> r.ty

  sem withTypePat (ty : Type) =
  | PatCon r -> PatCon {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatCon c ->
    match f acc c.subpat with (acc, subpat) then
      (acc, PatCon {c with subpat = subpat})
    else never
end

lang IntPat = MatchAst + IntAst
  syn Pat =
  | PatInt {val : Int,
            info : Info,
            ty : Type}

  sem infoPat =
  | PatInt r -> r.info

  sem tyPat =
  | PatInt r -> r.ty

  sem withTypePat (ty : Type) =
  | PatInt r -> PatInt {r with ty = ty}
end

lang CharPat = MatchAst
  syn Pat =
  | PatChar {val : Char,
             info : Info,
             ty : Type}

  sem infoPat =
  | PatChar r -> r.info

  sem tyPat =
  | PatChar r -> r.ty

  sem withTypePat (ty : Type) =
  | PatChar r -> PatChar {r with ty = ty}
end

lang BoolPat = MatchAst + BoolAst
  syn Pat =
  | PatBool {val : Bool,
             info : Info,
             ty : Type}

  sem infoPat =
  | PatBool r -> r.info

  sem tyPat =
  | PatBool r -> r.ty

  sem withTypePat (ty : Type) =
  | PatBool r -> PatBool {r with ty = ty}
end

lang AndPat = MatchAst
  syn Pat =
  | PatAnd {lpat : Pat,
            rpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat =
  | PatAnd r -> r.info

  sem tyPat =
  | PatAnd r -> r.ty

  sem withTypePat (ty : Type) =
  | PatAnd r -> PatAnd {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatAnd p ->
    match f acc p.lpat with (acc, lpat) then
      match f acc p.rpat with (acc, rpat) then
        (acc, PatAnd {{p with lpat = lpat} with rpat = rpat})
      else never
    else never
end

lang OrPat = MatchAst
  syn Pat =
  | PatOr {lpat : Pat,
           rpat : Pat,
           info : Info,
           ty : Type}

  sem infoPat =
  | PatOr r -> r.info

  sem tyPat =
  | PatOr r -> r.ty

  sem withTypePat (ty : Type) =
  | PatOr r -> PatOr {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatOr p ->
    match f acc p.lpat with (acc, lpat) then
      match f acc p.rpat with (acc, rpat) then
        (acc, PatOr {{p with lpat = lpat} with rpat = rpat})
      else never
    else never
end

lang NotPat = MatchAst
  syn Pat =
  | PatNot {subpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat =
  | PatNot r -> r.info

  sem tyPat =
  | PatNot r -> r.ty

  sem withTypePat (ty : Type) =
  | PatNot r -> PatNot {r with ty = ty}

  sem smapAccumL_Pat_Pat (f : acc -> a -> (acc, b)) (acc : acc) =
  | PatNot p ->
    match f acc p.subpat with (acc, subpat) then
      (acc, PatNot {p with subpat = subpat})
    else never
end

-----------
-- TYPES --
-----------

lang UnknownTypeAst = Ast
  syn Type =
  | TyUnknown {info : Info}

  sem tyWithInfo (info : Info) =
  | TyUnknown t -> TyUnknown {t with info = info}

  sem infoTy =
  | TyUnknown r -> r.info
end

lang BoolTypeAst = Ast
  syn Type =
  | TyBool {info  : Info}

  sem tyWithInfo (info : Info) =
  | TyBool t -> TyBool {t with info = info}

  sem infoTy =
  | TyBool r -> r.info
end

lang IntTypeAst = Ast
  syn Type =
  | TyInt {info : Info}

  sem tyWithInfo (info : Info) =
  | TyInt t -> TyInt {t with info = info}

  sem infoTy =
  | TyInt r -> r.info
end

lang FloatTypeAst = Ast
  syn Type =
  | TyFloat {info : Info}

  sem tyWithInfo (info : Info) =
  | TyFloat t -> TyFloat {t with info = info}

  sem infoTy =
  | TyFloat r -> r.info
end

lang CharTypeAst = Ast
  syn Type =
  | TyChar {info  : Info}

  sem tyWithInfo (info : Info) =
  | TyChar t -> TyChar {t with info = info}

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

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TyArrow t ->
    match f acc t.from with (acc, from) then
      match f acc t.to with (acc, to) then
        (acc, TyArrow {{t with from = from} with to = to})
      else never
    else never

  sem infoTy =
  | TyArrow r -> r.info
end

lang SeqTypeAst = Ast
  syn Type =
  | TySeq {info : Info,
           ty   : Type}

  sem tyWithInfo (info : Info) =
  | TySeq t -> TySeq {t with info = info}

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TySeq t ->
    match f acc t.ty with (acc, ty) then
      (acc, TySeq {t with ty = ty})
    else never

  sem infoTy =
  | TySeq r -> r.info
end

lang TensorTypeAst = Ast
  syn Type =
  | TyTensor {info : Info,
              ty   : Type}

  sem tyWithInfo (info : Info) =
  | TyTensor t -> TyTensor {t with info = info}

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TyTensor t ->
    match f acc t.ty with (acc, ty) then
      (acc, TyTensor {t with ty = ty})
    else never

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

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TyRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.fields with (acc, fields) then
      (acc, TyRecord {t with fields = fields})
    else never

  sem infoTy =
  | TyRecord r -> r.info
end

lang VariantTypeAst = Ast
  syn Type =
  | TyVariant {info     : Info,
               constrs  : Map Name Type}

  sem tyWithInfo (info : Info) =
  | TyVariant t -> TyVariant {t with info = info}

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TyVariant t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.constrs with (acc, constrs) then
      (acc, TyVariant {t with constrs = constrs})
    else never

  sem infoTy =
  | TyVariant r -> r.info
end

lang VarTypeAst = Ast
  syn Type =
  | TyVar {info   : Info,
           ident  : Name}

  sem tyWithInfo (info : Info) =
  | TyVar t -> TyVar {t with info = info}

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

  sem smapAccumL_Type_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TyApp t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, TyApp {{t with lhs = lhs} with rhs = rhs})
      else never
    else never

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
