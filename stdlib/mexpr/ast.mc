-- Language fragments of MExpr

include "assoc.mc"
include "info.mc"
include "map.mc"
include "name.mc"
include "string.mc"
include "stringid.mc"
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

---------------
-- CONSTANTS --
---------------

let tyint_ = use IntTypeAst in
  TyInt {info = NoInfo ()}

let tyfloat_ = use FloatTypeAst in
  TyFloat {info = NoInfo ()}

let tybool_ = use BoolTypeAst in
  TyBool {info = NoInfo ()}

let tychar_ = use CharTypeAst in
  TyChar {info = NoInfo ()}

let tyunknown_ = use UnknownTypeAst in
  TyUnknown {info = NoInfo ()}

let tyseq_ = use SeqTypeAst in
  lam ty.
  TySeq {ty = ty, info = NoInfo ()}

let tystr_ = tyseq_ tychar_

let tyarrow_ = use FunTypeAst in
  lam from. lam to.
  TyArrow {from = from, to = to, info = NoInfo ()}

let tyarrows_ = use FunTypeAst in
  lam tys.
  foldr1 (lam e. lam acc. TyArrow {from = e, to = acc, info = NoInfo ()}) tys

let tyrecord_ = use RecordTypeAst in
  lam fields.
  TyRecord {
    fields = mapFromList cmpSID (map (lam b. (stringToSid b.0, b.1)) fields),
    info = NoInfo ()
  }

let tytuple_ = lam tys.
  tyrecord_ (mapi (lam i. lam ty. (int2string i, ty)) tys)

let tyunit_ = tyrecord_ []

let tyvariant_ = use VariantTypeAst in
  lam constrs.
  TyVariant {
    constrs = mapFromList nameCmp constrs,
    info = NoInfo ()
  }

let tyapp_ = use AppTypeAst in
  lam lhs. lam rhs.
  TyApp {lhs = lhs, rhs = rhs, info = NoInfo ()}

let ntyvar_ = use VarTypeAst in
  lam n.
  TyVar {ident = n, info = NoInfo ()}

let tyvar_ = lam s.
  ntyvar_ (nameNoSym s)

-- The types defined below are used for documentation purposes.
let tysym_ = tyunknown_
let tyref_ = tyunknown_
let tymap_ = tyunknown_
let tytensor_ = lam ty. tyunknown_
let tybootparsetree_ = tyunknown_
let tygeneric_ = lam id. tyunknown_
let tygenericseq_ = lam id. tyseq_ (tygeneric_ id)
let tygenerictensor_ = lam id. tytensor_ (tygeneric_ id)

lang IntAst = ConstAst
  syn Const =
  | CInt {val : Int}

  sem tyConst =
  | CInt _ -> tyint_
end

lang ArithIntAst = ConstAst + IntAst
  syn Const =
  | CAddi {}
  | CSubi {}
  | CMuli {}
  | CDivi {}
  | CNegi {}
  | CModi {}

  sem tyConst =
  | CAddi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSubi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CMuli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CDivi _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CNegi _ -> tyarrow_ tyint_ tyint_
  | CModi _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang ShiftIntAst = ConstAst + IntAst
  syn Const =
  | CSlli {}
  | CSrli {}
  | CSrai {}

  sem tyConst =
  | CSlli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrli _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CSrai _ -> tyarrows_ [tyint_, tyint_, tyint_]
end

lang FloatAst = ConstAst
  syn Const =
  | CFloat {val : Float}

  sem tyConst =
  | CFloat _ -> tyfloat_
end

lang ArithFloatAst = ConstAst + FloatAst
  syn Const =
  | CAddf {}
  | CSubf {}
  | CMulf {}
  | CDivf {}
  | CNegf {}

  sem tyConst =
  | CAddf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CSubf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CMulf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CDivf _ -> tyarrows_ [tyfloat_, tyfloat_, tyfloat_]
  | CNegf _ -> tyarrow_ tyfloat_ tyfloat_
end

lang FloatIntConversionAst = IntAst + FloatAst
  syn Const =
  | CFloorfi {}
  | CCeilfi {}
  | CRoundfi {}
  | CInt2float {}

  sem tyConst =
  | CFloorfi _ -> tyarrow_ tyfloat_ tyint_
  | CCeilfi _ -> tyarrow_ tyfloat_ tyint_
  | CRoundfi _ -> tyarrow_ tyfloat_ tyint_
  | CInt2float _ -> tyarrow_ tyint_ tyfloat_
end

lang BoolAst = ConstAst
  syn Const =
  | CBool {val : Bool}

  sem tyConst =
  | CBool _ -> tybool_
end

lang CmpIntAst = IntAst + BoolAst
  syn Const =
  | CEqi {}
  | CNeqi {}
  | CLti {}
  | CGti {}
  | CLeqi {}
  | CGeqi {}

  sem tyConst =
  | CEqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CNeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGti _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CLeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
  | CGeqi _ -> tyarrows_ [tyint_, tyint_, tybool_]
end

lang CmpFloatAst = FloatAst + BoolAst
  syn Const =
  | CEqf {}
  | CLtf {}
  | CLeqf {}
  | CGtf {}
  | CGeqf {}
  | CNeqf {}

  sem tyConst =
  | CEqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CLeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGtf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CGeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
  | CNeqf _ -> tyarrows_ [tyfloat_, tyfloat_, tybool_]
end

lang CharAst = ConstAst
  syn Const =
  | CChar {val : Char}

  sem tyConst =
  | CChar _ -> tychar_
end

lang CmpCharAst = CharAst + BoolAst
  syn Const =
  | CEqc {}

  sem tyConst =
  | CEqc _ -> tyarrows_ [tychar_, tychar_, tybool_]
end

lang IntCharConversionAst = IntAst + CharAst
  syn Const =
  | CInt2Char {}
  | CChar2Int {}

  sem tyConst =
  | CInt2Char _ -> tyarrow_ tyint_ tychar_
  | CChar2Int _ -> tyarrow_ tychar_ tyint_
end

lang FloatStringConversionAst = SeqAst + FloatAst
  syn Const =
  | CString2float {}

  sem tyConst =
  | CString2float _ -> tyarrow_ tystr_ tyfloat_
end

lang SymbAst = ConstAst
  syn Const =
  | CSymb {val : Symb}
  | CGensym {}
  | CSym2hash {}

  sem tyConst =
  | CSymb _ -> tysym_
  | CGensym _ -> tyarrow_ tyunit_ tysym_
  | CSym2hash _ -> tyarrow_ tysym_ tyint_
end

lang CmpSymbAst = SymbAst + BoolAst
  syn Const =
  | CEqsym {}

  sem tyConst =
  | CEqsym _ -> tyarrows_ [tysym_, tysym_, tybool_]
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

  sem tyConst =
  | CSet _ -> tyarrows_ [tygenericseq_ "a", tyint_,
                         tygeneric_ "a", tygenericseq_ "a"]
  | CGet _ -> tyarrows_ [tygenericseq_ "a", tyint_, tygeneric_ "a"]
  | CCons _ -> tyarrows_ [tygeneric_ "a", tygenericseq_ "a", tygenericseq_ "a"]
  | CSnoc _ -> tyarrows_ [tygenericseq_ "a", tygeneric_ "a", tygenericseq_ "a"]
  | CConcat _ -> tyarrows_ [tygenericseq_ "a", tygenericseq_ "a",
                            tygenericseq_ "a"]
  | CLength _ -> tyarrow_ (tygenericseq_ "a") tyint_
  | CReverse _ -> tyarrow_ (tygenericseq_ "a") (tygenericseq_ "a")
  | CCreate _ -> tyarrows_ [tyint_, tyarrow_ tyint_ (tygeneric_ "a"),
                            tygenericseq_ "a"]
  | CSplitAt _ -> tyarrows_ [tygenericseq_ "a", tyint_,
                             tytuple_ [tygenericseq_ "a", tygenericseq_ "a"]]
  | CSubsequence _ -> tyarrows_ [tygenericseq_ "a", tyint_, tyint_,
                                 tygenericseq_ "a"]
end

lang FileOpAst = ConstAst
  syn Const =
  | CFileRead {}
  | CFileWrite {}
  | CFileExists {}
  | CFileDelete {}

  sem tyConst =
  | CFileRead _ -> tyarrow_ tystr_ tystr_
  | CFileWrite _ -> tyarrows_ [tystr_, tystr_, tyunit_]
  | CFileExists _ -> tyarrow_ tystr_ tybool_
  | CFileDelete _ -> tyarrow_ tystr_ tyunit_
end

lang IOAst = ConstAst
  syn Const =
  | CPrint {}
  | CDPrint {}
  | CReadLine {}
  | CReadBytesAsString {}

  sem tyConst =
  | CPrint _ -> tyarrow_ tystr_ tyunit_
  | CDPrint _ -> tyarrow_ tystr_ tyunit_
  | CReadLine _ -> tyarrow_ tyunit_ tystr_
  | CReadBytesAsString _ -> tyarrow_ tyint_ (tytuple_ [tystr_, tystr_])
end

lang RandomNumberGeneratorAst = ConstAst
  syn Const =
  | CRandIntU {}
  | CRandSetSeed {}

  sem tyConst =
  | CRandIntU _ -> tyarrows_ [tyint_, tyint_, tyint_]
  | CRandSetSeed _ -> tyarrow_ tyint_ tyunit_
end

lang SysAst = ConstAst
  syn Const =
  | CExit {}
  | CError {}
  | CArgv {}

  sem tyConst =
  | CExit _ -> tyarrow_ tyint_ tyunknown_
  | CError _ -> tyarrow_ tyint_ tyunknown_
  | CArgv _ -> tyseq_ tystr_
end

lang TimeAst = ConstAst
  syn Const =
  | CWallTimeMs {}
  | CSleepMs {}

  sem tyConst =
  | CWallTimeMs _ -> tyarrow_ tyunit_ tyfloat_
  | CSleepMs _ -> tyarrow_ tyint_ tyunit_
end

lang RefOpAst = ConstAst + RefAst
  syn Const =
  | CRef {}
  | CModRef {}
  | CDeRef {}

  sem tyConst =
  | CRef _ -> tyarrow_ (tygeneric_ "a") tyref_
  | CModRef _ -> tyarrow_ tyref_ (tygeneric_ "a")
  | CDeRef _ -> tyarrows_ [tyref_, tygeneric_ "a", tyunit_]
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

  sem tyConst =
  | CMapEmpty _ -> tyarrow_ (tyarrows_ [tygeneric_ "a", tygeneric_ "a", tyint_])
                            tymap_
  | CMapInsert _ -> tyarrows_ [tygeneric_ "a", tygeneric_ "b", tymap_, tymap_]
  | CMapRemove _ -> tyarrows_ [tygeneric_ "a", tymap_, tymap_]
  | CMapFindWithExn _ -> tyarrows_ [tygeneric_ "a", tymap_, tygeneric_ "b"]
  | CMapFindOrElse _ -> tyarrows_ [tyarrow_ tyunit_ (tygeneric_ "b"),
                                   tygeneric_ "a", tymap_, tygeneric_ "b"]
  | CMapFindApplyOrElse _ ->
    tyarrows_ [tyarrow_ (tygeneric_ "b") (tygeneric_ "c"),
               tyarrow_ tyunit_ (tygeneric_ "c"), tygeneric_ "a",
               tymap_, tygeneric_ "c"]
  | CMapBindings _ -> tyarrow_ tymap_
                               (tyseq_ (tytuple_ [tygeneric_ "a", tygeneric_ "b"]))
  | CMapSize _ -> tyarrow_ tymap_ tyint_
  | CMapMem _ -> tyarrows_ [tygeneric_ "a", tymap_, tyint_]
  | CMapAny _ -> tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b", tybool_],
                            tymap_, tybool_]
  | CMapMap _ -> tyarrows_ [tyarrow_ (tygeneric_ "b") (tygeneric_ "c"),
                            tymap_, tymap_]
  | CMapMapWithKey _ ->
    tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b", tygeneric_ "c"],
               tymap_, tymap_]
  | CMapFoldWithKey _ ->
    tyarrows_ [tyarrows_ [tygeneric_ "a", tygeneric_ "b",
                          tygeneric_ "c", tygeneric_ "c"],
               tygeneric_ "c", tymap_, tygeneric_ "c"]
  | CMapEq _ -> tyarrows_ [tyarrows_ [tygeneric_ "b", tygeneric_ "b", tybool_],
                           tymap_, tymap_, tybool_]
  | CMapCmp _ -> tyarrows_ [tyarrows_ [tygeneric_ "b", tygeneric_ "b", tyint_],
                            tymap_, tymap_, tyint_]
  | CMapGetCmpFun _ -> tyarrows_ [tymap_, tygeneric_ "a", tygeneric_ "a", tyint_]
end

lang TensorOpAst = ConstAst
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

  sem tyConst =
  | CTensorCreate _ -> tyarrows_ [tyseq_ tyint_,
                                  tyarrow_ (tyseq_ tyint_) (tygeneric_ "a"),
                                  tygenerictensor_ "a"]
  | CTensorGetExn _ -> tyarrows_ [tygenerictensor_ "a", tyseq_ tyint_,
                                  tygeneric_ "a"]
  | CTensorSetExn _ -> tyarrows_ [tygenerictensor_ "a", tyseq_ tyint_,
                                  tygeneric_ "a", tyunit_]
  | CTensorRank _ -> tyarrow_ (tygenerictensor_ "a") tyint_
  | CTensorShape _ -> tyarrow_ (tygenerictensor_ "a") (tyseq_ tyint_)
  | CTensorReshapeExn _ -> tyarrows_ [tygenerictensor_ "a",
                                      tyseq_ tyint_, tygenerictensor_ "a"]
  | CTensorCopyExn _ -> tyarrows_ [tygenerictensor_ "a", tygenerictensor_ "a",
                                   tyunit_]
  | CTensorSliceExn _ -> tyarrows_ [tygenerictensor_ "a", tyseq_ tyint_,
                                    tygenerictensor_ "a"]
  | CTensorSubExn _ -> tyarrows_ [tygenerictensor_ "a", tyint_, tyint_,
                                  tygenerictensor_ "a"]
  | CTensorIteri _ -> tyarrows_ [tyarrows_ [tyint_, tygenerictensor_ "a",
                                            tyunit_],
                                 tygenerictensor_ "a", tyunit_]
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

  sem tyConst =
  | CBootParserParseMExprString _ -> tyarrow_ tystr_ tybootparsetree_
  | CBootParserParseMCoreFile _ -> tyarrow_ tystr_ tybootparsetree_
  | CBootParserGetId _ -> tyarrow_ tybootparsetree_ tyint_
  | CBootParserGetTerm _ -> tyarrow_ tybootparsetree_ tybootparsetree_
  | CBootParserGetType _ -> tyarrow_ tybootparsetree_ tybootparsetree_
  | CBootParserGetString _ -> tyarrow_ tybootparsetree_ tystr_
  | CBootParserGetInt _ -> tyarrow_ tybootparsetree_ tyint_
  | CBootParserGetFloat _ -> tyarrow_ tybootparsetree_ tyfloat_
  | CBootParserGetListLength _ -> tyarrow_ tybootparsetree_ tyint_
  | CBootParserGetConst _ -> tyarrow_ tybootparsetree_ tybootparsetree_
  | CBootParserGetPat _ -> tyarrow_ tybootparsetree_ tybootparsetree_
  | CBootParserGetInfo _ -> tyarrow_ tybootparsetree_ tybootparsetree_
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

------------------------
-- MEXPR AST FRAGMENT --
------------------------

lang MExprAst =

  -- Terms
  VarAst + AppAst + LamAst + RecordAst + LetAst + TypeAst + RecLetsAst +
  ConstAst + DataAst + MatchAst + UtestAst + SeqAst + NeverAst + RefAst +

  -- Types
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + RecordTypeAst + VariantTypeAst + VarTypeAst +
  AppTypeAst +

  -- Constants
  IntAst + ArithIntAst + ShiftIntAst + FloatAst + ArithFloatAst + BoolAst +
  CmpIntAst + IntCharConversionAst + CmpFloatAst + CharAst + CmpCharAst +
  SymbAst + CmpSymbAst + SeqOpAst + FileOpAst + IOAst +
  RandomNumberGeneratorAst + SysAst + FloatIntConversionAst +
  FloatStringConversionAst + TimeAst + RefOpAst + MapAst + TensorOpAst +
  BootParserAst +

  -- Patterns
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat
