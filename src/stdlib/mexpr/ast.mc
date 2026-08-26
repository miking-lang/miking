-- Language fragments of MExpr

include "info.mc"
include "name.mc"
include "string.mc"
include "stringid.mc"
include "map.mc"
include "set.mc"
include "seq.mc"
include "basic-types.mc"
include "option.mc"

-----------
-- TERMS --
-----------

-- Shared fragment
lang Ast

  syn Expr =
  -- Intentionally left blank

  syn Decl =
  -- Intentionally left blank

  syn Type =
  -- Intentionally left blank

  syn Kind =
  -- Intentionally left blank

  syn Pat =
  -- Intentionally left blank

  sem infoTm: Expr -> Info
  sem tyTm: Expr -> Type
  sem withInfo: Info -> Expr -> Expr
  sem withType: Type -> Expr -> Expr

  sem infoPat: Pat -> Info
  sem tyPat: Pat -> Type
  sem withInfoPat: Info -> Pat -> Pat
  sem withTypePat: Type -> Pat -> Pat

  sem infoDecl: Decl -> Info
  sem declWithInfo: Info -> Decl -> Decl

  sem infoTy: Type -> Info
  sem tyWithInfo: Info -> Type -> Type

  sem smapAccumL_Expr_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Expr -> (acc, Expr)
  sem smapAccumL_Expr_Expr f acc =
  | p -> (acc, p)

  sem smap_Expr_Expr : (Expr -> Expr) -> Expr -> Expr
  sem smap_Expr_Expr f =
  | p ->
    let res = smapAccumL_Expr_Expr (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Expr_Expr : all acc. (acc -> Expr -> acc) -> acc -> Expr -> acc
  sem sfold_Expr_Expr f acc =
  | p ->
    let res = smapAccumL_Expr_Expr (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem mapAccumLPre_Expr_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Expr -> (acc, Expr)
  sem mapAccumLPre_Expr_Expr f acc =
  | expr ->
    match f acc expr with (acc,expr) in
    smapAccumL_Expr_Expr (mapAccumLPre_Expr_Expr f) acc expr

  sem mapAccumLPost_Expr_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Expr -> (acc, Expr)
  sem mapAccumLPost_Expr_Expr f acc =
  | expr ->
    match smapAccumL_Expr_Expr (mapAccumLPost_Expr_Expr f) acc expr with (acc,expr) in
    f acc expr

  sem mapPre_Expr_Expr : (Expr -> Expr) -> Expr -> Expr
  sem mapPre_Expr_Expr f =
  | expr ->
    let expr = f expr in
    smap_Expr_Expr (mapPre_Expr_Expr f) expr

  sem mapPost_Expr_Expr : (Expr -> Expr) -> Expr -> Expr
  sem mapPost_Expr_Expr f =
  | expr -> f (smap_Expr_Expr (mapPost_Expr_Expr f) expr)

  sem foldPre_Expr_Expr : all acc. (acc -> Expr -> acc) -> acc -> Expr -> acc
  sem foldPre_Expr_Expr f acc =
  | expr ->
    let acc = f acc expr in
    sfold_Expr_Expr (foldPre_Expr_Expr f) acc expr

  sem foldPost_Expr_Expr : all acc. (acc -> Expr -> acc) -> acc -> Expr -> acc
  sem foldPost_Expr_Expr f acc =
  | expr ->
    f (sfold_Expr_Expr (foldPost_Expr_Expr f) acc expr) expr

  -- NOTE(vipa, 2021-05-28): This function *does not* touch the `ty`
  -- field. It only covers nodes in the AST, so to speak, not
  -- annotations thereof.
  sem smapAccumL_Expr_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Expr -> (acc, Expr)
  sem smapAccumL_Expr_Type f acc =
  | p -> (acc, p)

  sem smap_Expr_Type : (Type -> Type) -> Expr -> Expr
  sem smap_Expr_Type f =
  | p ->
    let res = smapAccumL_Expr_Type (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Expr_Type : all acc. (acc -> Type -> acc) -> acc -> Expr -> acc
  sem sfold_Expr_Type f acc =
  | p ->
    let res = smapAccumL_Expr_Type (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  -- NOTE(aathn, 2022-11-15): This function covers the compiler-added annotations
  -- which are not touched by smapAccumL_Expr_Type.
  sem smapAccumL_Expr_TypeLabel : all acc. (acc -> Type -> (acc, Type)) -> acc -> Expr -> (acc, Expr)
  sem smapAccumL_Expr_TypeLabel f acc =
  | p ->
    match f acc (tyTm p) with (acc, ty) in
    (acc, withType ty p)

  sem smap_Expr_TypeLabel : (Type -> Type) -> Expr -> Expr
  sem smap_Expr_TypeLabel f =
  | p ->
    let res = smapAccumL_Expr_TypeLabel (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Expr_TypeLabel : all acc. (acc -> Type -> acc) -> acc -> Expr -> acc
  sem sfold_Expr_TypeLabel f acc =
  | p ->
    let res = smapAccumL_Expr_TypeLabel (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem smapAccumL_Expr_Pat : all acc. (acc -> Pat -> (acc, Pat)) -> acc -> Expr -> (acc, Expr)
  sem smapAccumL_Expr_Pat f acc =
  | p -> (acc, p)

  sem smap_Expr_Pat : (Pat -> Pat) -> Expr -> Expr
  sem smap_Expr_Pat f =
  | p ->
    match smapAccumL_Expr_Pat (lam. lam a. ((), f a)) () p with (_, p) in
    p

  sem sfold_Expr_Pat : all acc. (acc -> Pat -> acc) -> acc -> Expr -> acc
  sem sfold_Expr_Pat f acc =
  | p ->
    match smapAccumL_Expr_Pat (lam acc. lam a. (f acc a, a)) acc p
    with (acc, _) in acc

  sem smapAccumL_Decl_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Expr f acc = | d -> (acc, d)

  sem smap_Decl_Expr : (Expr -> Expr) -> Decl -> Decl
  sem smap_Decl_Expr f = | d -> (smapAccumL_Decl_Expr (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Expr : all acc. (acc -> Expr -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Expr f acc = | d -> (smapAccumL_Decl_Expr (lam acc. lam a. (f acc a, a)) acc d).0

  sem smapAccumL_Decl_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Type f acc = | d -> (acc, d)

  sem smap_Decl_Type : (Type -> Type) -> Decl -> Decl
  sem smap_Decl_Type f = | d -> (smapAccumL_Decl_Type (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Type : all acc. (acc -> Type -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Type f acc = | d -> (smapAccumL_Decl_Type (lam acc. lam a. (f acc a, a)) acc d).0

  sem smapAccumL_Decl_TypeLabel : all acc. (acc -> Type -> (acc, Type)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_TypeLabel f acc = | d -> (acc, d)

  sem smap_Decl_TypeLabel : (Type -> Type) -> Decl -> Decl
  sem smap_Decl_TypeLabel f =
  | p ->
    let res = smapAccumL_Decl_TypeLabel (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Decl_TypeLabel : all acc. (acc -> Type -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_TypeLabel f acc =
  | p ->
    let res = smapAccumL_Decl_TypeLabel (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem smapAccumL_Decl_Decl : all acc. (acc -> Decl -> (acc, Decl)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Decl f acc = | d -> (acc, d)
  sem smapAccumL_Decl_Pat : all acc. (acc -> Pat -> (acc, Pat)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Pat f acc = | d -> (acc, d)

  sem smap_Decl_Decl : (Decl -> Decl) -> Decl -> Decl
  sem smap_Decl_Decl f = | d -> (smapAccumL_Decl_Decl (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Decl : all acc. (acc -> Decl -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Decl f acc = | d -> (smapAccumL_Decl_Decl (lam acc. lam a. (f acc a, a)) acc d).0

  sem smap_Decl_Pat : (Pat -> Pat) -> Decl -> Decl
  sem smap_Decl_Pat f = | d -> (smapAccumL_Decl_Pat (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Pat : all acc. (acc -> Pat -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Pat f acc = | d -> (smapAccumL_Decl_Pat (lam acc. lam a. (f acc a, a)) acc d).0

  sem smapAccumL_Type_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Type -> (acc, Type)
  sem smapAccumL_Type_Type f acc =
  | p -> (acc, p)

  sem smap_Type_Type : (Type -> Type) -> Type -> Type
  sem smap_Type_Type f =
  | p ->
    let res = smapAccumL_Type_Type (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Type_Type : all acc. (acc -> Type -> acc) -> acc -> Type -> acc
  sem sfold_Type_Type f acc =
  | p ->
    let res = smapAccumL_Type_Type (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  -- Resolving application -- apply an accumulating function through links and aliases
  sem rappAccumL_Type_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Type -> (acc, Type)
  sem rappAccumL_Type_Type f acc = | ty -> (acc, ty)

  sem rapp_Type_Type : (Type -> Type) -> Type -> Type
  sem rapp_Type_Type f = | ty ->
    let res  = rappAccumL_Type_Type (lam. lam t. ((), f t)) () ty in
    res.1

  -- Strip all-quantifiers and aliases to inspect the structure of the type
  sem inspectType : Type -> Type
  sem inspectType = | ty -> rapp_Type_Type inspectType ty

  -- Unwrap links and aliases to expose the underlying type
  sem unwrapType : Type -> Type
  sem unwrapType = | ty -> rapp_Type_Type unwrapType ty

  sem smapAccumL_Kind_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Kind -> (acc, Kind)
  sem smapAccumL_Kind_Type f acc =
  | s -> (acc, s)

  sem smap_Kind_Type : (Type -> Type) -> Kind -> Kind
  sem smap_Kind_Type (f : Type -> Type) =
  | s ->
    match smapAccumL_Kind_Type (lam. lam x. ((), f x)) () s with (_, s) in s

  sem sfold_Kind_Type : all acc. (acc -> Type -> acc) -> acc -> Kind -> acc
  sem sfold_Kind_Type (f : acc -> Type -> acc) (acc : acc) =
  | s ->
    match smapAccumL_Kind_Type (lam a. lam x. (f a x, x)) acc s with (a, _) in a

  sem smapAccumL_Pat_Pat : all acc. (acc -> Pat -> (acc, Pat)) -> acc -> Pat -> (acc, Pat)
  sem smapAccumL_Pat_Pat f acc =
  | p -> (acc, p)

  sem smap_Pat_Pat : (Pat -> Pat) -> Pat -> Pat
  sem smap_Pat_Pat f =
  | p ->
    let res = smapAccumL_Pat_Pat (lam. lam a. ((), f a)) () p in
    res.1

  sem sfold_Pat_Pat : all acc. (acc -> Pat -> acc) -> acc -> Pat -> acc
  sem sfold_Pat_Pat f acc =
  | p ->
    let res = smapAccumL_Pat_Pat (lam acc. lam a. (f acc a, a)) acc p in
    res.0

  sem smapAccumL_Pat_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Pat -> (acc, Pat)
  sem smapAccumL_Pat_Expr f acc =
  | p -> (acc, p)

  sem smap_Pat_Expr : (Expr -> Expr) -> Pat -> Pat
  sem smap_Pat_Expr f =
  | p ->
    match smapAccumL_Pat_Expr (lam. lam a. ((), f a)) () p with (_, p) in
    p

  sem sfold_Pat_Expr : all acc. (acc -> Expr -> acc) -> acc -> Pat -> acc
  sem sfold_Pat_Expr f acc =
  | p ->
    match smapAccumL_Pat_Expr (lam acc. lam a. (f acc a, a)) acc p
    with (acc, _) in acc

  sem smapAccumL_Pat_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Pat -> (acc, Pat)
  sem smapAccumL_Pat_Type f acc =
  | p -> (acc, p)

  sem smap_Pat_Type : (Type -> Type) -> Pat -> Pat
  sem smap_Pat_Type f =
  | p ->
    match smapAccumL_Pat_Type (lam. lam a. ((), f a)) () p with (_, p) in
    p

  sem sfold_Pat_Type : all acc. (acc -> Type -> acc) -> acc -> Pat -> acc
  sem sfold_Pat_Type f acc =
  | p ->
    match smapAccumL_Pat_Type (lam acc. lam a. (f acc a, a)) acc p
    with (acc, _) in acc

  sem countExprNodes count = | t ->
    let count = addi count 1 in
    let count = sfold_Expr_Expr countExprNodes count t in
    let count = sfold_Expr_Type countTypeNodes count t in
    let count = sfold_Expr_TypeLabel countTypeNodes count t in
    let count = sfold_Expr_Pat countPatNodes count t in
    count
  sem countTypeNodes count = | t ->
    let count = addi count 1 in
    let count = sfold_Type_Type countTypeNodes count t in
    count
  sem countPatNodes count = | t ->
    let count = addi count 1 in
    let count = sfold_Pat_Pat countPatNodes count t in
    let count = sfold_Pat_Expr countExprNodes count t in
    let count = sfold_Pat_Type countTypeNodes count t in
    count
end

-- TmOpaque
lang OpaqueAst = Ast
  -- NOTE(vipa, 2026-02-05): TmOpaque is special, in the sense that
  -- its body should never be transformed by the compiler, with a
  -- small set of exceptions. This means that whatever code is put in
  -- an opaque block must already be transformed to a sufficiently
  -- low-level form that whatever backend is in use can compile
  -- it. Analysis is allowed however, which means that `sfold` works
  -- as expected, but `smap` and `smapAccumL` will explicitly crash.
  --
  -- Transformations that are allowed:
  -- * Renaming to something alpha-equivalent
  -- * Attaching results of type inference
  syn Expr +=
  | TmOpaque
    { body : Expr
    , info : Info
    , ty : Type
    }

  sem infoTm +=
  | TmOpaque x -> x.info

  sem withInfo info +=
  | TmOpaque x -> TmOpaque {x with info = info}

  sem tyTm +=
  | TmOpaque x -> x.ty

  sem withType ty +=
  | TmOpaque x -> TmOpaque {x with ty = ty}

  sem sfold_Expr_Expr f acc +=
  | TmOpaque x -> f acc x.body

  sem smapAccumL_Expr_Expr f acc +=
  | TmOpaque x ->
    printError "Compiler error: called `smap` or `smapAccumL` on a `TmOpaque`, but it must be special-cased since transformation isn't allowed.\n";
    flushStderr ();
    never

  sem mapPre_Expr_Expr f +=
  | tm & TmOpaque _ -> tm

  sem mapPost_Expr_Expr f +=
  | tm & TmOpaque _ -> tm

  -- Traverse an `Expr`, replacing any `TmOpaque` with its `body`. Its
  -- body is meant to already be in a form the backend can compile
  -- directly, so this is only safe to do right before handing the
  -- AST off to the backend, once no more transformations that would
  -- need to special-case `TmOpaque` remain.
  sem removeOpaqueExpr : Expr -> Expr
  sem removeOpaqueExpr =
  | TmOpaque x -> removeOpaqueExpr x.body
  | t -> smap_Expr_Expr removeOpaqueExpr t
end

-- TmVar --
lang VarAst = Ast
  type TmVarRec =
    { ident : Name
    , ty: Type
    , info: Info
    , frozen: Bool
    }

  syn Expr +=
  | TmVar TmVarRec

  sem infoTm +=
  | TmVar r -> r.info

  sem tyTm +=
  | TmVar t -> t.ty

  sem withInfo info +=
  | TmVar t -> TmVar {t with info = info}

  sem withType (ty : Type) +=
  | TmVar t -> TmVar {t with ty = ty}
end


-- TmApp --
lang AppAst = Ast
  syn Expr +=
  | TmApp {lhs : Expr,
           rhs : Expr,
           ty: Type,
           info: Info}

  sem infoTm +=
  | TmApp r -> r.info

  sem tyTm +=
  | TmApp t -> t.ty

  sem withInfo info +=
  | TmApp t -> TmApp {t with info = info}

  sem withType (ty : Type) +=
  | TmApp t -> TmApp {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmApp t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, TmApp {{t with lhs = lhs} with rhs = rhs})
      else never
    else never
end


-- TmLam --
lang LamAst = Ast
  syn Expr +=
  | TmLam {ident : Name,
           tyAnnot : Type,
           tyParam : Type,
           body : Expr,
           ty : Type,
           info : Info}

  sem infoTm +=
  | TmLam r -> r.info

  sem tyTm +=
  | TmLam t -> t.ty

  sem withInfo info +=
  | TmLam t -> TmLam {t with info = info}

  sem withType (ty : Type) +=
  | TmLam t -> TmLam {t with ty = ty}

  sem smapAccumL_Expr_Type f acc +=
  | TmLam t ->
    match f acc t.tyAnnot with (acc, tyAnnot) in
    (acc, TmLam {t with tyAnnot = tyAnnot})

  sem smapAccumL_Expr_TypeLabel f acc +=
  | TmLam t ->
    match f acc t.tyParam with (acc, tyParam) in
    match f acc t.ty with (acc, ty) in
    (acc, TmLam {t with tyParam = tyParam, ty = ty})

  sem smapAccumL_Expr_Expr f acc +=
  | TmLam t ->
    match f acc t.body with (acc, body) in
    (acc, TmLam {t with body = body})
end

-- TmDecl --
lang DeclAst = Ast
  syn Expr +=
  | TmDecl {decl : Decl, inexpr : Expr, info : Info, ty : Type}

  sem infoTm += | TmDecl x -> x.info
  sem tyTm += | TmDecl x -> x.ty
  sem withInfo info += | TmDecl x -> TmDecl {x with info = info}
  sem withType ty += | TmDecl x -> TmDecl {x with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmDecl x ->
    -- NOTE(vipa, 2025-05-07): We currently see a TmDecl as a
    -- composite value that includes the Decl in itself, thus
    -- smapAccumL looks "through" the decl as well
    match smapAccumL_Decl_Expr f acc x.decl with (acc, decl) in
    match f acc x.inexpr with (acc, inexpr) in
    (acc, TmDecl {x with decl = decl, inexpr = inexpr})

  sem smapAccumL_Expr_Type f acc +=
  | TmDecl x ->
    -- NOTE(vipa, 2025-05-07): We currently see a TmDecl as a
    -- composite value that includes the Decl in itself, thus
    -- smapAccumL looks "through" the decl as well
    match smapAccumL_Decl_Type f acc x.decl with (acc, decl) in
    (acc, TmDecl {x with decl = decl})

  sem smapAccumL_Expr_TypeLabel f acc +=
  | TmDecl x ->
    match smapAccumL_Decl_TypeLabel f acc x.decl with (acc, decl) in
    match f acc x.ty with (acc, ty) in
    (acc, TmDecl {x with decl = decl, ty = ty})
end

-- DeclLetRecord --
lang LetDeclAst = DeclAst
  type DeclLetRecord =
    { ident : Name
    , tyAnnot : Type
    , tyBody : Type
    , body : Expr
    , info: Info
    }

  syn Decl +=
  | DeclLet DeclLetRecord

  sem infoDecl +=
  | DeclLet d -> d.info

  sem declWithInfo info +=
  | DeclLet d -> DeclLet {d with info = info}

  sem smapAccumL_Decl_Expr f acc +=
  | DeclLet x ->
    match f acc x.body with (acc, body) in
    (acc, DeclLet {x with body = body})

  sem smapAccumL_Decl_Type f acc +=
  | DeclLet x ->
    match f acc x.tyAnnot with (acc, tyAnnot) in
    (acc, DeclLet {x with tyAnnot = tyAnnot})

  sem smapAccumL_Decl_TypeLabel f acc +=
  | DeclLet x ->
    match f acc x.tyBody with (acc, tyBody) in
    (acc, DeclLet {x with tyBody = tyBody})
end

-- DeclRecLets --
lang RecLetsDeclAst = DeclAst + LetDeclAst
  syn Decl +=
  | DeclRecLets
    { bindings : [DeclLetRecord]
    , info : Info
    }

  sem infoDecl +=
  | DeclRecLets d -> d.info

  sem declWithInfo info +=
  | DeclRecLets d -> DeclRecLets {d with info = info}

  sem smapAccumL_Decl_Type f acc +=
  | DeclRecLets x ->
    let fbinding = lam acc. lam b.
      match f acc b.tyAnnot with (acc, tyAnnot) in
      (acc, {b with tyAnnot = tyAnnot}) in
    match mapAccumL fbinding acc x.bindings with (acc, bindings) in
    (acc, DeclRecLets {x with bindings = bindings})

  sem smapAccumL_Decl_Expr f acc +=
  | DeclRecLets x ->
    let fbinding = lam acc. lam b.
      match f acc b.body with (acc, body) in
      (acc, {b with body = body}) in
    match mapAccumL fbinding acc x.bindings with (acc, bindings) in
    (acc, DeclRecLets {x with bindings = bindings})

  sem smapAccumL_Decl_TypeLabel f acc +=
  | DeclRecLets x ->
    let fbinding = lam acc. lam b.
      match f acc b.tyBody with (acc, tyBody) in
      (acc, {b with tyBody = tyBody}) in
    match mapAccumL fbinding acc x.bindings with (acc, bindings) in
    (acc, DeclRecLets {x with bindings = bindings})
end

-- TmConst --
lang ConstAst = Ast
  syn Const =

  syn Expr +=
  | TmConst {val : Const,
             ty: Type,
             info: Info}

  sem infoTm +=
  | TmConst r -> r.info

  sem tyTm +=
  | TmConst t -> t.ty

  sem withInfo info +=
  | TmConst t -> TmConst {t with info = info}

  sem withType (ty : Type) +=
  | TmConst t -> TmConst {t with ty = ty}
end

-- TmSeq --
lang SeqAst = Ast
  syn Expr +=
  | TmSeq {tms : [Expr],
           ty: Type,
           info: Info}

  sem infoTm +=
  | TmSeq r -> r.info

  sem tyTm +=
  | TmSeq t -> t.ty

  sem withInfo info +=
  | TmSeq t -> TmSeq {t with info = info}

  sem withType (ty : Type) +=
  | TmSeq t -> TmSeq {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmSeq t ->
    match mapAccumL f acc t.tms with (acc, tms) then
      (acc, TmSeq {t with tms = tms})
    else never
end


-- TmRecord and TmRecordUpdate --
lang RecordAst = Ast
  syn Expr +=
  | TmRecord {bindings : Map SID Expr,
              ty : Type,
              info : Info}
  | TmRecordUpdate {rec : Expr,
                    key : SID,
                    value : Expr,
                    ty : Type,
                    info : Info}

  sem infoTm +=
  | TmRecord r -> r.info
  | TmRecordUpdate r -> r.info

  sem tyTm +=
  | TmRecord t -> t.ty
  | TmRecordUpdate t -> t.ty

  sem withInfo info +=
  | TmRecord t -> TmRecord {t with info = info}
  | TmRecordUpdate t -> TmRecordUpdate {t with info = info}

  sem withType (ty : Type) +=
  | TmRecord t -> TmRecord {t with ty = ty}
  | TmRecordUpdate t -> TmRecordUpdate {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
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

-- DeclType --
lang TypeDeclAst = DeclAst
  syn Decl +=
  | DeclType {ident : Name,
              params : [Name],
              tyIdent : Type,
              info : Info}

  sem infoDecl +=
  | DeclType d -> d.info

  sem declWithInfo info +=
  | DeclType d -> DeclType {d with info = info}

  sem smapAccumL_Decl_Type f acc +=
  | DeclType x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclType {x with tyIdent = tyIdent})
end

-- DeclConDef --
lang DataDeclAst = DeclAst
  syn Decl +=
  | DeclConDef {ident : Name,
                tyIdent : Type,
                info : Info}

  sem infoDecl +=
  | DeclConDef d -> d.info

  sem declWithInfo info +=
  | DeclConDef d -> DeclConDef {d with info = info}

  sem smapAccumL_Decl_Type f acc +=
  | DeclConDef x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclConDef {x with tyIdent = tyIdent})
end

-- TmConApp --
lang DataAst = Ast
  syn Expr +=
  | TmConApp {ident : Name,
              body : Expr,
              ty : Type,
              info: Info}

  sem infoTm +=
  | TmConApp r -> r.info

  sem tyTm +=
  | TmConApp t -> t.ty

  sem withInfo info +=
  | TmConApp t -> TmConApp {t with info = info}

  sem withType (ty : Type) +=
  | TmConApp t -> TmConApp {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmConApp t ->
    match f acc t.body with (acc, body) then
      (acc, TmConApp {t with body = body})
    else never
end

-- TmMatch --
lang MatchAst = Ast
  syn Expr +=
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr,
             ty     : Type,
             info   : Info}

  syn Pat +=
  -- Intentionally left blank

  sem infoTm +=
  | TmMatch r -> r.info

  sem tyTm +=
  | TmMatch t -> t.ty

  sem withInfo info +=
  | TmMatch t -> TmMatch {t with info = info}

  sem withType (ty : Type) +=
  | TmMatch t -> TmMatch {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmMatch t ->
    match f acc t.target with (acc, target) then
      match f acc t.thn with (acc, thn) then
        match f acc t.els with (acc, els) then
          (acc, TmMatch {{{t with target = target} with thn = thn} with els = els})
        else never
      else never
    else never

  sem smapAccumL_Expr_Pat f acc +=
  | TmMatch t ->
    match f acc t.pat with (acc, pat) in
    (acc, TmMatch {t with pat = pat})
end

-- DeclUtest --
lang UtestDeclAst = DeclAst
  syn Decl +=
  | DeclUtest {test : Expr,
               expected : Expr,
               tusing : Option Expr,
               tonfail : Option Expr,
               info : Info}

  sem infoDecl +=
  | DeclUtest d -> d.info

  sem declWithInfo info +=
  | DeclUtest d -> DeclUtest {d with info = info}

  sem smapAccumL_Decl_Expr f acc +=
  | DeclUtest x ->
    match f acc x.test with (acc, test) in
    match f acc x.expected with (acc, expected) in
    match optionMapAccum f acc x.tusing with (acc, tusing) in
    match optionMapAccum f acc x.tonfail with (acc, tonfail) in
    (acc, DeclUtest {x with test = test,
                            expected = expected,
                            tusing = tusing,
                            tonfail = tonfail})
end

-- TmNever --
lang NeverAst = Ast
  syn Expr +=
  | TmNever {ty: Type,
            info: Info}

  sem infoTm +=
  | TmNever r -> r.info

  sem tyTm +=
  | TmNever t -> t.ty

  sem withInfo info +=
  | TmNever t -> TmNever {t with info = info}

  sem withType (ty : Type) +=
  | TmNever t -> TmNever {t with ty = ty}
end

-- TmPlaceholder --
lang PlaceholderAst = Ast
  syn Expr +=
  | TmPlaceholder {ty : Type,
                   info : Info}

  sem infoTm +=
  | TmPlaceholder t -> t.info

  sem withInfo info +=
  | TmPlaceholder t -> TmPlaceholder {t with info = info}

  sem tyTm +=
  | TmPlaceholder t -> t.ty

  sem withType ty +=
  | TmPlaceholder t -> TmPlaceholder {t with ty = ty}
end

-- DeclExt --
lang ExtDeclAst = DeclAst
  syn Decl +=
  | DeclExt {ident : Name,
             tyIdent : Type,
             effect : Bool,
             info : Info}

  sem infoDecl +=
  | DeclExt d -> d.info

  sem declWithInfo info +=
  | DeclExt d -> DeclExt {d with info = info}

  sem smapAccumL_Decl_Type f acc +=
  | DeclExt x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclExt {x with tyIdent = tyIdent})
end

---------------
-- CONSTANTS --
---------------

lang UnsafeCoerceAst = ConstAst
  syn Const +=
  | CUnsafeCoerce {}
end

lang IntAst = ConstAst
  syn Const +=
  | CInt {val : Int}
end

lang ArithIntAst = ConstAst + IntAst
  syn Const +=
  | CAddi {}
  | CSubi {}
  | CMuli {}
  | CDivi {}
  | CNegi {}
  | CModi {}
end

lang ShiftIntAst = ConstAst + IntAst
  syn Const +=
  | CSlli {}
  | CSrli {}
  | CSrai {}
end

lang FloatAst = ConstAst
  syn Const +=
  | CFloat {val : Float}
end

lang ArithFloatAst = ConstAst + FloatAst
  syn Const +=
  | CAddf {}
  | CSubf {}
  | CMulf {}
  | CDivf {}
  | CNegf {}
end

lang FloatIntConversionAst = IntAst + FloatAst
  syn Const +=
  | CFloorfi {}
  | CCeilfi {}
  | CRoundfi {}
  | CInt2float {}
end

lang BoolAst = ConstAst
  syn Const +=
  | CBool {val : Bool}
end

lang CmpIntAst = IntAst + BoolAst
  syn Const +=
  | CEqi {}
  | CNeqi {}
  | CLti {}
  | CGti {}
  | CLeqi {}
  | CGeqi {}
end

lang CmpFloatAst = FloatAst + BoolAst
  syn Const +=
  | CEqf {}
  | CLtf {}
  | CLeqf {}
  | CGtf {}
  | CGeqf {}
  | CNeqf {}
end

lang CharAst = ConstAst
  syn Const +=
  | CChar {val : Char}
end

lang CmpCharAst = CharAst + BoolAst
  syn Const +=
  | CEqc {}
end

lang IntCharConversionAst = IntAst + CharAst
  syn Const +=
  | CInt2Char {}
  | CChar2Int {}
end

lang FloatStringConversionAst = SeqAst + FloatAst
  syn Const +=
  | CStringIsFloat {}
  | CString2float {}
  | CFloat2string {}
end

lang SymbAst = ConstAst
  syn Const +=
  | CSymb {val : Symbol}
  | CGensym {}
  | CSym2hash {}
end

lang CmpSymbAst = SymbAst + BoolAst
  syn Const +=
  | CEqsym {}
end

lang SeqOpAst = SeqAst + ConstAst
  syn Const +=
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
  | CCreateList {}
  | CCreateRope {}
  | CIsList {}
  | CIsRope {}
  | CSplitAt {}
  | CSubsequence {}
end

lang FileOpAst = ConstAst
  syn Const +=
  | CFileRead {}
  | CFileWrite {}
  | CFileExists {}
  | CFileDelete {}
end

lang IOAst = ConstAst
  syn Const +=
  | CPrint {}
  | CPrintError {}
  | CDPrint {}
  | CFlushStdout {}
  | CFlushStderr {}
  | CReadLine {}
  | CReadBytesAsString {}
end

lang RandomNumberGeneratorAst = ConstAst
  syn Const +=
  | CRandIntU {}
  | CRandSetSeed {}
end

lang SysAst = ConstAst
  syn Const +=
  | CExit {}
  | CError {}
  | CArgv {}
  | CCommand {}
  | CExec {}
end

lang TimeAst = ConstAst
  syn Const +=
  | CWallTimeMs {}
  | CSleepMs {}
end

lang ConTagAst = ConstAst
  syn Const +=
  | CConstructorTag {}
end

lang RefOpAst = ConstAst
  syn Const +=
  | CRef {}
  | CModRef {}
  | CDeRef {}
end

lang TypeOpAst = ConstAst
  syn Const +=
  | CTypeOf {}
end

lang TensorOpAst = ConstAst
  syn Const +=
  | CTensorCreateUninitInt {}
  | CTensorCreateUninitFloat {}
  | CTensorCreateInt {}
  | CTensorCreateFloat {}
  | CTensorCreate {}
  | CTensorGetExn {}
  | CTensorSetExn {}
  | CTensorLinearGetExn {}
  | CTensorLinearSetExn {}
  | CTensorRank {}
  | CTensorShape {}
  | CTensorReshapeExn {}
  | CTensorCopy {}
  | CTensorTransposeExn {}
  | CTensorSliceExn {}
  | CTensorSubExn {}
  | CTensorIterSlice {}
  | CTensorEq {}
  | CTensorToString {}
end

lang BootParserAst = ConstAst
  syn Const +=
  | CBootParserParseMExprString {}
  | CBootParserParseMLangString {}
  | CBootParserParseMLangFile {}
  | CBootParserParseMCoreFile {}
  | CBootParserGetId {}
  | CBootParserGetTerm {}
  | CBootParserGetTop {}
  | CBootParserGetDecl {}
  | CBootParserGetType {}
  | CBootParserGetString {}
  | CBootParserGetInt {}
  | CBootParserGetFloat {}
  | CBootParserGetListLength {}
  | CBootParserGetConst {}
  | CBootParserGetPat {}
  | CBootParserGetCopat {}
  | CBootParserGetInfo {}
end

--------------
-- PATTERNS --
--------------

type PatName
con PName : Name -> PatName
con PWildcard : () -> PatName

lang NamedPat = Ast
  syn Pat +=
  | PatNamed {ident : PatName,
              info : Info,
              ty : Type}

  sem infoPat +=
  | PatNamed r -> r.info

  sem withInfoPat info +=
  | PatNamed r -> PatNamed {r with info = info}

  sem tyPat +=
  | PatNamed r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatNamed r -> PatNamed {r with ty = ty}
end

lang SeqTotPat = Ast
  syn Pat +=
  | PatSeqTot {pats : [Pat],
               info : Info,
               ty : Type}

  sem infoPat +=
  | PatSeqTot r -> r.info

  sem withInfoPat info +=
  | PatSeqTot r -> PatSeqTot {r with info = info}

  sem tyPat +=
  | PatSeqTot r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatSeqTot r -> PatSeqTot {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatSeqTot r ->
    match mapAccumL f acc r.pats with (acc, pats) then
      (acc, PatSeqTot {r with pats = pats})
    else never
end

lang SeqEdgePat = Ast
  syn Pat +=
  | PatSeqEdge {prefix : [Pat],
                middle: PatName,
                postfix : [Pat],
                info: Info,
                ty: Type}

  sem infoPat +=
  | PatSeqEdge r -> r.info

  sem withInfoPat info +=
  | PatSeqEdge r -> PatSeqEdge {r with info = info}

  sem tyPat +=
  | PatSeqEdge r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatSeqEdge r -> PatSeqEdge {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatSeqEdge p ->
    match mapAccumL f acc p.prefix with (acc, prefix) then
      match mapAccumL f acc p.postfix with (acc, postfix) then
        (acc, PatSeqEdge {{p with prefix = prefix} with postfix = postfix})
      else never
    else never
end

lang RecordPat = Ast
  syn Pat +=
  | PatRecord {bindings : Map SID Pat,
               info: Info,
               ty: Type}

  sem infoPat +=
  | PatRecord r -> r.info

  sem withInfoPat info +=
  | PatRecord r -> PatRecord {r with info = info}

  sem tyPat +=
  | PatRecord r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatRecord r -> PatRecord {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatRecord p ->
    match mapMapAccum (lam acc. lam. lam p. f acc p) acc p.bindings with (acc, bindings) then
      (acc, PatRecord {p with bindings = bindings})
    else never
end

lang DataPat = Ast + DataAst
  syn Pat +=
  | PatCon {ident : Name,
            subpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat +=
  | PatCon r -> r.info

  sem withInfoPat info +=
  | PatCon r -> PatCon {r with info = info}

  sem tyPat +=
  | PatCon r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatCon r -> PatCon {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatCon c ->
    match f acc c.subpat with (acc, subpat) then
      (acc, PatCon {c with subpat = subpat})
    else never
end

lang IntPat = Ast + IntAst
  syn Pat +=
  | PatInt {val : Int,
            info : Info,
            ty : Type}

  sem infoPat +=
  | PatInt r -> r.info

  sem withInfoPat info +=
  | PatInt r -> PatInt {r with info = info}

  sem tyPat +=
  | PatInt r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatInt r -> PatInt {r with ty = ty}
end

lang CharPat = Ast
  syn Pat +=
  | PatChar {val : Char,
             info : Info,
             ty : Type}

  sem infoPat +=
  | PatChar r -> r.info

  sem withInfoPat info +=
  | PatChar r -> PatChar {r with info = info}

  sem tyPat +=
  | PatChar r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatChar r -> PatChar {r with ty = ty}
end

lang BoolPat = Ast + BoolAst
  syn Pat +=
  | PatBool {val : Bool,
             info : Info,
             ty : Type}

  sem infoPat +=
  | PatBool r -> r.info

  sem withInfoPat info +=
  | PatBool r -> PatBool {r with info = info}

  sem tyPat +=
  | PatBool r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatBool r -> PatBool {r with ty = ty}
end

lang AndPat = Ast
  syn Pat +=
  | PatAnd {lpat : Pat,
            rpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat +=
  | PatAnd r -> r.info

  sem withInfoPat info +=
  | PatAnd r -> PatAnd {r with info = info}

  sem tyPat +=
  | PatAnd r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatAnd r -> PatAnd {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatAnd p ->
    match f acc p.lpat with (acc, lpat) then
      match f acc p.rpat with (acc, rpat) then
        (acc, PatAnd {{p with lpat = lpat} with rpat = rpat})
      else never
    else never
end

lang OrPat = Ast
  syn Pat +=
  | PatOr {lpat : Pat,
           rpat : Pat,
           info : Info,
           ty : Type}

  sem infoPat +=
  | PatOr r -> r.info

  sem withInfoPat info +=
  | PatOr r -> PatOr {r with info = info}

  sem tyPat +=
  | PatOr r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatOr r -> PatOr {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatOr p ->
    match f acc p.lpat with (acc, lpat) then
      match f acc p.rpat with (acc, rpat) then
        (acc, PatOr {{p with lpat = lpat} with rpat = rpat})
      else never
    else never
end

lang NotPat = Ast
  syn Pat +=
  | PatNot {subpat : Pat,
            info : Info,
            ty : Type}

  sem infoPat +=
  | PatNot r -> r.info

  sem withInfoPat info +=
  | PatNot r -> PatNot {r with info = info}

  sem tyPat +=
  | PatNot r -> r.ty

  sem withTypePat (ty : Type) +=
  | PatNot r -> PatNot {r with ty = ty}

  sem smapAccumL_Pat_Pat f acc +=
  | PatNot p ->
    match f acc p.subpat with (acc, subpat) then
      (acc, PatNot {p with subpat = subpat})
    else never
end

-----------
-- TYPES --
-----------

lang UnknownTypeAst = Ast
  syn Type +=
  | TyUnknown {info : Info}

  sem tyWithInfo info +=
  | TyUnknown t -> TyUnknown {t with info = info}

  sem infoTy +=
  | TyUnknown r -> r.info

  sem sremoveUnknown =
  | TyUnknown _ -> None ()
  | ty -> Some ty
end

lang BoolTypeAst = Ast
  syn Type +=
  | TyBool {info  : Info}

  sem tyWithInfo info +=
  | TyBool t -> TyBool {t with info = info}

  sem infoTy +=
  | TyBool r -> r.info
end

lang IntTypeAst = Ast
  syn Type +=
  | TyInt {info : Info}

  sem tyWithInfo info +=
  | TyInt t -> TyInt {t with info = info}

  sem infoTy +=
  | TyInt r -> r.info
end

lang FloatTypeAst = Ast
  syn Type +=
  | TyFloat {info : Info}

  sem tyWithInfo info +=
  | TyFloat t -> TyFloat {t with info = info}

  sem infoTy +=
  | TyFloat r -> r.info
end

lang CharTypeAst = Ast
  syn Type +=
  | TyChar {info  : Info}

  sem tyWithInfo info +=
  | TyChar t -> TyChar {t with info = info}

  sem infoTy +=
  | TyChar r -> r.info
end

lang FunTypeAst = Ast
  syn Type +=
  | TyArrow {info : Info,
             from : Type,
             to   : Type}

  sem tyWithInfo info +=
  | TyArrow t -> TyArrow {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyArrow t ->
    match f acc t.from with (acc, from) then
      match f acc t.to with (acc, to) then
        (acc, TyArrow {{t with from = from} with to = to})
      else never
    else never

  sem infoTy +=
  | TyArrow r -> r.info
end

lang SeqTypeAst = Ast
  syn Type +=
  | TySeq {info : Info,
           ty   : Type}

  sem tyWithInfo info +=
  | TySeq t -> TySeq {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TySeq t ->
    match f acc t.ty with (acc, ty) then
      (acc, TySeq {t with ty = ty})
    else never

  sem infoTy +=
  | TySeq r -> r.info
end

lang TensorTypeAst = Ast
  syn Type +=
  | TyTensor {info : Info,
              ty   : Type}

  sem tyWithInfo info +=
  | TyTensor t -> TyTensor {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyTensor t ->
    match f acc t.ty with (acc, ty) then
      (acc, TyTensor {t with ty = ty})
    else never

  sem infoTy +=
  | TyTensor r -> r.info
end

lang RecordTypeAst = Ast
  syn Type +=
  | TyRecord {info   : Info,
              fields : Map SID Type}

  sem tyWithInfo info +=
  | TyRecord t -> TyRecord {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.fields with (acc, fields) then
      (acc, TyRecord {t with fields = fields})
    else never

  sem infoTy +=
  | TyRecord r -> r.info
end

lang VariantTypeAst = Ast
  syn Type +=
  | TyVariant {info     : Info,
               constrs  : Map Name Type}

  sem tyWithInfo info +=
  | TyVariant t -> TyVariant {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyVariant t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.constrs with (acc, constrs) then
      (acc, TyVariant {t with constrs = constrs})
    else never

  sem infoTy +=
  | TyVariant r -> r.info
end

lang ConTypeAst = Ast
  syn Type +=
  | TyCon {info   : Info,
           ident  : Name,
           data   : Type}

  sem tyWithInfo info +=
  | TyCon t -> TyCon {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyCon t ->
    match f acc t.data with (acc, data) in
    (acc, TyCon {t with data = data})

  sem infoTy +=
  | TyCon r -> r.info
end

lang DataTypeAst = Ast
  type DataRec =
    {info     : Info,
     universe : Map Name (Set Name),
     positive : Bool,
     cons     : Set Name}

  syn Type +=
  | TyData DataRec

  sem tyWithInfo info +=
  | TyData t -> TyData {t with info = info}

  sem infoTy +=
  | TyData r -> r.info

  sem computeData : DataRec -> Map Name (Set Name)
  sem computeData =
  | r ->
    if r.positive then
      mapMap (setIntersect r.cons) r.universe
    else
      mapMap (lam x. setSubtract x r.cons) r.universe
end


lang VarTypeAst = Ast
  syn Type +=
  -- Rigid type variable
  | TyVar  {info     : Info,
            ident    : Name}

  sem tyWithInfo info +=
  | TyVar t -> TyVar {t with info = info}

  sem infoTy +=
  | TyVar t -> t.info
end

lang AllTypeAst = Ast
  syn Type +=
  | TyAll {info  : Info,
           ident : Name,
           kind  : Kind,
           ty    : Type}

  sem tyWithInfo info +=
  | TyAll t -> TyAll {t with info = info}

  sem infoTy +=
  | TyAll t -> t.info

  sem smapAccumL_Type_Type f acc +=
  | TyAll t ->
    match smapAccumL_Kind_Type f acc t.kind with (acc, kind) in
    match f acc t.ty with (acc, ty) in
    (acc, TyAll {t with kind = kind,
                        ty = ty})

  sem inspectType +=
  | TyAll t -> inspectType t.ty

  sem stripTyAll =
  | ty -> stripTyAllBase [] ty

  sem stripTyAllBase (vars : [(Name, Kind)]) =
  | TyAll t -> stripTyAllBase (snoc vars (t.ident, t.kind)) t.ty
  | ty -> rappAccumL_Type_Type stripTyAllBase vars ty
end

lang AppTypeAst = Ast
  syn Type +=
  | TyApp {info : Info,
           lhs  : Type,
           rhs  : Type}

  sem tyWithInfo info +=
  | TyApp t -> TyApp {t with info = info}

  sem smapAccumL_Type_Type f acc +=
  | TyApp t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, TyApp {{t with lhs = lhs} with rhs = rhs})
      else never
    else never

  sem infoTy +=
  | TyApp r -> r.info
end

lang AliasTypeAst = AllTypeAst
  syn Type +=
  -- An aliased type, treated as content but printed as display.
  | TyAlias {display : Type,
             content : Type}

  sem tyWithInfo info +=
  | TyAlias t -> TyAlias {t with display = tyWithInfo info t.display}

  sem infoTy +=
  | TyAlias t -> infoTy t.display

  sem smapAccumL_Type_Type f acc +=
  | TyAlias t ->
    match f acc t.content with (acc, content) in
    match f acc t.display with (acc, display) in
    (acc, TyAlias {t with content = content, display = display})

  sem rappAccumL_Type_Type f acc +=
  | TyAlias t -> f acc t.content

  sem stripTyAll +=
  | TyAlias t & ty ->
    switch stripTyAll t.content
    case ([], _) then ([], ty)
    case stripped then stripped
    end
end

lang PolyKindAst = Ast
  syn Kind +=
  | Poly ()
end

lang MonoKindAst = Ast
  syn Kind +=
  | Mono ()
end

lang RecordKindAst = Ast
  syn Kind +=
  | Record {fields : Map SID Type}

  sem smapAccumL_Kind_Type f acc +=
  | Record r ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc r.fields with (acc, flds) in
    (acc, Record {r with fields = flds})
end

lang DataKindAst = Ast
  syn Kind +=
  | Data { types : Map Name { lower : Set Name, upper : Option (Set Name) } }
end


------------------------
-- MEXPR AST FRAGMENT --
------------------------

lang MExprAst =

  -- Terms
  VarAst + AppAst + LamAst + RecordAst + ConstAst + DataAst + MatchAst +
  SeqAst + NeverAst + PlaceholderAst + OpaqueAst +

  -- Decls
  LetDeclAst + TypeDeclAst + RecLetsDeclAst + DataDeclAst + UtestDeclAst +
  ExtDeclAst +

  -- Constants
  IntAst + ArithIntAst + ShiftIntAst + FloatAst + ArithFloatAst + BoolAst +
  CmpIntAst + IntCharConversionAst + CmpFloatAst + CharAst + CmpCharAst +
  SymbAst + CmpSymbAst + SeqOpAst + FileOpAst + IOAst +
  RandomNumberGeneratorAst + SysAst + FloatIntConversionAst +
  FloatStringConversionAst + TimeAst + ConTagAst + RefOpAst + TensorOpAst +
  BootParserAst + UnsafeCoerceAst + TypeOpAst +

  -- Patterns
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat + IntPat + CharPat +
  BoolPat + AndPat + OrPat + NotPat +

  -- Types
  UnknownTypeAst + BoolTypeAst + IntTypeAst + FloatTypeAst + CharTypeAst +
  FunTypeAst + SeqTypeAst + RecordTypeAst + VariantTypeAst + ConTypeAst +
  DataTypeAst + VarTypeAst + AppTypeAst + TensorTypeAst + AllTypeAst +
  AliasTypeAst +

  -- Kinds
  PolyKindAst + MonoKindAst + RecordKindAst + DataKindAst
end
