-- Language fragments for MLang, extending those of MExpr.
--
-- The Decl syntax fragment contains the top-level declarations in an
-- MCore file such as DeclInclude, DeclUtest, DeclLang, but also
-- declarations that must be inside language fragments (DeclSyn and DeclSem).
-- As such it is possible to create invalid MCore ASTs using this fragment by,
-- for example, putting a DeclInclude or DeclUtest inside of a DeclInclude or
-- by putting a DeclSyn or DeclSem at the top-level.
--
-- This fragement also extends the MExpr Expr and Type syntax fragments
-- by adding a TmUse and TyUse respectively.
--
-- An MLang program consists of a list of Decls and the expression to be
-- evaluated.

include "map.mc"
include "name.mc"
include "seq.mc"
include "option.mc"
include "string.mc"
include "stringid.mc"

include "mexpr/ast.mc"
include "mexpr/info.mc"

type DeclKind
con BaseKind : () -> DeclKind
con SumExtKind : () -> DeclKind

-- TmUse --
lang UseAst = Ast
  syn Expr =
  | TmUse {ident : Name,
           inexpr : Expr,
           ty : Type,
           info : Info}

  sem infoTm =
  | TmUse t -> t.info

  sem tyTm =
  | TmUse t -> t.ty

  sem withInfo (info : Info) =
  | TmUse t -> TmUse {t with info = info}

  sem withType (ty : Type) =
  | TmUse t -> TmUse {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmUse t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmUse {t with inexpr = inexpr})
end

lang TyUseAst = Ast
  syn Type =
  | TyUse {ident : Name,
           info : Info,
           inty : Type}

  sem infoTy =
  | TyUse {info = info} -> info

  sem tyWithInfo info =
  | TyUse t -> TyUse {t with info = info}
end

-- Base fragment for MLang declarations --
lang DeclAst = Ast
  syn Decl = -- intentionally left blank

  sem infoDecl: Decl -> Info
  sem declWithInfo: Info -> Decl -> Decl

  sem smapAccumL_Decl_Decl : all acc. (acc -> Decl -> (acc, Decl)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Decl f acc = | d -> (acc, d)
  sem smapAccumL_Decl_Expr : all acc. (acc -> Expr -> (acc, Expr)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Expr f acc = | d -> (acc, d)
  sem smapAccumL_Decl_Type : all acc. (acc -> Type -> (acc, Type)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Type f acc = | d -> (acc, d)
  sem smapAccumL_Decl_Pat : all acc. (acc -> Pat -> (acc, Pat)) -> acc -> Decl -> (acc, Decl)
  sem smapAccumL_Decl_Pat f acc = | d -> (acc, d)

  sem smap_Decl_Decl : (Decl -> Decl) -> Decl -> Decl
  sem smap_Decl_Decl f = | d -> (smapAccumL_Decl_Decl (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Decl : all acc. (acc -> Decl -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Decl f acc = | d -> (smapAccumL_Decl_Decl (lam acc. lam a. (f acc a, a)) acc d).0

  sem smap_Decl_Expr : (Expr -> Expr) -> Decl -> Decl
  sem smap_Decl_Expr f = | d -> (smapAccumL_Decl_Expr (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Expr : all acc. (acc -> Expr -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Expr f acc = | d -> (smapAccumL_Decl_Expr (lam acc. lam a. (f acc a, a)) acc d).0

  sem smap_Decl_Type : (Type -> Type) -> Decl -> Decl
  sem smap_Decl_Type f = | d -> (smapAccumL_Decl_Type (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Type : all acc. (acc -> Type -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Type f acc = | d -> (smapAccumL_Decl_Type (lam acc. lam a. (f acc a, a)) acc d).0

  sem smap_Decl_Pat : (Pat -> Pat) -> Decl -> Decl
  sem smap_Decl_Pat f = | d -> (smapAccumL_Decl_Pat (lam. lam a. ((), f a)) () d).1

  sem sfold_Decl_Pat : all acc. (acc -> Pat -> acc) -> acc -> Decl -> acc
  sem sfold_Decl_Pat f acc = | d -> (smapAccumL_Decl_Pat (lam acc. lam a. (f acc a, a)) acc d).0
end

-- TODO(vipa, 2024-11-26): This enables working more or less as though
-- https://github.com/miking-lang/miking/issues/826 were already
-- implemented.
lang ExprAsDecl = DeclAst
  sem exprAsDecl : Expr -> Option (Decl, Expr)
  sem exprAsDecl =
  | _ -> None ()

  sem declAsExpr : Expr -> Decl -> Expr
end

-- DeclLang --
lang LangDeclAst = DeclAst
  syn Decl =
  | DeclLang {ident : Name,
              includes : [Name],
              decls : [Decl],
              info : Info}

  sem infoDecl =
  | DeclLang d -> d.info

  sem declWithInfo info =
  | DeclLang d -> DeclLang {d with info = info}

  sem smapAccumL_Decl_Decl f acc =
  | DeclLang x ->
    match mapAccumL f acc x.decls with (acc, decls) in
    (acc, DeclLang {x with decls = decls})
end

-- DeclSyn --
lang SynDeclAst = DeclAst
  syn Decl =
  | DeclSyn {ident : Name,
             params : [Name],
             defs : [{ident : Name, tyIdent : Type, tyName : Name}],
             -- The list of syns whose constructors should be included.
             -- The first string identifies the langauge of the include
             -- and the second string identifies the name.
             includes : [(String, String)],
             info : Info,
             declKind : DeclKind}

  sem infoDecl =
  | DeclSyn d -> d.info

  sem declWithInfo info =
  | DeclSyn d -> DeclSyn {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclSyn x ->
    let f = lam acc. lam def.
      match f acc def.tyIdent with (acc, tyIdent) in
      (acc, {def with tyIdent = tyIdent}) in
    match mapAccumL f acc x.defs with (acc, defs) in
    (acc, DeclSyn {x with defs = defs})
end

lang SynProdExtDeclAst = DeclAst
  syn Decl =
  | SynDeclProdExt {ident : Name,
                    extIdent : Name,
                    params : [Name],
                    globalExt : Option Type,
                    individualExts : [{ident : Name, tyIdent : Type}],
                    includes : [(String, String)],
                    info : Info}

  sem infoDecl =
  | SynDeclProdExt {info = info} -> info

  sem declWithInfo info =
  | SynDeclProdExt d -> SynDeclProdExt {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | SynDeclProdExt x ->
    let f = lam acc. lam def.
      match f acc def.tyIdent with (acc, tyIdent) in
      (acc, {def with tyIdent = tyIdent}) in
    match mapAccumL f acc x.individualExts with (acc, individualExts) in
    (acc, SynDeclProdExt {x with individualExts = individualExts})
end
-- DeclSem --
lang SemDeclAst = DeclAst
  type DeclSemType = {ident : Name,
                      tyAnnot : Type,
                      tyBody : Type,
                      args : Option [{ident : Name, tyAnnot : Type}],
                      cases : [{pat : Pat, thn : Expr}],
                      -- The list of semantic function s whose cases should be included.
                      -- The first string identifies the langauge of the include
                      -- and the second string identifies the name.
                      includes : [(String, String)],
                      info : Info,
                      declKind : DeclKind}
  syn Decl =
  | DeclSem DeclSemType

  sem infoDecl =
  | DeclSem d -> d.info

  sem declWithInfo info =
  | DeclSem d -> DeclSem {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclSem x ->
    let farg = lam acc. lam def.
      match f acc def.tyAnnot with (acc, tyAnnot) in
      (acc, {def with tyAnnot = tyAnnot}) in
    match f acc x.tyAnnot with (acc, tyAnnot) in
    match f acc x.tyBody with (acc, tyBody) in
    match optionMapAccum (mapAccumL farg) acc x.args with (acc, args) in
    (acc, DeclSem {x with args = args, tyAnnot = tyAnnot, tyBody = tyBody})

  sem smapAccumL_Decl_Expr f acc =
  | DeclSem x ->
    let fcase = lam acc. lam c.
      match f acc c.thn with (acc, thn) in
      (acc, {c with thn = thn}) in
    match mapAccumL fcase acc x.cases with (acc, cases) in
    (acc, DeclSem {x with cases = cases})

  sem smapAccumL_Decl_Pat f acc =
  | DeclSem x ->
    let fcase = lam acc. lam c.
      match f acc c.pat with (acc, pat) in
      (acc, {c with pat = pat}) in
    match mapAccumL fcase acc x.cases with (acc, cases) in
    (acc, DeclSem {x with cases = cases})
end


-- DeclLet --
lang LetDeclAst = DeclAst
  syn Decl =
  | DeclLet {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             body : Expr,
             info: Info}

  sem infoDecl =
  | DeclLet d -> d.info

  sem declWithInfo info =
  | DeclLet d -> DeclLet {d with info = info}

  sem smapAccumL_Decl_Expr f acc =
  | DeclLet x ->
    match f acc x.body with (acc, body) in
    (acc, DeclLet {x with body = body})

  sem smapAccumL_Decl_Type f acc =
  | DeclLet x ->
    match f acc x.tyAnnot with (acc, tyAnnot) in
    match f acc x.tyBody with (acc, tyBody) in
    (acc, DeclLet {x with tyAnnot = tyAnnot, tyBody = tyBody})
end

lang LetAsDecl = ExprAsDecl + LetAst + LetDeclAst
  sem exprAsDecl =
  | TmLet x -> Some
    ( DeclLet {ident = x.ident, tyAnnot = x.tyAnnot, tyBody = x.tyBody, body = x.body, info = x.info}
    , x.inexpr
    )

  sem declAsExpr inexpr =
  | DeclLet x -> TmLet
    { ident = x.ident
    , tyAnnot = x.tyAnnot
    , tyBody = x.tyBody
    , body = x.body
    , info = x.info
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- DeclType --
lang TypeDeclAst = DeclAst
  syn Decl =
  | DeclType {ident : Name,
              params : [Name],
              tyIdent : Type,
              info : Info}

  sem infoDecl =
  | DeclType d -> d.info

  sem declWithInfo info =
  | DeclType d -> DeclType {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclType x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclType {x with tyIdent = tyIdent})
end

lang TypeAsDecl = ExprAsDecl + TypeAst + TypeDeclAst
  sem exprAsDecl =
  | TmType x -> Some
    ( DeclType {ident = x.ident, params = x.params, tyIdent = x.tyIdent, info = x.info}
    , x.inexpr
    )

  sem declAsExpr inexpr =
  | DeclType x -> TmType
    { ident = x.ident
    , params = x.params
    , tyIdent = x.tyIdent
    , info = x.info
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
  end

-- DeclRecLets --
lang RecLetsDeclAst = DeclAst + RecLetsAst
  syn Decl =
  | DeclRecLets {bindings : [RecLetBinding],
                 info : Info}

  sem infoDecl =
  | DeclRecLets d -> d.info

  sem declWithInfo info =
  | DeclRecLets d -> DeclRecLets {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclRecLets x ->
    let fbinding = lam acc. lam b.
      match f acc b.tyAnnot with (acc, tyAnnot) in
      match f acc b.tyBody with (acc, tyBody) in
      (acc, {b with tyAnnot = tyAnnot, tyBody = tyBody}) in
    match mapAccumL fbinding acc x.bindings with (acc, bindings) in
    (acc, DeclRecLets {x with bindings = bindings})

  sem smapAccumL_Decl_Expr f acc =
  | DeclRecLets x ->
    let fbinding = lam acc. lam b.
      match f acc b.body with (acc, body) in
      (acc, {b with body = body}) in
    match mapAccumL fbinding acc x.bindings with (acc, bindings) in
    (acc, DeclRecLets {x with bindings = bindings})
end

lang RecLetsAsDecl = ExprAsDecl + RecLetsAst + RecLetsDeclAst
  sem exprAsDecl =
  | TmRecLets x -> Some
    ( DeclRecLets {info = x.info, bindings = x.bindings}
    , x.inexpr
    )

  sem declAsExpr inexpr =
  | DeclRecLets x -> TmRecLets
    { bindings = x.bindings
    , info = x.info
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- DeclConDef --
lang DataDeclAst = DeclAst
  syn Decl =
  | DeclConDef {ident : Name,
                tyIdent : Type,
                info : Info}

  sem infoDecl =
  | DeclConDef d -> d.info

  sem declWithInfo info =
  | DeclConDef d -> DeclConDef {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclConDef x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclConDef {x with tyIdent = tyIdent})
end

lang DataAsDecl = ExprAsDecl + DataAst + DataDeclAst
  sem exprAsDecl =
  | TmConDef x -> Some
    ( DeclConDef {ident = x.ident, tyIdent = x.tyIdent, info = x.info}
    , x.inexpr
    )

  sem declAsExpr inexpr =
  | DeclConDef x -> TmConDef
    { ident = x.ident
    , tyIdent = x.tyIdent
    , info = x.info
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- DeclUtest --
lang UtestDeclAst = DeclAst
  syn Decl =
  | DeclUtest {test : Expr,
               expected : Expr,
               tusing : Option Expr,
               tonfail : Option Expr,
               info : Info}

  sem infoDecl =
  | DeclUtest d -> d.info

  sem declWithInfo info =
  | DeclUtest d -> DeclUtest {d with info = info}

  sem smapAccumL_Decl_Expr f acc =
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

lang UtestAsDecl = ExprAsDecl + UtestAst + UtestDeclAst
  sem exprAsDecl =
  | TmUtest x -> Some
    ( DeclUtest {test = x.test, expected = x.expected, tusing = x.tusing, tonfail = x.tonfail, info = x.info}
    , x.next
    )

  sem declAsExpr inexpr =
  | DeclUtest x -> TmUtest
    { test = x.test
    , expected = x.expected
    , tusing = x.tusing
    , tonfail = x.tonfail
    , info = x.info
    , next = inexpr
    , ty = tyTm inexpr
    }
end

-- DeclExt --
lang ExtDeclAst = DeclAst
  syn Decl =
  | DeclExt {ident : Name,
             tyIdent : Type,
             effect : Bool,
             info : Info}

  sem infoDecl =
  | DeclExt d -> d.info

  sem declWithInfo info =
  | DeclExt d -> DeclExt {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclExt x ->
    match f acc x.tyIdent with (acc, tyIdent) in
    (acc, DeclExt {x with tyIdent = tyIdent})
end

lang ExtAsDecl = ExprAsDecl + ExtAst + ExtDeclAst
  sem exprAsDecl =
  | TmExt x -> Some
    ( DeclExt {ident = x.ident, tyIdent = x.tyIdent, effect = x.effect, info = x.info}
    , x.inexpr
    )

  sem declAsExpr inexpr =
  | DeclExt x -> TmExt
    { ident = x.ident
    , tyIdent = x.tyIdent
    , effect = x.effect
    , info = x.info
    , inexpr = inexpr
    , ty = tyTm inexpr
    }
end

-- DeclInclude --
lang IncludeDeclAst = DeclAst
  syn Decl =
  | DeclInclude {path : String,
                 info : Info}

  sem infoDecl =
  | DeclInclude d -> d.info

  sem declWithInfo info =
  | DeclInclude d -> DeclInclude {d with info = info}
end

lang MLangTopLevel = DeclAst
  type MLangProgram = {
    decls : [Decl],
    expr : Expr
  }

  sem countProgNodes : MLangProgram -> Int
  sem countProgNodes =
  | prog ->
    let count = foldl countDeclNodes 0 prog.decls in
    countExprNodes count prog.expr

  -- Todo: Extend to also look at patterns.
  sem countDeclNodes count =
  | decl ->
    let count = addi count 1 in
    let count = sfold_Decl_Decl countDeclNodes count decl in
    let count = sfold_Decl_Type countTypeNodes count decl in
    let count = sfold_Decl_Expr countExprNodes count decl in
    count

  sem smap_Prog_Decl : all acc. (acc -> Decl -> (acc, Decl)) -> acc -> MLangProgram -> (acc, MLangProgram)
  sem smap_Prog_Decl f acc =
  | prog ->
    match mapAccumL f acc prog.decls with (acc, decls) in
    (acc, {prog with decls = decls})
end


lang MLangAst =

  -- Top level program
  MLangTopLevel

  -- Additional expressions
  + UseAst

  -- Declarations
  + LangDeclAst + SynDeclAst + SemDeclAst + LetDeclAst + TypeDeclAst
  + RecLetsDeclAst + DataDeclAst + UtestDeclAst + ExtDeclAst + IncludeDeclAst
  + TyUseAst
end

lang MExprAsDecl
  = LetAsDecl
  + TypeAsDecl
  + RecLetsAsDecl
  + DataAsDecl
  + UtestAsDecl
  + ExtAsDecl
end
