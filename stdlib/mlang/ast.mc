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
             defs : [{ident : Name, tyIdent : Type}],
             -- The list of syns whose constructors should be included.
             -- The first string identifies the langauge of the include
             -- and the second string identifies the name.
             includes : [(String, String)],
             info : Info}

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
  syn Decl =
  | DeclSem {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             args : Option [{ident : Name, tyAnnot : Type}],
             cases : [{pat : Pat, thn : Expr}],
             -- The list of semantic function s whose cases should be included.
             -- The first string identifies the langauge of the include
             -- and the second string identifies the name.
             includes : [(String, String)],
             info : Info}

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
    (acc, DeclUtest {x with test = test, expected = expected, tusing = tusing})
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
end


lang MLangAst =

  -- Top level program
  MLangTopLevel

  -- Additional expressions
  + UseAst

  -- Declarations
  + LangDeclAst + SynDeclAst + SemDeclAst + LetDeclAst + TypeDeclAst
  + RecLetsDeclAst + DataDeclAst + UtestDeclAst + ExtDeclAst + IncludeDeclAst
  + TyUseAst + SynProdExtDeclAst

end
