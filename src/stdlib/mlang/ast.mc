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

-- DeclUse --
lang UseDeclAst = Ast
  syn Decl =
  | DeclUse {ident : Name, info : Info}

  sem infoDecl =
  | DeclUse t -> t.info

  sem declWithInfo (info : Info) =
  | DeclUse t -> DeclUse {t with info = info}
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

-- DeclLang --
lang LangDeclAst = DeclAst
  syn Decl =
  | DeclLang {ident : Name,
              includes : [(Name, Info)],
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
  syn SynDeclKind =
  | SynBase
  | SynSum {base : Name}
  -- | SynProd {base : Name, globalExt : Map SID Type}

  syn Decl =
  | DeclSyn {ident : Name,
             params : [Name],
             defs : [{ident : Name, tyIdent : Type, info : Info}],
             info : Info,
             kind : SynDeclKind}

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

-- DeclSem --
lang SemDeclAst = DeclAst
  syn SemDeclKind =
  | SemBase
  | SemSum {base : Name}
  syn Decl =
  | DeclSem
    { ident : Name
    , tyAnnot : Type
    , tyBody : Type
    , impl : Option
      { params : [{ident : Name, tyAnnot : Type, tyParam : Type, info : Info}]
      , cases : [{pat : Pat, body : Expr, info : Info}]
      }
    , info : Info
    , kind : SemDeclKind
    }

  sem infoDecl =
  | DeclSem d -> d.info

  sem declWithInfo info =
  | DeclSem d -> DeclSem {d with info = info}

  sem smapAccumL_Decl_Type f acc =
  | DeclSem x ->
    let fparam = lam acc. lam def.
      match f acc def.tyAnnot with (acc, tyAnnot) in
      (acc, {def with tyAnnot = tyAnnot}) in
    let fimpl = lam acc. lam impl.
      match mapAccumL fparam acc impl.params with (acc, params) in
      (acc, {impl with params = params}) in
    match f acc x.tyAnnot with (acc, tyAnnot) in
    match f acc x.tyBody with (acc, tyBody) in
    match optionMapAccum fimpl acc x.impl with (acc, impl) in
    (acc, DeclSem {x with impl = impl, tyAnnot = tyAnnot, tyBody = tyBody})

  sem smapAccumL_Decl_Expr f acc =
  | DeclSem x ->
    let fcase = lam acc. lam c.
      match f acc c.body with (acc, body) in
      (acc, {c with body = body}) in
    let fimpl = lam acc. lam impl.
      match mapAccumL fcase acc impl.cases with (acc, cases) in
      (acc, {impl with cases = cases}) in
    match optionMapAccum fimpl acc x.impl with (acc, impl) in
    (acc, DeclSem {x with impl = impl})

  sem smapAccumL_Decl_Pat f acc =
  | DeclSem x ->
    let fcase = lam acc. lam c.
      match f acc c.pat with (acc, pat) in
      (acc, {c with pat = pat}) in
    match mapAccumL fcase acc x.cases with (acc, cases) in
    (acc, DeclSem {x with cases = cases})
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

  -- Declarations
  + LangDeclAst + SynDeclAst + SemDeclAst + LetDeclAst + TypeDeclAst
  + RecLetsDeclAst + DataDeclAst + UtestDeclAst + ExtDeclAst + IncludeDeclAst
  + UseDeclAst + TyUseAst
end
