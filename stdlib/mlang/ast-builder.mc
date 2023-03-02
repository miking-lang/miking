-- Helper functions for creating MLang AST nodes.
-- Functions for types are defined in ast.mc

include "mexpr/ast-builder.mc"
include "./ast.mc"


-- Extending the bind function for mlang expressions

recursive let mlang_bindF_ = use MLangAst in
  lam f : Expr -> Expr -> Expr. lam letexpr. lam expr.
  bindF_ (lam letexpr. lam expr.
    match letexpr with TmUse t then
      TmUse {t with inexpr = mlang_bindF_ f t.inexpr expr}
    else match letexpr with TmInclude t then
      TmInclude {t with inexpr = mlang_bindF_ f t.inexpr expr}
    else
      f letexpr expr -- Insert at the end of the chain
  ) letexpr expr
end

let bind_ = mlang_bindF_ (lam. lam expr. expr)

let bindall_ = use MLangAst in
  lam exprs.
  foldr1 bind_ exprs


-- Extended expressions --

let nuse_ = use UseAst in
  lam n.
  TmUse {ident = n, inexpr = uunit_, ty = tyunknown_, info = NoInfo {}}

let use_ = use UseAst in
  lam s.
  nuse_ (nameNoSym s)

let include_ = use IncludeAst in
  lam p.
  TmInclude {path = p, inexpr = uunit_, ty = tyunknown_, info = NoInfo {}}


-- Declarations --

let decl_nlangin_ = use MLangAst in
  lam n. lam nincls. lam decls.
  DeclLang {ident = n,
            includes = nincls,
            decls = decls,
            info = NoInfo {}}

let decl_nlangi_ = use MLangAst in
  lam n. lam incls. lam decls.
  decl_nlangin_ n (map nameNoSym incls) decls

let decl_langin_ = use MLangAst in
  lam s. lam nincls. lam decls.
  decl_nlangin_ (nameNoSym s) nincls decls

let decl_langi_ = use MLangAst in
  lam s. lam incls. lam decls.
  decl_nlangin_ (nameNoSym s) (map nameNoSym incls) decls

let decl_nlang_ = use MLangAst in
  lam n. lam decls.
  decl_nlangin_ n [] decls

let decl_lang_ = use MLangAst in
  lam s. lam decls.
  decl_nlang_ (nameNoSym s) decls


let decl_nsynn_ = use MLangAst in
  lam n. lam ndefs: [(Name, Type)].
  DeclSyn {ident = n,
           defs = map (lam t. {ident = t.0, tyIdent = t.1}) ndefs,
           info = NoInfo {}}

let decl_nsyn_ = use MLangAst in
  lam n. lam defs: [(String, Type)].
  decl_nsynn_ n (map (lam t. (nameNoSym t.0, t.1)) defs)

let decl_synn_ = use MLangAst in
  lam s. lam ndefs: [(Name, Type)].
  decl_nsynn_ (nameNoSym s) ndefs

let decl_syn_ = use MLangAst in
  lam s. lam defs: [(String, Type)].
  decl_nsyn_ (nameNoSym s) defs


let decl_nsemty_ = use MLangAst in
  lam n. lam ty.
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_,
           args = [], cases = [], info = NoInfo {}}

let decl_semty_ = use MLangAst in
  lam s. lam ty.
  decl_nsemty_ (nameNoSym s) ty

let decl_nsem_ = use MLangAst in
  lam n. lam nargs: [(Name, Type)]. lam cases: [(Pat, Expr)].
  DeclSem {ident = n, tyAnnot = tyunknown_,
           tyBody = tyunknown_,
           args = map (lam t. {ident = t.0, tyAnnot = t.1}) nargs,
           cases = map (lam t. {pat = t.0, thn = t.1}) cases,
           info = NoInfo {}}

let decl_nusem_ = use MLangAst in
  lam n. lam nuargs: [Name]. lam cases.
  decl_nsem_ n (map (lam x. (x, tyunknown_)) nuargs) cases

let decl_sem_ = use MLangAst in
  lam s. lam args: [(String, Type)]. lam cases.
  decl_nsem_ (nameNoSym s) (map (lam t. (nameNoSym t.0, t.1)) args) cases

let decl_usem_ = use MLangAst in
  lam s. lam uargs: [String]. lam cases.
  decl_nusem_ (nameNoSym s) (map nameNoSym uargs) cases


let decl_nlet_ = use MLangAst in
  lam n. lam ty. lam body.
  DeclLet {ident = n,
           tyAnnot = ty,
           tyBody = ty,
           body = body,
           info = NoInfo ()}

let decl_let_ = use MLangAst in
  lam s. lam ty. lam body.
  decl_nlet_ (nameNoSym s) ty body

let decl_nulet_ = use MLangAst in
  lam n. lam body.
  decl_nlet_ n tyunknown_ body

let decl_ulet_ = use MLangAst in
  lam s. lam body.
  decl_let_ s tyunknown_ body

