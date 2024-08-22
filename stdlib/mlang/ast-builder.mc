-- Helper functions for creating MLang AST nodes.
-- Functions for types are defined in ast.mc

include "mexpr/ast-builder.mc"
include "ast.mc"


-- Extending the bind function for mlang expressions

recursive let mlang_bindF_ = use MLangAst in
  lam f : Expr -> Expr -> Expr. lam letexpr. lam expr.
  bindF_ (lam letexpr. lam expr.
    match letexpr with TmUse t then
      TmUse {t with inexpr = mlang_bindF_ f t.inexpr expr}
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

--  Extended types --
let ntyuse_ = use TyUseAst in 
  lam n : Name. lam inty : Type. 
  TyUse {ident = n,
         info = NoInfo {},
         inty = inty}

let tyuse_ = use TyUseAst in 
  lam s : String. lam inty : Type. 
  TyUse {ident = nameNoSym s,
         info = NoInfo {},
         inty = inty}


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
           params = [],
           includes = [],
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

let decl_syn_params_ = use MLangAst in 
  lam s : String. lam ss : [String]. lam defs : [(String, Type)].
  DeclSyn {ident = nameNoSym s,
           defs = map (lam t. {ident = nameNoSym t.0, tyIdent = t.1}) defs,
           params = map nameNoSym ss,
           includes = [],
           info = NoInfo {}}

let decl_nsemty_ = use MLangAst in
  lam n. lam ty.
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_, includes = [],
           args = None (), cases = [], info = NoInfo {}}

let decl_semty_ = use MLangAst in
  lam s. lam ty.
  decl_nsemty_ (nameNoSym s) ty

let decl_semty_cases_ = use MLangAst in 
  lam s. lam ty. lam cases.
  let n = nameNoSym s in 
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_, includes = [],
           args = Some [],
           cases = map (lam t. {pat = t.0, thn = t.1}) cases,
           info = NoInfo {}}

let decl_sem_args_ty_cases_ = use MLangAst in 
  lam s : String. lam args : [(String, Type)]. lam ty : Type. lam cases.
  let n = nameNoSym s in 
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_, includes = [],
           args = Some (map (lam t. {ident = nameNoSym t.0, tyAnnot = t.1}) args),
           cases = map (lam t. {pat = t.0, thn = t.1}) cases,
           info = NoInfo {}}

let decl_nsem_ = use MLangAst in
  lam n. lam nargs: [(Name, Type)]. lam cases: [(Pat, Expr)].
  DeclSem {ident = n, tyAnnot = tyunknown_,
           tyBody = tyunknown_, includes = [],
           args = Some (map (lam t. {ident = t.0, tyAnnot = t.1}) nargs),
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


let decl_ntype_ = use MLangAst in
  lam n. lam params. lam ty.
  DeclType {ident = n,
            params = params,
            tyIdent = ty,
            info = NoInfo ()}

let decl_type_ = use MLangAst in
  lam s. lam params. lam ty.
  decl_ntype_ (nameNoSym s) (map nameNoSym params) ty


let decl_nreclets_ = use MLangAst in
  lam bs: [(Name, Type, Expr)].
  let bindings = map (lam b.
    {ident = b.0, tyAnnot = b.1, tyBody = b.1,
     body = b.2, info = NoInfo ()}
  ) bs in
  DeclRecLets {bindings = bindings, info = NoInfo ()}

let decl_reclets_ = use MLangAst in
  lam bs: [(String, Type, Expr)].
  decl_nreclets_ (map (lam b. (nameNoSym b.0, b.1, b.2)) bs)

let decl_nureclets_ = use MLangAst in
  lam bs: [(Name, Expr)].
  decl_nreclets_ (map (lam b. (b.0, tyunknown_, b.1)) bs)

let decl_ureclets_ = use MLangAst in
  lam bs: [(String, Expr)].
  decl_reclets_ (map (lam b. (b.0, tyunknown_, b.1)) bs)

let decl_reclet_ = use MLangAst in
  lam s. lam ty. lam body.
  decl_reclets_ [(s, ty, body)]

let decl_ureclet_ = use MLangAst in
  lam s. lam body.
  decl_ureclets_ [(s, body)]


let decl_ncondef_ = use MLangAst in
  lam n. lam ty.
  DeclConDef {ident = n, tyIdent = ty, info = NoInfo ()}

let decl_condef_ = use MLangAst in
  lam s. lam ty.
  decl_ncondef_ (nameNoSym s) ty

let decl_nucondef_ = use MLangAst in
  lam n.
  decl_ncondef_ n tyunknown_

let decl_ucondef_ = use MLangAst in
  lam s.
  decl_condef_ s tyunknown_


let decl_utestuf_ = use MLangAst in
  lam t. lam e. lam u. lam f.
  DeclUtest {test = t, expected = e, tusing = Some u, tonfail = Some f, info = NoInfo ()}

let decl_utestu_ = use MLangAst in
  lam t. lam e. lam u.
  DeclUtest {test = t, expected = e, tusing = Some u, tonfail = None (), info = NoInfo ()}

let decl_utestf_ = use MLangAst in
  lam t. lam e. lam f.
  DeclUtest {test = t, expected = e, tusing = None (), tonfail = Some f, info = NoInfo ()}

let decl_utest_ = use MLangAst in
  lam t. lam e.
  DeclUtest {test = t, expected = e, tusing = None (), tonfail = None (), info = NoInfo ()}


let decl_next_ = use MLangAst in
  lam n. lam e. lam ty.
  DeclExt {ident = n, tyIdent = ty, effect = e, info = NoInfo ()}

let decl_ext_ = use MLangAst in
  lam s. lam e. lam ty.
  decl_next_ (nameNoSym s) e ty


let decl_include_ = use MLangAst in
  lam p.
  DeclInclude {path = p, info = NoInfo {}}
