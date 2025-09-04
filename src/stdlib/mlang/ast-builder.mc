-- Helper functions for creating MLang AST nodes.
-- Functions for types are defined in ast.mc

include "mexpr/ast-builder.mc"
include "ast.mc"

include "extrec/ast.mc"


-- Extending the bind function for mlang expressions

let base_kind_ = BaseKind ()
let sumext_kind_ = SumExtKind ()


-- Extended expressions --

let nuse_ = use UseDeclAst in
  lam n.
  DeclUse {ident = n, info = NoInfo {}}

let use_ =
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
  lam isBase. lam n. lam ndefs: [(Name, Type)].
  DeclSyn {ident = n,
           defs = map (lam t. {ident = t.0, tyIdent = t.1, tyName = nameNoSym (concat (nameGetStr t.0) "Type")}) ndefs,
           params = [],
           includes = [],
           info = NoInfo {},
           declKind = if isBase then base_kind_ else sumext_kind_}

let decl_nsyn_ = use MLangAst in
  lam isBase. lam n. lam defs: [(String, Type)].
  decl_nsynn_ isBase n (map (lam t. (nameNoSym t.0, t.1)) defs)

let decl_synn_ = use MLangAst in
  lam isBase. lam s. lam ndefs: [(Name, Type)].
  decl_nsynn_ isBase (nameNoSym s) ndefs

let decl_syn_ = use MLangAst in
  lam s. lam defs: [(String, Type)].
  decl_nsyn_ true (nameNoSym s) defs

let decl_syn_ext_ = use MLangAst in
  lam s. lam defs: [(String, Type)].
  decl_nsyn_ false (nameNoSym s) defs

let decl_syn_params_ = use MLangAst in
  lam s : String. lam ss : [String]. lam defs : [(String, Type)].
  DeclSyn {ident = nameNoSym s,
           defs = map (lam t. {ident = nameNoSym t.0,
                               tyIdent = t.1,
                               tyName = nameNoSym (concat s "Type")}) defs,
           params = map nameNoSym ss,
           includes = [],
           info = NoInfo {},
           declKind = base_kind_}

let decl_nsemty_ = use MLangAst in
  lam n. lam ty.
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_, includes = [],
           args = None (), cases = [], info = NoInfo {},
           declKind = base_kind_}

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
           info = NoInfo {},
           declKind = base_kind_}

let decl_sem_args_ty_cases_ = use MLangAst in
  lam s : String. lam args : [(String, Type)]. lam ty : Type. lam cases.
  let n = nameNoSym s in
  DeclSem {ident = n, tyAnnot = ty,
           tyBody = tyunknown_, includes = [],
           args = Some (map (lam t. {ident = nameNoSym t.0, tyAnnot = t.1}) args),
           cases = map (lam t. {pat = t.0, thn = t.1}) cases,
           info = NoInfo {},
           declKind = base_kind_}

let decl_nsem_ = use MLangAst in
  lam isBase. lam n. lam nargs: [(Name, Type)]. lam cases: [(Pat, Expr)].
  DeclSem {ident = n, tyAnnot = tyunknown_,
           tyBody = tyunknown_, includes = [],
           args = Some (map (lam t. {ident = t.0, tyAnnot = t.1}) nargs),
           cases = map (lam t. {pat = t.0, thn = t.1}) cases,
           info = NoInfo {},
           declKind = if isBase then base_kind_ else sumext_kind_}

let decl_nusem_ = use MLangAst in
  lam n. lam nuargs: [Name]. lam cases.
  decl_nsem_ true n (map (lam x. (x, tyunknown_)) nuargs) cases

let decl_sem_ = use MLangAst in
  lam s. lam args: [(String, Type)]. lam cases.
  decl_nsem_ true (nameNoSym s) (map (lam t. (nameNoSym t.0, t.1)) args) cases

let decl_sem_ext_ = use MLangAst in
  lam s. lam args: [(String, Type)]. lam cases.
  decl_nsem_ false (nameNoSym s) (map (lam t. (nameNoSym t.0, t.1)) args) cases

let decl_usem_ = use MLangAst in
  lam s. lam uargs: [String]. lam cases.
  decl_nusem_ (nameNoSym s) (map nameNoSym uargs) cases


let decl_include_ = use MLangAst in
  lam p.
  DeclInclude {path = p, info = NoInfo {}}
