include "ast.mc"

include "mlang/ast-builder.mc"

let ext_record_ = lam s. lam b.
  use ExtRecordAst in
  TmExtRecord {bindings = mapFromSeq cmpString b,
               ident = nameNoSym s,
               ty = tyunknown_,
               info = NoInfo ()}

let placeholder_ = use PlaceholderAst in
  TmPlaceholder {info = NoInfo (),
                 ty = tyunknown_}

let decl_ncosyn_ = use ExtRecAst in
  lam n : Name. lam params : [Name]. lam isBase : Bool. lam ty : Type.
    DeclCosyn {ident = n,
               params = params,
               isBase = isBase,
               ty = ty,
               info = NoInfo (),
               includes = []}

let decl_cosyn_ = lam s. lam sparams.
  decl_ncosyn_ (nameNoSym s) (map nameNoSym sparams)


let decl_ncosem_ = use ExtRecAst in
  lam n : Name. lam nargs : [(Name, Type)]. lam cases: [(Copat, Expr)]. lam isBase : Bool.
  DeclCosem {ident = n,
             info = NoInfo (),
             args = map (lam tupl. {ident = tupl.0, tyAnnot = tupl.1}) nargs,
             cases = cases,
             isBase = isBase,
             tyAnnot = tyunknown_,
             targetTyIdent = nameNoSym "",
             includes = []}

let decl_cosem_ = use ExtRecAst in
  lam s : String. lam args : [(String, Type)]. lam cases: [(Copat, Expr)]. lam isBase : Bool.
  decl_ncosem_ (nameNoSym s) (map (lam tupl. (nameNoSym tupl.0, tupl.1)) args) cases isBase

let record_copat_ = use RecordCopatAst in
  lam fields : [String].
    RecordCopat {info = NoInfo (), fields = fields}

let decl_syn_prodext_ = use ExtRecAst in
  lam s. lam globExt : Option Type. lam indivExts : [(String, Type)].
  let parseExt = lam indivExt.
    {ident = nameNoSym indivExt.0,
     tyIdent = indivExt.1,
     tyName = nameNoSym (concat indivExt.0 "Type")} in
  SynDeclProdExt {ident = nameNoSym s,
                  params = [],
                  includes = [],
                  globalExt = globExt,
                  individualExts = map parseExt indivExts,
                  info = NoInfo ()}
