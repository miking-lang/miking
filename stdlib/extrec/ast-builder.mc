include "ast.mc"

include "mlang/ast-builder.mc"

let ext_record_ = lam s. lam b.
  use ExtRecordAst in 
  TmExtRecord {bindings = mapFromSeq cmpString b,
               ident = nameNoSym s,
               ty = tyunknown_,
               info = NoInfo ()}

let ext_proj_ = lam s. lam lhs. lam l. 
  use ExtRecordAst in 
  TmExtProject {e = lhs, 
                label = l,
                ident = nameNoSym s,
                ty = tyunknown_,
                info = NoInfo ()}

-- todo implement this
recursive let extrec_bindF_ = use MLangAst in
  lam f : Expr -> Expr -> Expr. lam letexpr. lam expr.
  bindF_ (lam letexpr. lam expr.
    match letexpr with TmUse t then
      TmUse {t with inexpr = extrec_bindF_ f t.inexpr expr}
    else
      f letexpr expr -- Insert at the end of the chain
  ) letexpr expr
end

let placeholder_ = use PlaceholderAst in 
  TmPlaceholder {info = NoInfo (), 
                 ty = tyunknown_}