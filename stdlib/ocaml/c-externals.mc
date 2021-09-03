include "ocaml/ast.mc"

lang OCamlCExternals = MExprAst + OCamlAst
  sem insertExternalCDeclarations (externals : Map Name (Name, Type)) =
  | ast /- : Expr -/ ->
    mapFoldWithKey
      (lam acc : Expr. lam k : Name. lam v : (Name, Type).
        OTmCExternalDecl {ident = k, ty = v.1, cIdent = nameGetStr v.0,
                          inexpr = acc})
      ast
      externals
end
