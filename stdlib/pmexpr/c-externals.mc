include "mexpr/ast.mc"
include "ocaml/ast.mc"
include "pmexpr/extract.mc"

lang PMExprCExternals = MExprAst + OCamlAst
  sem insertExternalCDeclarations (accelerated : Map Name AccelerateData) =
  | ast /- : Expr -> Expr -/ ->
    mapFoldWithKey
      (lam acc : Expr. lam k : Name. lam v : AccelerateData.
        let ty =
          foldr
            (lam param : (Name, Type). lam acc : Type.
              TyArrow {from = param.1, to = acc, info = infoTy acc})
            v.returnType v.params in
        OTmCExternalDecl {
          ident = k, ty = ty, bytecodeIdent = v.bytecodeWrapperId,
          nativeIdent = k, inexpr = acc})
      ast accelerated
end
