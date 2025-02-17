include "mexpr/ast.mc"
include "ocaml/ast.mc"
include "pmexpr/extract.mc"

lang PMExprCExternals = MExprAst + OCamlAst + PMExprExtractAccelerate
  sem getExternalCDeclarations =
  | accelerated /- : Map Name AcceleratedData -> [Top] -/ ->
    mapValues
      (mapMapWithKey
        (lam k : Name. lam v : AccelerateData.
          let ty =
            foldr
              (lam param : (Name, Type). lam acc : Type.
                TyArrow {from = param.1, to = acc, info = infoTy acc})
              v.returnType v.params in
          OTopCExternalDecl {
            ident = k, ty = ty, bytecodeIdent = v.bytecodeWrapperId,
            nativeIdent = k})
        accelerated)
end
