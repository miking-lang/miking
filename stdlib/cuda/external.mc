include "cuda/ast.mc"

lang CudaDataConversion = CudaAst
end

lang CudaGenerateExternal = CudaAst
  sem convertData (info : Info) (env : GenerateEnv) (t : Expr) (ty1 : Type) =
  | ty2 -> convertDataH info env t (ty1, ty2)

  sem convertDataH (info : Info) (env : GenerateEnv) (t : Expr) =
  | (TyTensor {ty = elty1}, CTyPtr {ty = elty2}) ->
end

lang CudaGenerateExternalNaive = CudaGenerateExternal + ExtAst
  sem chooseExternalImpls (implsMap : Map String [ExternalImpl])
                          (env : GenerateEnv) =
  | TmExt {ident = ident, tyIdent = tyIdent, inexpr = inexpr, info = info} ->
    ()
end
