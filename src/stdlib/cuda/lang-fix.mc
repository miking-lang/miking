-- Defines a function for replacing the failure case of semantic functions
-- generated from language fragments with empty code. Currently, this is
-- required for two reasons:
-- 1. The failure code uses 'error', which should result in an 'exit' in the
--    generated code. But this does not work on the GPU, so we cannot use it
--    there.
-- 2. The result of the error operation is returned, which results in a type
--    error in C/CUDA.

include "pmexpr/ast.mc"

lang CudaLanguageFragmentFix = PMExprAst
  sem _eliminateFailureCodeInSemanticFunctionBody : Expr -> Expr
  sem _eliminateFailureCodeInSemanticFunctionBody =
  | TmLam t ->
    TmLam {t with body = _eliminateFailureCodeInSemanticFunctionBody t.body}
  | TmMatch t ->
    TmMatch {t with els = _eliminateFailureCodeInSemanticFunctionBody t.els}
  | TmLet {
      body = TmApp {lhs = TmConst {val = CDPrint _}},
      inexpr = TmApp {lhs = TmConst {val = CError _},
                      rhs = TmSeq _},
      info = info} ->
    -- NOTE(larshum, 2022-03-29): If we find an expression that corresponds to
    -- what is (currently) generated when compiling a semantic function, we
    -- replace it with a never term (which is compiled correctly).
    TmNever {ty = TyUnknown {info = info}, info = info}
  | t -> t

  sem _eliminateFailureCodeInSemanticFunction : RecLetBinding -> RecLetBinding
  sem _eliminateFailureCodeInSemanticFunction =
  | recLetBinding ->
    let recLetBinding : RecLetBinding = recLetBinding in
    let body = _eliminateFailureCodeInSemanticFunctionBody recLetBinding.body in
    {recLetBinding with body = body}

  sem fixLanguageFragmentSemanticFunction : Expr -> Expr
  sem fixLanguageFragmentSemanticFunction =
  | TmLet t ->
    TmLet {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}
  | TmRecLets t ->
    let bindings = map _eliminateFailureCodeInSemanticFunction t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}
  | TmType t ->
    TmType {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}
  | TmConDef t ->
    TmConDef {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}
  | TmUtest t ->
    TmUtest {t with next = fixLanguageFragmentSemanticFunction t.next}
  | TmExt t ->
    TmExt {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}
  | t -> t
end
