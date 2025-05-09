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
  | TmDecl {decl = DeclLet {
      body = TmApp {lhs = TmConst {val = CDPrint _}},
      inexpr = TmApp {lhs = TmConst {val = CError _},
                      rhs = TmSeq _},
      info = info}} ->
    -- NOTE(larshum, 2022-03-29): If we find an expression that corresponds to
    -- what is (currently) generated when compiling a semantic function, we
    -- replace it with a never term (which is compiled correctly).
    TmNever {ty = TyUnknown {info = info}, info = info}
  | t -> t

  sem _eliminateFailureCodeInSemanticFunction : DeclLetRecord -> DeclLetRecord
  sem _eliminateFailureCodeInSemanticFunction =
  | recLetBinding ->
    let DeclLetRecord : DeclLetRecord = DeclLetRecord in
    let body = _eliminateFailureCodeInSemanticFunctionBody recLetBinding.body in
    {recLetBinding with body = body}

  sem fixLanguageFragmentSemanticFunction : Expr -> Expr
  sem fixLanguageFragmentSemanticFunction =
  | TmDecl {decl = DeclLet t} ->
    TmDecl {decl = DeclLet {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}}
  | TmDecl {decl = DeclRecLets t} ->
    let bindings = map _eliminateFailureCodeInSemanticFunction t.bindings in
    TmDecl {decl = DeclRecLets {{t with bindings = bindings}
                  with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}}
  | TmDecl {decl = DeclType t} ->
    TmDecl {decl = DeclType {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}}
  | TmDecl {decl = DeclConDef t} ->
    TmDecl {decl = DeclConDef {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}}
  | TmDecl {decl = DeclUtest t} ->
    TmDecl {decl = DeclUtest {t with next = fixLanguageFragmentSemanticFunction t.next}}
  | TmDecl {decl = DeclExt t} ->
    TmDecl {decl = DeclExt {t with inexpr = fixLanguageFragmentSemanticFunction t.inexpr}}
  | t -> t
end
