include "mexpr/ast.mc"
include "map.mc"

lang MExprInlineSingleUse = MExprAst
  sem collectVariableUseCounts : Map Name Int -> Expr -> Map Name Int
  sem collectVariableUseCounts useCounts =
  | TmVar t -> mapInsertWith addi t.ident 1 useCounts
  | e -> sfold_Expr_Expr collectVariableUseCounts useCounts e

  sem isTrivialNode : Expr -> Bool
  sem isTrivialNode =
  | TmVar _ -> true
  | TmConst {val = CInt _ | CFloat _ | CChar _ | CBool _} -> true
  | TmRecord {bindings = bindings} -> mapIsEmpty bindings
  | _ -> false

  sem replaceSingleUseBindings : Map Name Int -> Map Name Expr -> Expr -> Expr
  sem replaceSingleUseBindings useCounts subMap =
  | TmVar t ->
    optionGetOrElse (lam. TmVar t) (mapLookup t.ident subMap)
  | TmDecl (t & {decl = DeclLet tt}) ->
    let default = lam body.
      TmDecl {t with decl = DeclLet {tt with body = body},
                     inexpr = replaceSingleUseBindings useCounts subMap t.inexpr}
    in
    let body = replaceSingleUseBindings useCounts subMap tt.body in
    -- NOTE(larshum, 2025-10-25): To avoid modifying the behavior of the
    -- program when inlining or making the implementation overly complicated,
    -- we only inline bodies consisting of simple nodes like constant literals
    -- or variables that certainly have no impact on performance.
    if isTrivialNode body then
      match mapLookup tt.ident useCounts with Some 1 then
        let subMap = mapInsert tt.ident body subMap in
        replaceSingleUseBindings useCounts subMap t.inexpr
      else
        default body
    else
      default body
  | e -> smap_Expr_Expr (replaceSingleUseBindings useCounts subMap) e

  sem inlineSingleUseBindings : Expr -> Expr
  sem inlineSingleUseBindings =
  | e ->
    let useCounts = collectVariableUseCounts (mapEmpty nameCmp) e in
    replaceSingleUseBindings useCounts (mapEmpty nameCmp) e
end
