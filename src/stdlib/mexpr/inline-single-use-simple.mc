include "ast.mc"
include "hoas.mc"
include "map.mc"
include "name.mc"
include "basic-types.mc"
include "seq.mc"
include "option.mc"
include "mexpr/ast-builder.mc"

-- This file implements a simple version of inlining, where every
-- binding that is used exactly once is inlined.
--
-- Assumptions:
-- * The AST to be processed either:
--   * ...contains no side-effects at all, or
--   * ...the side-effects commute, i.e., they can be re-ordered
--     relative each other without changing the semantics of the
--     program.
--
-- The implementation may leave behind `TempLam` nodes from
-- `mexpr/hoas.mc` if any inlined functions appear without being fully
-- applied. The implementation should pass over every node of the AST
-- thrice: once to collect usage counts going down, once to collect
-- definitions to inline later going up, and once to do inlining going
-- down. Note also that function parameters of inlined functions may
-- further get inlined if they are only used once in the function
-- body.
--
-- The primary entry point is `inlineSingleUseLets`.

lang InlineSingleUse = DeclAst + LetDeclAst + RecLetsDeclAst + VarAst + TempLamAst
  syn InlineMap =
  | InlineMap (Map Name (InlineMap -> Expr))
  type InlineSingleUseState =
    { useCounts : Map Name Int
    , toInline : Map Name (InlineMap -> Expr)
    }

  sem inlineSingleUseLets : Expr -> Expr
  sem inlineSingleUseLets = | tm ->
    match collectSingleUses {useCounts = mapEmpty nameCmp, toInline = mapEmpty nameCmp} tm with (st, tm) in
    insertSingleUses (InlineMap st.toInline) tm

  sem collectSingleUses : InlineSingleUseState -> Expr -> (InlineSingleUseState, Expr)
  sem collectSingleUses st =
  | TmDecl (x & {decl = DeclLet l}) ->
    match collectSingleUses st l.body with (st, body) in
    match collectSingleUses st x.inexpr with (st, inexpr) in
    let bodyIsSimple = sfold_Expr_Expr (lam. lam. false) true body in
    match (bodyIsSimple, mapLookup l.ident st.useCounts) with (true, _) | (_, Some 1) then
      ( { st with useCounts = mapRemove l.ident st.useCounts
        , toInline = mapInsert l.ident (mkInlineable st.useCounts body) st.toInline
        }
      , inexpr
      )
    else (st, TmDecl {x with decl = DeclLet {l with body = body}, inexpr = inexpr})
  | TmDecl (x & {decl = DeclRecLets l}) ->
    let f = lam st. lam binding.
      match collectSingleUses st binding.body with (st, body) in
      (st, {binding with body = body}) in
    match mapAccumL f st l.bindings with (st, bindings) in
    match collectSingleUses st x.inexpr with (st, inexpr) in
    let f = lam st. lam binding.
      match mapLookup binding.ident st.useCounts with Some 1 then
        ( { st with useCounts = mapRemove binding.ident st.useCounts
          , toInline = mapInsert binding.ident (mkInlineable st.useCounts binding.body) st.toInline
          }
        , None ()
        )
      else (st, Some binding) in
    match mapAccumL f st bindings with (st, bindings) in
    match filterOption bindings with bindings & ![]
    then (st, TmDecl {x with decl = DeclRecLets {l with bindings = bindings}, inexpr = inexpr})
    else (st, inexpr)
  | tm & TmOpaque x ->
    -- NOTE(vipa, 2026-02-06): We may not modify the contents of a
    -- TmOpaque, nor may we remove definitions it uses. This branch
    -- thus only finds uses, ensures that any use counts as more than
    -- 1, then returns the same TmOpaque unchanged.
    let used = (collectSingleUses {useCounts = mapEmpty nameCmp, toInline = mapEmpty nameCmp} x.body).0 in
    let st = {st with useCounts = mapUnionWith addi st.useCounts (mapMap (muli 2) used.useCounts)} in
    (st, tm)
  | tm & TmVar x ->
    ({st with useCounts = mapInsertWith addi x.ident 1 st.useCounts}, tm)
  | tm -> smapAccumL_Expr_Expr collectSingleUses st tm

  sem isSimpleInline : Expr -> Bool
  sem isSimpleInline =
  | TmConst _ -> true
  | TmVar _ -> true
  | _ -> false

  sem mkInlineable : Map Name Int -> Expr -> InlineMap -> Expr
  sem mkInlineable useCounts =
  | TmLam x ->
    switch optionGetOr 0 (mapLookup x.ident useCounts)
    case 1 then lam st.
      match st with InlineMap toInline in
      let f = lam arg.
        let toInline = mapInsert x.ident (lam. arg) toInline in
        mkInlineable useCounts x.body (InlineMap toInline) in
      TempLam {f = f, info = x.info, ty = x.ty}
    case 0 then lam st.
      let f = lam. mkInlineable useCounts x.body st in
      TempLam {f = f, info = x.info, ty = x.ty}
    case _ then lam st.
      let f = lam arg.
        if isSimpleInline arg then
          match st with InlineMap toInline in
          let toInline = mapInsert x.ident (lam. arg) toInline in
          mkInlineable useCounts x.body (InlineMap toInline)
        else
          let body = mkInlineable useCounts x.body st in
          let mkBinding = lam body. TmDecl
            { decl = DeclLet
              { ident = x.ident
              , tyAnnot = x.tyAnnot
              , tyBody = x.tyParam
              , body = arg
              , info = x.info
              }
            , inexpr = body
            , info = x.info
            , ty = tyunknown_
            } in
          match body with TempLam f
          then TempLam {f with f = lam bodyArg. mkBinding (f.f bodyArg)}
          else mkBinding body in
      TempLam {f = f, info = x.info, ty = x.ty}
    end
  | tm -> lam st. insertSingleUses st tm

  sem insertSingleUses : InlineMap -> Expr -> Expr
  sem insertSingleUses st =
  | TmApp x ->
    let lhs = insertSingleUses st x.lhs in
    let rhs = insertSingleUses st x.rhs in
    match lhs with TempLam f
    then f.f rhs
    else TmApp {x with lhs = lhs, rhs = rhs}
  | tm & TmVar x ->
    match st with InlineMap toInline in
    optionGetOr tm (optionMap (lam f. f st) (mapLookup x.ident toInline))
  | TmOpaque x ->
    -- NOTE(vipa, 2026-02-06): We may need to rename variables inside
    -- a `TmOpaque` because some surrounding variable has been
    -- renamed, and that's done via `insertSingleUses`. Because of
    -- what `collectSingleUses` does for `TmOpaque` we know that
    -- nothing inside is counted as single use, thus the only thing
    -- being inserted is what's considered as "simple" by `isSimple`
    -- above. That's _technically_ not just `TmVar`s, it could also be
    -- constants or literals, but I'm counting it good enough for now.
    TmOpaque {x with body = insertSingleUses st x.body}
  | tm -> smap_Expr_Expr (insertSingleUses st) tm
end
