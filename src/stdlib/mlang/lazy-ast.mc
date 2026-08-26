-- An AST node for lazily populating part of a program, intended for
-- code that is likely to be dead, where we can save time by not
-- creating it at all. This is currently primarily used in
-- `mlang/loader.mc` to avoid materializing the entire body of each
-- `sem` in every language fragment, since most of them will end up
-- being dead by the end of the program (typically only a smaller
-- subset of them, e.g., final compositions, are used).
--
-- Using it is relatively tricky, because we very much want to avoid
-- forcing the thunk until we really need to, but at the same time we
-- want to make sure to not break any of the passes it must live
-- through. This means, e.g., that `smap` et al. are disabled, they'll
-- crash, and you'll have to make an explicit case. Deadcode
-- elimination in particular gets a few added fields for precomputed
-- data that it will need to work without forcing the thunk.

include "lazy.mc"
include "set.mc"
include "seq.mc"
include "name.mc"
include "mexpr/ast.mc"
include "mexpr/info.mc"

lang LazyAst = Ast + OpaqueAst
  syn Expr +=
  | TmLazy
    { thunk : Lazy Expr
    -- A superset of free variables referenced in the expression
    -- produced by forcing `thunk`.
    , freeVars : Set Name
    -- Conservative approximation of whether evaluation of the
    -- expression produced by forcing `thunk` may have side-effects.
    , sideEffect : Bool
    , ty : Type
    , info : Info
    }

  sem infoTm +=
  | TmLazy t -> t.info
  sem tyTm +=
  | TmLazy t -> t.ty
  sem withInfo info +=
  | TmLazy t -> TmLazy {t with info = info}
  sem withType ty +=
  | TmLazy t -> TmLazy {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc +=
  | TmLazy _ ->
    error (join
      [ "TmLazy does not support smapAccumL_Expr_Expr. Either add necessary"
      , " data to it at construction time, use lazyMap, or use forceLazyExpr."
      ])

  -- Traverse an `Expr` forcing (and removing) any `TmLazy` present.
  sem forceLazyExpr : Expr -> Expr
  sem forceLazyExpr =
  | TmLazy t -> forceLazyExpr (lazyForce t.thunk)
  | tm & TmOpaque _ -> tm
  | t -> smap_Expr_Expr forceLazyExpr t

  -- Count a `TmLazy` as a single node, without forcing (and thus
  -- without instantiating) its thunk. This lets `countExprNodes`
  -- (see `PhaseStats`) be used on ASTs that still contain unforced
  -- `TmLazy` nodes, e.g. to measure AST size before dead code has
  -- had a chance to prune never-forced branches.
  sem countExprNodes count +=
  | TmLazy _ -> addi count 1
end
