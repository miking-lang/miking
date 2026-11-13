-- This file provides an interface for building local blocks of code
-- where:
--
-- * Variables may be rebound, meaning later references use the
--   updated value.
--   * Variables that have not been rebound are left as-is, i.e.,
--     they'll be free in the final produced expression.
--   * Every variable bound by an `ssa...` function behaves in this
--     way, we'll refer to them as "ssa-bound variables".
-- * A more imperative loop can be used.
-- * The continuation can be captured at any point in the block.
--   * The continuation is delimited by `ssaFinalize`
-- * Generally, expressions passed to functions in this file are opaque
--   when it comes to control-flow, `ssa...` functions only affect the
--   control-flow in `SSABlock`s.
--
-- # Laws
--
-- These laws are written with observational equality in mind which
-- roughly means that if a law says `a = b`, then:
-- * if they're both `Expr`s:
--   * Evaluating both `Expr`s in a context that binds all their free
--     variables produces identical values and identical side-effects
--     (in the same order), and have identical termination behaviour.
-- * if they're both `SSABlock`s:
--   * Putting both blocks in otherwise equal `SSABlock` contexts that
--     bind any free `ssaBlock` labels, then calling `ssaFinalize`
--     with identical `SSAExpr`s produce `Expr`s that are considered
--     equal according to the above.
--
-- Free variables in the equations below are implicitly universally
-- quantified, and the options argument to `ssaFinalize` is
-- elided. Laws preceeded by `(*)` follow from other laws, but are
-- helpful for readability.
--
-- ssaChain a (ssaChain b c) = ssaChain (ssaChain a b) c
--
-- ssaFinalize (ssaEmpty ()) x = x
-- ssaChain (ssaEmpty ()) a = ssaChain a (ssaEmpty ()) = a
--
-- ssaFinalize (ssaReturn a) b = a
-- ssaChain (ssaReturn x) a = ssaReturn x
-- (*) ssaReturn x = ssaCallCC (lam. x)
--
-- ssaFinalize (ssaChain (ssaRun x) a) b = semi_ x (ssaFinalize a b)
--
-- ssaSetPar {n_1 -> x_1, ..., n_k -> x_k} =
--   ssaMatch (utuple_ [x_1, ..., x_k]) (ptuple_ [npvar_ n_1, ..., npvar_ n_k]) (ssaEmpty ()) (ssaEmpty ())
-- ssaFinalize (ssaChain (ssaSet n x) a) b = bind_ (nulet_ n x) (ssaFinalize a b)
-- (*) ssaSet n x = ssaSetPar {n -> x}
--
-- ssaFinalize (ssaMatch x p a b) c = match_ x p (ssaFinalize a c) (ssaFinalize b c)
-- ssaChain (ssaMatch x p a b) c = ssaMatch x p (ssaChain a c) (ssaChain b c)
-- (*) ssaMatch x (npvar_ n) a b = ssaChain (ssaSet n x) a
-- (*) ssaMatch x pvarw_ a b = ssaChain (ssaRun x) a
-- (*) ssaMatch x p a b = ssaChain (ssaSet n x) (ssaMatch (nvar_ n) p a b)  -- (where `n` is fresh)
--
-- ssaLoop a = ssaChain a (ssaLoop a)   -- (the least solution)
-- (*) ssaChain (ssaLoop a) b = ssaLoop a
--
-- ssaBlock (lam. a) = a
-- ssaFinalize (ssaChain (ssaBlock f) c) x =
--   ssaFinalize (ssaChain (f (ssaChain c (ssaReturn x))) c) x
-- (*) ssaBlock (lam l. ssaChain l a) = ssaBlock (lam l. l) = ssaEmpty ()
--
-- ssaFinalize (ssaChain (ssaCallCC f) b) c = f (lam a. ssaFinalize (ssaChain a b) c)  -- (assuming names bound by `f` are fresh in `b` and `c`)


include "ast.mc"
include "ast-builder.mc"
include "utils.mc"
include "error.mc"
include "lazy.mc"
include "map.mc"
include "name.mc"
include "set.mc"
include "mlang/lazy-ast.mc"
include "info.mc"
include "seq.mc"
include "string.mc"
include "basic-types.mc"
include "symbolize.mc"
include "type-check.mc"
include "type.mc"
include "eval.mc"
include "free-vars.mc"


-- Marker type to signify that parameters of this type will have free
-- `TmVar`s substituted to refer to the correct value in scope
-- according to previously ssa-bound variables.
type SSAExpr = use Ast in Expr

let _ssaLabelMapEmpty : all v. () -> Map Symbol v
  = lam. mapEmpty (lam l. lam r. subi (sym2hash l) (sym2hash r))

let _ssaB2i : Bool -> Int = lam b. if b then 1 else 0

let _ssaLiveUnion : all v. Map Name v -> Map Name v -> Map Name v
  = lam a. lam b. mapUnionWith (lam a. lam. a) a b

-- For each `ssaBlock` label, the number of escapes to it, and the
-- names written on some path from the start of the code in question
-- to one of those escapes.
type SSAEscapes = Map Symbol {count : Int, writes : Set Name}

let _ssaEscUnion : SSAEscapes -> SSAEscapes -> SSAEscapes
  = lam a. lam b. mapUnionWith
    (lam l. lam r. {count = addi l.count r.count, writes = setUnion l.writes r.writes})
    a b

-- Account for `writes` happening before the code that escapes.
let _ssaEscAddWrites : Set Name -> SSAEscapes -> SSAEscapes
  = lam writes. lam escapes.
    mapMap (lam e. {e with writes = setUnion writes e.writes}) escapes

lang SSABlockLang = LazySubstitute + MExprFreeNames + LazyFreeNames
  -- What `ssaFinalize` needs to know about a point where control
  -- flow merges. `incoming` and `writes` are filled in when
  -- `construct`s are called, `params` after liveness analysis.
  -- `writes` holds the names written on some path from the start of
  -- the construct to the join.
  type SSAJoin =
    { incoming : Int
    , writes : Set Name
    , params : [(Name, (Type, Info))]
    }

  -- A value passed to a join parameter.
  syn SSASource =
  -- The variable has not been ssa-bound on this path, i.e., the value
  -- is whatever the variable is bound to outside the block.
  | SSAOuter Name
  -- An ssa-binding (`ssaSet`, a pattern in `ssaMatch`, or another
  -- join's parameter), with its `Info` and type.
  | SSADef (Info, Type)

  -- Live ssa-bound names, with the type and `Info` of an occurrence.
  type SSALive = Map Name (Type, Info)

  syn SSAStmt =
  | SRun Expr
  | SSetPar (Map Name (Info, Expr))
  | SMatch {info : Info, target : Expr, pat : Pat, thn : [SSAStmt], els : [SSAStmt], joinInfo : SSAJoin}
  | SLoop {info : Info, body : [SSAStmt], joinInfo : SSAJoin}
  | SBlock {info : Info, label : Symbol, body : [SSAStmt], joinInfo : SSAJoin}
  | SEscape {info : Info, label : Symbol}
  | SReturn {info : Info, value : Expr}
  | SNever {info : Info}
  | SCallCC {info : Info, construct : ([SSAStmt] -> Expr) -> Expr}
  -- An `SCallCC` whose `construct` has been called. `result` is the
  -- compiled code of the block, read by the `TmLazy` that the
  -- continuation returned.
  | SCallCCInst
    { info : Info
    , expr : Expr
    , calls : [{block : [SSAStmt], result : Ref (Option Expr)}]
    , joinInfo : SSAJoin
    }

  type SSABlock = [SSAStmt]

  -- Options for `ssaFinalize`, deciding how types are handled. See
  -- `ssaFinalizeOpts` and `ssaFinalizeOptsUntyped` for typical values.
  --
  -- * `unify infos expected actual` makes two types equal, reporting
  --   an error at `infos` if they're incompatible. It is used for the
  --   result type of the block (`ssaReturn` values, the fall-through,
  --   `construct`'s expression), and to connect each join parameter's
  --   type to the type of an occurrence that reads it.
  -- * `newVar info` produces a fresh unification variable, used as the
  --   type of a join parameter.
  -- * `joinParam {info, name, ty, sources, readInfo}` is called once
  --   per join parameter, after all jumps to the join have been
  --   generated. `info` is the `Info` of the construct that creates
  --   the join
  --   (given to `ssaMatchI`, `ssaLoopI`, `ssaBlockI`, or
  --   `ssaCallCCI`; `ssaMatch` uses its target's `Info`, the other
  --   non-`I` builders `NoInfo`), `name` the variable, `ty` the type
  --   produced by `newVar`, and `sources` the values passed to the
  --   parameter (one per jump, in no particular order). It is
  --   expected to relate `ty` to the `sources`, or report an error if
  --   some source is disallowed. `sources` always contains at least
  --   one `SSADef`. `readInfo` is the `Info` of an occurrence reading
  --   the variable after the join, preferring the syntactically first
  --   one.
  --
  -- A join is a point where at least two control flow paths meet
  -- (after an `ssaMatch`, `ssaBlock`, or `ssaCallCC`, or the head of
  -- an `ssaLoop`), and it has a parameter for each variable that is
  -- both read after the join and ssa-bound on some path to it.
  -- Variables passed unchanged on every path, and points reached by
  -- only one path, don't involve `joinParam`.
  type SSAJoinParamArgs =
    { info : Info
    , name : Name
    , ty : Type
    , sources : [SSASource]
    , readInfo : Info
    }

  type SSAFinalizeOpts =
    { unify : [Info] -> Type -> Type -> ()
    , newVar : Info -> Type
    , joinParam : SSAJoinParamArgs -> ()
    }

  -- A `joinParam` that unifies the parameter with every ssa-binding
  -- passed to it, and leaves values from outside the block
  -- unconstrained.
  sem ssaJoinParamDefault : ([Info] -> Type -> Type -> ()) -> SSAJoinParamArgs -> ()
  sem ssaJoinParamDefault unify =
  | args ->
    iter
      (lam s. match s with SSADef (defInfo, defTy) then unify [defInfo, args.info] args.ty defTy else ())
      args.sources

  -- Options given `unify` and `newVar`, using `ssaJoinParamDefault`.
  sem ssaFinalizeOpts : ([Info] -> Type -> Type -> ()) -> (Info -> Type) -> SSAFinalizeOpts
  sem ssaFinalizeOpts unify =
  | newVar -> {unify = unify, newVar = newVar, joinParam = ssaJoinParamDefault unify}

  -- Options that don't relate types at all; join parameters get type
  -- `TyUnknown`.
  sem ssaFinalizeOptsUntyped : () -> SSAFinalizeOpts
  sem ssaFinalizeOptsUntyped =
  | _ ->
    { unify = lam. lam. lam. ()
    , newVar = lam. tyunknown_
    , joinParam = lam. ()
    }

  sem ssaJoinEmpty : () -> SSAJoin
  sem ssaJoinEmpty =
  | _ -> {incoming = 0, writes = setEmpty nameCmp, params = []}

  -- === Builders ===

  sem ssaEmpty : () -> SSABlock
  sem ssaEmpty =
  | _ -> []

  -- Sequential composition
  sem ssaChain : SSABlock -> SSABlock -> SSABlock
  sem ssaChain a =
  | b -> concat a b

  sem ssaSeq : [SSABlock] -> SSABlock
  sem ssaSeq =
  | blocks -> join blocks

  -- Run something for side-effects
  sem ssaRun : SSAExpr -> SSABlock
  sem ssaRun =
  | x -> [SRun x]

  -- Unconditionally rebind a set of variables to newly computed
  -- values. Note that the values are computed before variables are
  -- rebound, i.e., each expression sees old bindings. However, the
  -- order the expressions are evaluated in is unspecified, so the
  -- expressions must not exhibit order-dependent side-effects.
  sem ssaSetPar : Map Name SSAExpr -> SSABlock
  sem ssaSetPar =
  | binds -> ssaSetParI (mapMap (lam x. (infoTm x, x)) binds)

  sem ssaSetParI : Map Name (Info, SSAExpr) -> SSABlock
  sem ssaSetParI =
  | binds -> [SSetPar binds]

  sem ssaSet : Name -> SSAExpr -> SSABlock
  sem ssaSet n =
  | x -> ssaSetI (infoTm x) n x

  sem ssaSetI : Info -> Name -> SSAExpr -> SSABlock
  sem ssaSetI info n =
  | x -> ssaSetParI (mapFromSeq nameCmp [(n, (info, x))])

  -- Branch on a pattern match. Note that variables bound by the pattern
  -- on a successful match remain bound after the `ssaMatch` as well,
  -- and are otherwise unchanged from before the `ssaMatch`. See also
  -- `ssaMatchIrrefutable`.
  sem ssaMatch : SSAExpr -> Pat -> SSABlock -> SSABlock -> SSABlock
  sem ssaMatch target pat thn =
  | els -> ssaMatchI (infoTm target) target pat thn els

  sem ssaMatchI : Info -> SSAExpr -> Pat -> SSABlock -> SSABlock -> SSABlock
  sem ssaMatchI info target pat thn =
  | els ->
    [ SMatch
      { info = info, target = target, pat = pat, thn = thn, els = els
      , joinInfo = ssaJoinEmpty ()
      } ]

  -- Match on a pattern that is assumed to always match; crashes at
  -- runtime if it doesn't.
  --
  -- ssaMatchIrrefutable x p a = ssaMatch x p a (ssaReturn never_)
  sem ssaMatchIrrefutable : SSAExpr -> Pat -> SSABlock -> SSABlock
  sem ssaMatchIrrefutable target pat =
  | thn -> ssaMatchIrrefutableI (infoTm target) target pat thn

  sem ssaMatchIrrefutableI : Info -> SSAExpr -> Pat -> SSABlock -> SSABlock
  sem ssaMatchIrrefutableI info target pat =
  | thn -> ssaMatchI info target pat thn [SNever {info = info}]

  -- Infinite loop. Might still be exited via `ssaBlock`.
  sem ssaLoop : SSABlock -> SSABlock
  sem ssaLoop =
  | body -> ssaLoopI (NoInfo ()) body

  sem ssaLoopI : Info -> SSABlock -> SSABlock
  sem ssaLoopI info =
  | body -> [SLoop {info = info, body = body, joinInfo = ssaJoinEmpty ()}]

  -- Allow control flow escape from a block. The given function should
  -- define the block, and it is given an `SSABlock` that when executed
  -- will escape the block entirely. Note that the escape `SSABlock` is
  -- only meaningful inside the block, and should not escape.
  sem ssaBlock : (SSABlock -> SSABlock) -> SSABlock
  sem ssaBlock =
  | f -> ssaBlockI (NoInfo ()) f

  sem ssaBlockI : Info -> (SSABlock -> SSABlock) -> SSABlock
  sem ssaBlockI info =
  | f ->
    let label = gensym () in
    let body = f [SEscape {info = info, label = label}] in
    [SBlock {info = info, label = label, body = body, joinInfo = ssaJoinEmpty ()}]

  -- Escape the _entire_ surrounding `SSABlock`, producing the given
  -- value. Escapes all the way to the surrounding `ssaFinalize` call or call
  -- to the continuation in `ssaCallCC`, whichever is closer.
  sem ssaReturn : SSAExpr -> SSABlock
  sem ssaReturn =
  | x -> ssaReturnI (infoTm x) x

  sem ssaReturnI : Info -> SSAExpr -> SSABlock
  sem ssaReturnI info =
  | x -> [SReturn {info = info, value = x}]

  -- Call with continuation, where each call to the continuation can
  -- run arbitrary code before the continuation resumes. The sole
  -- argument (`construct`) is expected to build an `Expr`, and may
  -- use its parameter (`resume`) to construct calls to the
  -- continuation by passing whatever code should run before it.
  --
  -- `ssaCallCC` captures the continuation up until `ssaFinalize` or a
  -- call to `resume`, whichever is closer, similar to how `ssaReturn`
  -- returns to such places. For example:
  --   ssaFinalize opts
  --     (ssaSeq
  --       [ ssaCallCC (lam continue.
  --           addi_ (continue (ssaReturn (int_ 1))) (continue (ssaEmpty ())))
  --       , ssaReturn (int_ 5) ])
  --     unit_
  --   -- is equivalent to `addi_ (int_ 1) (int_ 5)`
  --
  -- There are a number of rules for correct usage:
  -- * The expression built by `construct` may not bind an ssa-bound
  --   variable, though it may refer to them.
  -- * The `Expr` produced by calling `resume` must be treated as
  --   opaque, only its `info` and `ty` fields may be examined.
  -- * Each `SSABlock` passed to `resume` may read variables bound by
  --   `construct`'s `Expr` as well as ssa-bound variables, and
  --   ssa-bound variables can be rebound there as usual.
  -- * `resume` may only be called while `construct` is executing.
  sem ssaCallCC : ((SSABlock -> Expr) -> SSAExpr) -> SSABlock
  sem ssaCallCC =
  | construct -> ssaCallCCI (NoInfo ()) construct

  sem ssaCallCCI : Info -> ((SSABlock -> Expr) -> SSAExpr) -> SSABlock
  sem ssaCallCCI info =
  | construct -> [SCallCC {info = info, construct = construct}]

  -- Build the final expression for the entire `SSABlock`. The `SSAExpr`
  -- is what's returned if no `ssaReturn` instruction is encountered.
  sem ssaFinalize : SSAFinalizeOpts -> SSABlock -> SSAExpr -> Expr
  sem ssaFinalize opts block =
  | fall ->
    let resTy = tyTm fall in
    let inst = ssaInstBlock resTy block in
    let tracked = inst.allWrites in
    let liveCtx = {tracked = tracked, labels = _ssaLabelMapEmpty ()} in
    let liveOut = ssaReads tracked (mapEmpty nameCmp) fall in
    match ssaLiveBlock liveCtx liveOut inst.block with (_, block) in
    let ctx =
      { unify = opts.unify
      , newVar = opts.newVar
      , joinParam = opts.joinParam
      , resTy = resTy
      , fall = lam env. ssaSubst env fall
      , labels = _ssaLabelMapEmpty ()
      } in
    let env = {names = mapEmpty nameCmp, vals = mapEmpty nameCmp} in
    forceLazyExpr (ssaCompileBlock ctx env block)

  -- === Helpers ===

  -- The names bound by a pattern, with their types and `Info`s.
  sem ssaPatBinds : Map Name (Type, Info) -> Pat -> Map Name (Type, Info)
  sem ssaPatBinds acc =
  | PatNamed {ident = PName n, ty = ty, info = info} -> mapInsert n (ty, info) acc
  | p & PatSeqEdge {middle = PName n, info = info} ->
    sfold_Pat_Pat ssaPatBinds (mapInsert n (tyPat p, info) acc) p
  | p -> sfold_Pat_Pat ssaPatBinds acc p

  sem ssaRenamePat : Map Name Name -> Pat -> Pat
  sem ssaRenamePat names =
  | PatNamed (x & {ident = PName n}) ->
    PatNamed {x with ident = PName (mapFindExn n names)}
  | PatSeqEdge (x & {middle = PName n}) ->
    smap_Pat_Pat (ssaRenamePat names)
      (PatSeqEdge {x with middle = PName (mapFindExn n names)})
  | p -> smap_Pat_Pat (ssaRenamePat names) p

  -- Add occurrences of `tracked` names to the live set. The
  -- expression is assumed to come before the code `acc` was computed
  -- from, so its occurrences take precedence.
  sem ssaReads : Set Name -> SSALive -> Expr -> SSALive
  sem ssaReads tracked acc =
  | tm -> mapUnionWith (lam new. lam. new) (ssaReadsFirst tracked (mapEmpty nameCmp) tm) acc

  -- Like `ssaReads`, but keeps occurrences already in `acc`.
  sem ssaReadsFirst : Set Name -> SSALive -> Expr -> SSALive
  sem ssaReadsFirst tracked acc =
  | TmVar x ->
    if setMem x.ident tracked
    then mapInsertWith (lam old. lam. old) x.ident (x.ty, x.info) acc
    else acc
  | TmLazy _ -> acc
  | tm -> sfold_Expr_Expr (ssaReadsFirst tracked) acc tm

  -- Set the `freeVars` of the continuation results in `construct`'s
  -- expression, without entering them.
  sem ssaSetLazyFreeVars : Set Name -> Expr -> Expr
  sem ssaSetLazyFreeVars freeVars =
  | TmLazy t -> TmLazy {t with freeVars = freeVars}
  | TmOpaque x -> TmOpaque {x with body = ssaSetLazyFreeVars freeVars x.body}
  | tm -> smap_Expr_Expr (ssaSetLazyFreeVars freeVars) tm

  -- Check that `construct` doesn't bind a name that is live in a call
  -- to the continuation it encloses, i.e., that every such name is
  -- still free in its expression.
  sem ssaCheckConstruct : Info -> Set Name -> Expr -> Expr
  sem ssaCheckConstruct info live =
  | tm ->
    let tm = ssaSetLazyFreeVars live tm in
    let bound = setSubtract live (freeNames tm) in
    if setIsEmpty bound then tm else
      errorSingle [info] (join
        [ "The expression built by `construct` in `ssaCallCC` binds the "
        , "ssa-bound variable(s) "
        , strJoin ", " (map (lam n. join ["'", nameGetStr n, "'"]) (setToSeq bound))
        , " around a call to the continuation."
        ])

  -- === Instantiation ===
  -- Calls `construct`s, removes dead code, and computes `incoming`
  -- and `writes` for joins.
  --
  -- Besides the instantiated code, each step produces:
  -- * `falls`: whether some path falls through.
  -- * `writes`: the names written on some path that falls through
  --   (empty if none does).
  -- * `escapes`: escapes to `ssaBlock` labels, see `SSAEscapes`.
  -- * `allWrites`: the names written anywhere, including on paths that
  --   return.

  sem ssaInstBlock : Type -> SSABlock
                   -> { block : SSABlock, falls : Bool, writes : Set Name
                      , escapes : SSAEscapes, allWrites : Set Name }
  sem ssaInstBlock resTy =
  | block ->
    recursive let work = lam acc. lam stmts.
      match stmts with [stmt] ++ stmts then
        let r = ssaInstStmt resTy stmt in
        let acc =
          { block = snoc acc.block r.stmt
          , falls = r.falls
          -- `acc.writes` are the writes on paths falling through the
          -- statements before this one
          , escapes = _ssaEscUnion acc.escapes (_ssaEscAddWrites acc.writes r.escapes)
          , writes = setUnion acc.writes r.writes
          , allWrites = setUnion acc.allWrites r.allWrites
          } in
        if r.falls then work acc stmts else {acc with writes = setEmpty nameCmp}
      else acc in
    work
      { block = []
      , falls = true
      , writes = setEmpty nameCmp
      , escapes = _ssaLabelMapEmpty ()
      , allWrites = setEmpty nameCmp
      }
      block

  sem ssaInstStmt : Type -> SSAStmt
                  -> { stmt : SSAStmt, falls : Bool, writes : Set Name
                     , escapes : SSAEscapes, allWrites : Set Name }
  sem ssaInstStmt resTy =
  | stmt & SRun _ ->
    { stmt = stmt, falls = true, writes = setEmpty nameCmp
    , escapes = _ssaLabelMapEmpty (), allWrites = setEmpty nameCmp
    }
  | stmt & SSetPar binds ->
    let writes = mapMap (lam. ()) binds in
    { stmt = stmt, falls = true, writes = writes
    , escapes = _ssaLabelMapEmpty (), allWrites = writes
    }
  | stmt & (SReturn _ | SNever _) ->
    { stmt = stmt, falls = false, writes = setEmpty nameCmp
    , escapes = _ssaLabelMapEmpty (), allWrites = setEmpty nameCmp
    }
  | stmt & SEscape x ->
    { stmt = stmt, falls = false, writes = setEmpty nameCmp
    , escapes = mapInsert x.label {count = 1, writes = setEmpty nameCmp} (_ssaLabelMapEmpty ())
    , allWrites = setEmpty nameCmp
    }
  | SMatch x ->
    let thn = ssaInstBlock resTy x.thn in
    let els = ssaInstBlock resTy x.els in
    -- Pattern variables are bound on every path through `thn`
    let patWrites = mapMap (lam. ()) (ssaPatBinds (mapEmpty nameCmp) x.pat) in
    let thnWrites = if thn.falls then setUnion patWrites thn.writes else setEmpty nameCmp in
    let writes = setUnion thnWrites els.writes in
    let incoming = addi (_ssaB2i thn.falls) (_ssaB2i els.falls) in
    { stmt = SMatch
      { x with thn = thn.block, els = els.block
      , joinInfo = {x.joinInfo with incoming = incoming, writes = writes}
      }
    , falls = gti incoming 0
    , writes = writes
    , escapes = _ssaEscUnion (_ssaEscAddWrites patWrites thn.escapes) els.escapes
    , allWrites = setUnion patWrites (setUnion thn.allWrites els.allWrites)
    }
  | SLoop x ->
    let body = ssaInstBlock resTy x.body in
    -- The paths falling through the body are those that jump back to
    -- the loop head, so their writes may reach an escape in a later
    -- iteration.
    { stmt = SLoop
      { x with body = body.block
      , joinInfo = {x.joinInfo with writes = body.writes}
      }
    , falls = false
    , writes = setEmpty nameCmp
    , escapes = _ssaEscAddWrites body.writes body.escapes
    , allWrites = body.allWrites
    }
  | SBlock x ->
    let body = ssaInstBlock resTy x.body in
    let own = mapLookupOrElse
      (lam. {count = 0, writes = setEmpty nameCmp}) x.label body.escapes in
    let incoming = addi (_ssaB2i body.falls) own.count in
    let writes = setUnion body.writes own.writes in
    { stmt = SBlock
      { x with body = body.block
      , joinInfo = {x.joinInfo with incoming = incoming, writes = writes}
      }
    , falls = gti incoming 0
    , writes = writes
    , escapes = mapRemove x.label body.escapes
    , allWrites = body.allWrites
    }
  | SCallCC x ->
    let done = ref false in
    let calls = ref [] in
    let continue = lam block.
      if deref done then
        errorSingle [x.info] "A continuation from `ssaCallCC` was called after `construct` returned."
      else
        let result = ref (None ()) in
        modref calls (snoc (deref calls) (block, result));
        TmLazy
        { thunk = lazy (lam.
            match deref result with Some tm then tm
            else error "Compiler error: forced an uncompiled `ssaCallCC` continuation.")
        , freeVars = setEmpty nameCmp
        , sideEffect = true
        , ty = resTy
        , info = x.info
        } in
    let expr = x.construct continue in
    modref done true;
    let calls = map
      (lam c. match c with (block, result) in {inst = ssaInstBlock resTy block, result = result})
      (deref calls) in
    let incoming = foldl (lam acc. lam c. addi acc (_ssaB2i c.inst.falls)) 0 calls in
    let writes = foldl (lam acc. lam c. setUnion acc c.inst.writes) (setEmpty nameCmp) calls in
    let escapes = foldl (lam acc. lam c. _ssaEscUnion acc c.inst.escapes) (_ssaLabelMapEmpty ()) calls in
    let allWrites = foldl (lam acc. lam c. setUnion acc c.inst.allWrites) (setEmpty nameCmp) calls in
    { stmt = SCallCCInst
      { info = x.info
      , expr = expr
      , calls = map (lam c. {block = c.inst.block, result = c.result}) calls
      , joinInfo = {incoming = incoming, writes = writes, params = []}
      }
    , falls = gti incoming 0
    , writes = writes
    , escapes = escapes
    , allWrites = allWrites
    }

  -- === Liveness ===

  sem ssaLiveBlock : {tracked : Set Name, labels : Map Symbol SSALive}
                   -> SSALive -> SSABlock -> (SSALive, SSABlock)
  sem ssaLiveBlock ctx out =
  | block ->
    foldr
      (lam stmt. lam acc.
        match ssaLiveStmt ctx acc.0 stmt with (live, stmt) in
        (live, cons stmt acc.1))
      (out, [])
      block

  -- Takes the live set after the statement (when falling through)
  -- and produces the live set before it.
  sem ssaLiveStmt : {tracked : Set Name, labels : Map Symbol SSALive}
                  -> SSALive -> SSAStmt -> (SSALive, SSAStmt)
  sem ssaLiveStmt ctx out =
  | stmt & SRun x -> (ssaReads ctx.tracked out x, stmt)
  | stmt & SSetPar binds ->
    let live = mapDifference out binds in
    let live = mapFoldWithKey
      (lam acc. lam. lam b. ssaReads ctx.tracked acc b.1) live binds in
    (live, stmt)
  | stmt & SReturn x -> (ssaReads ctx.tracked (mapEmpty nameCmp) x.value, stmt)
  | stmt & SNever _ -> (mapEmpty nameCmp, stmt)
  | stmt & SEscape x ->
    match mapLookup x.label ctx.labels with Some live then (live, stmt) else
      errorSingle [x.info] "An escape from `ssaBlock` was used outside of its block."
  | SMatch x ->
    match ssaLiveBlock ctx out x.thn with (thnLive, thn) in
    match ssaLiveBlock ctx out x.els with (elsLive, els) in
    let thnLive = mapDifference thnLive (ssaPatBinds (mapEmpty nameCmp) x.pat) in
    let live = _ssaLiveUnion thnLive elsLive in
    let live = ssaReads ctx.tracked live x.target in
    (live, SMatch {x with thn = thn, els = els, joinInfo = ssaJoinParams out x.joinInfo})
  | SBlock x ->
    let bodyCtx = {ctx with labels = mapInsert x.label out ctx.labels} in
    match ssaLiveBlock bodyCtx out x.body with (live, body) in
    (live, SBlock {x with body = body, joinInfo = ssaJoinParams out x.joinInfo})
  | SLoop x ->
    recursive let fix = lam head.
      match ssaLiveBlock ctx head x.body with (bodyLive, body) in
      let next = _ssaLiveUnion head bodyLive in
      if eqi (mapSize next) (mapSize head) then (head, body) else fix next in
    match fix (mapEmpty nameCmp) with (head, body) in
    (head, SLoop {x with body = body, joinInfo = ssaJoinParams head x.joinInfo})
  | SCallCCInst x ->
    match mapAccumL
      (lam acc. lam c.
        match ssaLiveBlock ctx out c.block with (live, block) in
        (_ssaLiveUnion acc live, {c with block = block}))
      (mapEmpty nameCmp)
      x.calls
    with (callsLive, calls) in
    let expr = ssaCheckConstruct x.info (mapMap (lam. ()) callsLive) x.expr in
    let live = ssaReads ctx.tracked callsLive expr in
    ( live
    , SCallCCInst
      {x with expr = expr, calls = calls, joinInfo = ssaJoinParams out x.joinInfo}
    )

  sem ssaJoinParams : SSALive -> SSAJoin -> SSAJoin
  sem ssaJoinParams live =
  | j ->
    {j with params = mapBindings (mapFilterWithKey (lam n. lam. setMem n j.writes) live)}

  -- === Compilation ===

  type SSAEnv =
    -- The current ssa-name of each written name
    { names : Map Name Name
    -- The type and binding `Info` of the current value of each
    -- written name
    , vals : Map Name (Type, Info)
    }

  type SSACtx =
    { unify : [Info] -> Type -> Type -> ()
    , newVar : Info -> Type
    , joinParam : SSAJoinParamArgs -> ()
    , resTy : Type
    -- What to do when falling off the end of the current block
    , fall : SSAEnv -> Expr
    , labels : Map Symbol (SSAEnv -> Expr)
    }

  sem ssaSubst : SSAEnv -> Expr -> Expr
  sem ssaSubst env =
  | tm -> if mapIsEmpty env.names then tm else substituteIdentifiers env.names tm

  sem ssaBindName : SSAEnv -> Name -> Name -> (Type, Info) -> SSAEnv
  sem ssaBindName env n ssaName =
  | val -> {names = mapInsert n ssaName env.names, vals = mapInsert n val env.vals}

  sem ssaCompileBlock : SSACtx -> SSAEnv -> SSABlock -> Expr
  sem ssaCompileBlock ctx env =
  | [] -> ctx.fall env
  | [stmt] ++ rest ->
    ssaCompileStmt ctx env (lam env. ssaCompileBlock ctx env rest) stmt

  -- Compile a statement, given what comes after it.
  sem ssaCompileStmt : SSACtx -> SSAEnv -> (SSAEnv -> Expr) -> SSAStmt -> Expr
  sem ssaCompileStmt ctx env next =
  | SRun x ->
    let x = ssaSubst env x in
    let info = infoTm x in
    TmDecl
    { decl = DeclLet
      { ident = nameNoSym "", tyAnnot = tyunknown_, tyBody = tyTm x
      , body = x, info = info
      }
    , inexpr = next env, ty = ctx.resTy, info = info
    }
  | SSetPar binds ->
    let binds = map
      (lam b. match b with (n, (info, x)) in
        let x = ssaSubst env x in
        {n = n, ssaName = nameSetNewSym n, info = info, x = x})
      (mapBindings binds) in
    let env = foldl
      (lam env. lam b. ssaBindName env b.n b.ssaName (tyTm b.x, b.info))
      env binds in
    foldr
      (lam b. lam inexpr.
        TmDecl
        { decl = DeclLet
          { ident = b.ssaName, tyAnnot = tyunknown_, tyBody = tyTm b.x
          , body = b.x, info = b.info
          }
        , inexpr = inexpr, ty = ctx.resTy, info = b.info
        })
      (next env)
      binds
  | SReturn x ->
    let value = ssaSubst env x.value in
    ctx.unify [x.info] ctx.resTy (tyTm value);
    value
  | SNever x -> TmNever {ty = ctx.resTy, info = x.info}
  | SEscape x ->
    match mapLookup x.label ctx.labels with Some escape then escape env else
      errorSingle [x.info] "An escape from `ssaBlock` was used outside of its block."
  | SMatch x ->
    let target = ssaSubst env x.target in
    let binds = ssaPatBinds (mapEmpty nameCmp) x.pat in
    let fresh = mapMapWithKey (lam n. lam. nameSetNewSym n) binds in
    let pat = ssaRenamePat fresh x.pat in
    let thnEnv = mapFoldWithKey
      (lam env. lam n. lam val. ssaBindName env n (mapFindExn n fresh) val)
      env binds in
    ssaWithJoin ctx x.info x.joinInfo env next
      (lam jump.
        let ctx = {ctx with fall = jump} in
        TmMatch
        { target = target, pat = pat
        , thn = ssaCompileBlock ctx thnEnv x.thn
        , els = ssaCompileBlock ctx env x.els
        , ty = ctx.resTy, info = x.info
        })
  | SBlock x ->
    ssaWithJoin ctx x.info x.joinInfo env next
      (lam escape.
        let ctx = {ctx with fall = escape, labels = mapInsert x.label escape ctx.labels} in
        ssaCompileBlock ctx env x.body)
  | SLoop x ->
    let loopName = nameSym "loop" in
    let params = ssaMkParams ctx x.info x.joinInfo.params in
    let fty = ssaJoinType ctx params in
    let jump = ssaJump ctx x.info loopName fty params in
    let fn = ssaJoinLam ctx x.info params env
      (lam env. ssaCompileBlock {ctx with fall = jump} env x.body) in
    let entry = jump env in
    ssaFinishParams ctx x.info params;
    TmDecl
    { decl = DeclRecLets
      { bindings =
        [ { ident = loopName, tyAnnot = tyunknown_, tyBody = fty
          , body = fn, info = x.info
          } ]
      , info = x.info
      }
    , inexpr = entry, ty = ctx.resTy, info = x.info
    }
  | SCallCCInst x ->
    let expr = ssaSubst env x.expr in
    ctx.unify [x.info] ctx.resTy (tyTm expr);
    ssaWithJoin ctx x.info x.joinInfo env next
      (lam jump.
        let ctx = {ctx with fall = jump} in
        iter (lam c. modref c.result (Some (ssaCompileBlock ctx env c.block))) x.calls;
        expr)

  -- Build the code for a join point. `after` produces the code after
  -- the join, and `body` the code that may jump to it, given a
  -- function producing a jump. The join is inlined if only one path
  -- reaches it.
  sem ssaWithJoin : SSACtx -> Info -> SSAJoin -> SSAEnv -> (SSAEnv -> Expr)
                  -> ((SSAEnv -> Expr) -> Expr) -> Expr
  sem ssaWithJoin ctx info j env after =
  | body ->
    if eqi j.incoming 0 then
      body (lam. error "Compiler error: jump to an unreachable join in `ssaFinalize`.")
    else if eqi j.incoming 1 then body after
    else
      let joinName = nameSym "join" in
      let params = ssaMkParams ctx info j.params in
      let fty = ssaJoinType ctx params in
      let fn = ssaJoinLam ctx info params env after in
      let inexpr = body (ssaJump ctx info joinName fty params) in
      ssaFinishParams ctx info params;
      TmDecl
      { decl = DeclLet
        { ident = joinName, tyAnnot = tyunknown_, tyBody = fty
        , body = fn, info = info
        }
      , inexpr = inexpr
      , ty = ctx.resTy, info = info
      }

  -- A join parameter during compilation: `ty` is a fresh type,
  -- `occ` the type and `Info` of an occurrence reading it, and
  -- `sources` collects the values passed by jumps.
  type SSAParam =
    { name : Name
    , ty : Type
    , occ : (Type, Info)
    , sources : Ref [SSASource]
    }

  sem ssaMkParams : SSACtx -> Info -> [(Name, (Type, Info))] -> [SSAParam]
  sem ssaMkParams ctx info =
  | params ->
    map
      (lam p. match p with (n, occ) in
        {name = n, ty = ctx.newVar info, occ = occ, sources = ref []})
      params

  -- Relate parameter types to what's passed to them and to how
  -- they're read. Must run after all jumps to the join are generated.
  sem ssaFinishParams : SSACtx -> Info -> [SSAParam] -> ()
  sem ssaFinishParams ctx info =
  | params ->
    iter
      (lam p.
        match p.occ with (occTy, occInfo) in
        ctx.joinParam
          {info = info, name = p.name, ty = p.ty, sources = deref p.sources, readInfo = occInfo};
        ctx.unify [occInfo, info] occTy p.ty)
      params

  sem ssaJoinType : SSACtx -> [SSAParam] -> Type
  sem ssaJoinType ctx =
  | [] -> TyArrow {info = NoInfo (), from = tyunit_, to = ctx.resTy}
  | params ->
    foldr
      (lam p. lam to. TyArrow {info = NoInfo (), from = p.ty, to = to})
      ctx.resTy params

  sem ssaJoinLam : SSACtx -> Info -> [SSAParam] -> SSAEnv
                 -> (SSAEnv -> Expr) -> Expr
  sem ssaJoinLam ctx info params env =
  | after ->
    let params = map
      (lam p. {n = p.name, ssaName = nameSetNewSym p.name, ty = p.ty})
      params in
    let env = foldl
      (lam env. lam p. ssaBindName env p.n p.ssaName (p.ty, info))
      env params in
    let mkLam = lam ident. lam ty. lam body.
      TmLam
      { ident = ident, tyAnnot = tyunknown_, tyParam = ty, body = body
      , ty = TyArrow {info = info, from = ty, to = tyTm body}, info = info
      } in
    let body = after env in
    match params with [] then mkLam (nameNoSym "") tyunit_ body
    else foldr (lam p. lam body. mkLam p.ssaName p.ty body) body params

  -- Jump to a join point, recording the value passed to each
  -- parameter.
  sem ssaJump : SSACtx -> Info -> Name -> Type -> [SSAParam] -> SSAEnv -> Expr
  sem ssaJump ctx info joinName fty params =
  | env ->
    let args = map
      (lam p.
        match
          match mapLookup p.name env.vals with Some (vty, vinfo) then
            (SSADef (vinfo, vty), mapFindExn p.name env.names, vty)
          else (SSAOuter p.name, p.name, p.ty)
        with (source, ident, ty) in
        modref p.sources (snoc (deref p.sources) source);
        TmVar {ident = ident, ty = ty, info = info, frozen = false})
      params in
    let args = match args with [] then [unit_] else args in
    let app = lam f. lam arg.
      let ty = match tyTm f with TyArrow {to = to} then to else tyunknown_ in
      TmApp {lhs = f, rhs = arg, ty = ty, info = info} in
    foldl app (TmVar {ident = joinName, ty = fty, info = info, frozen = false}) args
end


lang SSABlockTest = SSABlockLang + MExprSym + MExprTypeCheck + MExprEval end

mexpr

use SSABlockTest in

let isDef = lam s. match s with SSADef _ then true else false in
-- Untyped, but checks that every join parameter gets an ssa-binding
let checked =
  { ssaFinalizeOptsUntyped () with
    joinParam = lam args.
      if any isDef args.sources then () else
        errorSingle [args.info] (concat "No ssa-binding reaches the join parameter " (nameGetStr args.name))
  } in
let unifyCounter = lam.
  let count = ref 0 in
  (ssaFinalizeOpts (lam. lam. lam. modref count (addi (deref count) 1)) (lam. tyunknown_), count) in
-- Record the sources of each join parameter, as "d" for `SSADef` and
-- "o" for `SSAOuter`
let sourceRecorder = lam.
  let calls = ref [] in
  let opts =
    { ssaFinalizeOptsUntyped () with
      joinParam = lam args.
        let kinds = map (lam s. if isDef s then 'd' else 'o') args.sources in
        modref calls (snoc (deref calls) (join [nameGetStr args.name, ":", kinds]))
    } in
  (opts, calls) in

let evalInt : Expr -> Int = lam tm.
  match tm with TmConst {val = CInt {val = i}} then i
  else error "evalInt: not an integer" in
let evalClosed : Expr -> Int = lam tm.
  let tm = typeCheck (symbolize tm) in
  evalInt (eval (evalCtxEmpty ()) tm) in
let run : SSABlock -> Expr -> Int = lam block. lam fall.
  evalClosed (ssaFinalize checked block fall) in
let unifications : SSABlock -> Expr -> Int = lam block. lam fall.
  match unifyCounter () with (opts, count) in
  ssaFinalize opts block fall;
  deref count in
let sources : SSABlock -> Expr -> [String] = lam block. lam fall.
  match sourceRecorder () with (opts, calls) in
  ssaFinalize opts block fall;
  deref calls in

let x = nameSym "x" in
let y = nameSym "y" in
let a = nameSym "a" in
let b = nameSym "b" in

-- Run with `x` bound to 5 outside the block
let runOuter : SSABlock -> Expr -> Int = lam block. lam fall.
  evalClosed (bind_ (nulet_ x (int_ 5)) (ssaFinalize checked block fall)) in

-- Straight-line rebinding
utest run
  (ssaSeq [ssaSet x (int_ 1), ssaSet x (addi_ (nvar_ x) (int_ 2))])
  (nvar_ x)
with 3 in

-- Parallel assignment sees old values
utest run
  (ssaSeq
    [ ssaSet x (int_ 1), ssaSet y (int_ 2)
    , ssaSetPar (mapFromSeq nameCmp [(x, nvar_ y), (y, nvar_ x)])
    ])
  (subi_ (nvar_ x) (nvar_ y))
with 1 in

-- Join after a match
let matchJoin = lam target.
  ssaSeq
    [ ssaSet x (int_ 0)
    , ssaMatch target (pint_ 1) (ssaSet x (int_ 10)) (ssaSet x (int_ 20))
    , ssaSet y (addi_ (nvar_ x) (int_ 1))
    ] in
utest run (matchJoin (int_ 1)) (nvar_ y) with 11 in
utest run (matchJoin (int_ 2)) (nvar_ y) with 21 in

-- Pattern variables remain bound after the match
let tup = utuple_ [int_ 1, int_ 2] in
let ptup = ptuple_ [npvar_ a, npvar_ b] in
utest run
  (ssaMatch tup ptup (ssaEmpty ()) (ssaReturn (int_ 0)))
  (addi_ (nvar_ a) (nvar_ b))
with 3 in
utest run
  (ssaMatchIrrefutable tup ptup (ssaEmpty ()))
  (addi_ (nvar_ a) (nvar_ b))
with 3 in

-- Loop exited via `ssaBlock`
let i = nameSym "i" in
let s = nameSym "s" in
let sumLoop = ssaSeq
  [ ssaSet i (int_ 0), ssaSet s (int_ 0)
  , ssaBlock (lam break. ssaLoop (ssaSeq
    [ ssaMatch (nvar_ i) (pint_ 10) break (ssaEmpty ())
    , ssaSet i (addi_ (nvar_ i) (int_ 1))
    , ssaSet s (addi_ (nvar_ s) (nvar_ i))
    ]))
  ] in
utest run sumLoop (nvar_ s) with 55 in

-- Loop exited via `ssaReturn`
utest run
  (ssaSeq
    [ ssaSet i (int_ 0)
    , ssaLoop (ssaSeq
      [ ssaMatch (eqi_ (nvar_ i) (int_ 5)) ptrue_ (ssaReturn (muli_ (nvar_ i) (int_ 100))) (ssaEmpty ())
      , ssaSet i (addi_ (nvar_ i) (int_ 1))
      ])
    ])
  (int_ 0)
with 500 in

-- The example from the documentation of `ssaCallCC`
utest run
  (ssaSeq
    [ ssaCallCC (lam continue.
        addi_ (continue (ssaReturn (int_ 1))) (continue (ssaEmpty ())))
    , ssaReturn (int_ 5) ])
  unit_
with 6 in

-- Continuations that write different variables
utest run
  (ssaSeq
    [ ssaSet x (int_ 1)
    , ssaCallCC (lam continue.
        addi_ (continue (ssaEmpty ())) (continue (ssaSet x (int_ 10))))
    ])
  (nvar_ x)
with 11 in

-- `construct` reads ssa-bound variables at the `ssaCallCC`
utest run
  (ssaSeq
    [ ssaSet x (int_ 1)
    , ssaCallCC (lam continue.
        addi_ (nvar_ x) (continue (ssaSet x (int_ 10))))
    ])
  (nvar_ x)
with 11 in

-- A read only in `construct` keeps a variable live across a join
utest run
  (ssaSeq
    [ ssaMatch (int_ 1) (pint_ 1) (ssaSet x (int_ 10)) (ssaSet x (int_ 20))
    , ssaCallCC (lam continue. addi_ (nvar_ x) (continue (ssaEmpty ())))
    ])
  (int_ 0)
with 10 in

-- Blocks passed to the continuation may read `construct`'s binders
utest run
  (ssaSeq
    [ ssaSet x (int_ 1)
    , ssaCallCC (lam continue.
        bind_ (nulet_ y (int_ 7)) (continue (ssaSet x (nvar_ y))))
    ])
  (nvar_ x)
with 7 in

-- Nested `ssaCallCC`
utest run
  (ssaSeq
    [ ssaSet x (int_ 1)
    , ssaCallCC (lam k1. k1 (ssaCallCC (lam k2. muli_ (k2 (ssaSet x (int_ 3))) (int_ 2))))
    ])
  (nvar_ x)
with 6 in

-- Escaping an `ssaBlock` from inside a continuation
utest run
  (ssaSeq
    [ ssaSet x (int_ 0)
    , ssaBlock (lam break. ssaSeq
      [ ssaCallCC (lam continue. continue (ssaSeq [ssaSet x (int_ 7), break]))
      , ssaSet x (int_ 100)
      ])
    ])
  (nvar_ x)
with 7 in

-- Law instances
let law = lam lhs. lam rhs. lam fall. eqi (run lhs fall) (run rhs fall) in

let c = ssaSet y (muli_ (nvar_ x) (int_ 10)) in
let ab = lam target.
  (ssaSet x (int_ 1), ssaSeq [ssaSet x (int_ 2), ssaMatch target (pint_ 0) (ssaReturn (int_ 0)) (ssaEmpty ())]) in
let matchChain = lam target.
  match ab target with (a, b) in
  law
    (ssaSeq [ssaSet y (int_ 0), ssaChain (ssaMatch target (pint_ 1) a b) c])
    (ssaSeq [ssaSet y (int_ 0), ssaMatch target (pint_ 1) (ssaChain a c) (ssaChain b c)])
    (nvar_ y) in
utest matchChain (int_ 0) with true in
utest matchChain (int_ 1) with true in
utest matchChain (int_ 2) with true in

let blockLaw = lam target.
  let f = lam l. ssaSeq [ssaSet x (int_ 1), ssaMatch target (pint_ 1) l (ssaEmpty ()), ssaSet x (int_ 2)] in
  law
    (ssaSeq [ssaSet x (int_ 0), ssaChain (ssaBlock f) c])
    (ssaSeq [ssaSet x (int_ 0), ssaChain (f (ssaChain c (ssaReturn (nvar_ y)))) c])
    (nvar_ y) in
utest blockLaw (int_ 1) with true in
utest blockLaw (int_ 2) with true in

-- Unification only happens for variables that are live after a join:
-- once per value passed to the parameter, and once for the read
let branches = ssaMatch (int_ 1) (pint_ 1) (ssaSet x (int_ 10)) (ssaSet x (int_ 20)) in
utest unifications (ssaSeq [ssaSet x (int_ 0), branches]) (int_ 0) with 0 in
utest unifications (ssaSeq [ssaSet x (int_ 0), branches]) (nvar_ x) with 3 in
utest unifications (ssaSeq [branches, ssaSet x (int_ 1)]) (nvar_ x) with 0 in
utest unifications (ssaSeq [ssaSet y (int_ 0), ssaLoop (ssaSet x (int_ 1))]) (int_ 0) with 0 in
utest unifications
  (ssaSeq [ssaSet x (int_ 0), ssaLoop (ssaSet x (addi_ (nvar_ x) (int_ 1)))])
  (int_ 0)
with 3 in

-- Variables bound outside the block: read, rebound, and read again
utest runOuter
  (ssaSet y (nvar_ x))
  (addi_ (muli_ (nvar_ y) (int_ 100)) (nvar_ x))
with 505 in
utest runOuter
  (ssaSeq [ssaSet y (nvar_ x), ssaSet x (addi_ (nvar_ x) (int_ 1))])
  (addi_ (muli_ (nvar_ y) (int_ 100)) (nvar_ x))
with 506 in

-- Rebinding an outer variable on only one path to a join
let oneBranch = lam target. ssaMatch target (pint_ 1) (ssaSet x (int_ 10)) (ssaEmpty ()) in
utest runOuter (oneBranch (int_ 1)) (nvar_ x) with 10 in
utest runOuter (oneBranch (int_ 2)) (nvar_ x) with 5 in
utest sources (oneBranch (int_ 1)) (nvar_ x) with ["x:do"] in

-- An outer variable rebound in a loop
let countTo8 = ssaBlock (lam brk. ssaLoop (ssaSeq
  [ ssaMatch (nvar_ x) (pint_ 8) brk (ssaEmpty ())
  , ssaSet x (addi_ (nvar_ x) (int_ 1)) ])) in
utest runOuter countTo8 (nvar_ x) with 8 in
utest sources countTo8 (nvar_ x) with ["x:do"] in

-- Writes on paths that don't reach a join don't make parameters
let returnWrite = lam target.
  ssaMatch target (pint_ 1)
    (ssaMatch target (pint_ 2) (ssaSeq [ssaSet x (int_ 1), ssaReturn (withType tyint_ (int_ 0))]) (ssaEmpty ()))
    (ssaEmpty ()) in
utest runOuter (returnWrite (int_ 1)) (nvar_ x) with 5 in
utest runOuter (returnWrite (int_ 2)) (nvar_ x) with 5 in
utest sources (returnWrite (int_ 1)) (nvar_ x) with [] in
let exitWrite = ssaBlock (lam brk. ssaLoop (ssaSeq
  [ ssaMatch (nvar_ x) (pint_ 6) (ssaSeq [ssaSet x (int_ 100), ssaReturn (nvar_ x)]) (ssaEmpty ())
  , ssaRun (nvar_ x)
  , brk ])) in
utest runOuter exitWrite (nvar_ x) with 5 in
utest sources exitWrite (nvar_ x) with [] in

-- `readInfo` is the syntactically first read after the join
let readInfos : SSABlock -> Expr -> [Info] = lam block. lam fall.
  let infos = ref [] in
  let opts = {checked with joinParam = lam args. modref infos (snoc (deref infos) args.readInfo)} in
  ssaFinalize opts block fall;
  deref infos in
let firstRead = infoVal "first" 1 0 1 1 in
let laterRead = infoVal "later" 2 0 2 1 in
utest readInfos
  (ssaSeq
    [ ssaMatch (int_ 1) (pint_ 1) (ssaSet x (int_ 10)) (ssaSet x (int_ 20))
    , ssaSet a (withInfo firstRead (nvar_ x))
    ])
  (withInfo laterRead (nvar_ x))
with [firstRead] using eqSeq (lam l. lam r. eqi (infoCmp l r) 0) in

-- Writes in earlier iterations of a loop reach an escape in a later one
utest run
  (ssaSeq
    [ ssaSet i (int_ 0)
    , ssaBlock (lam brk. ssaLoop (ssaSeq
      [ ssaMatch (nvar_ i) (pint_ 3) brk (ssaEmpty ())
      , ssaSet i (addi_ (nvar_ i) (int_ 1))
      ]))
    ])
  (nvar_ i)
with 3 in

-- With real unification variables, every join parameter gets a known
-- type
let tcenv = typcheckEnvDefault in
let typedOpts = ssaFinalizeOpts (unify tcenv) (newvar tcenv.currentLvl) in
let tint = lam tm. withType tyint_ tm in
let ix = tint (nvar_ x) in
recursive let lamTypes = lam acc. lam tm.
  let acc =
    match tm with TmLam t then
      if null (nameGetStr t.ident) then acc else snoc acc t.tyParam
    else acc in
  sfold_Expr_Expr lamTypes acc tm in
let paramTypes = lam block. lam fall.
  let tm = removeMetaVarExpr (ssaFinalize typedOpts block fall) in
  map (lam ty. match ty with TyInt _ then "int" else type2str ty) (lamTypes [] tm) in
utest paramTypes
  (ssaMatch (int_ 1) (pint_ 1) (ssaSet x (tint (int_ 10))) (ssaEmpty ()))
  ix
with ["int"] in
utest paramTypes
  (ssaBlock (lam brk. ssaLoop (ssaSeq
    [ ssaMatch ix (pint_ 8) brk (ssaEmpty ())
    , ssaSet x (tint (addi_ ix (tint (int_ 1)))) ])))
  ix
with ["int"] in
utest paramTypes (returnWrite (int_ 1)) ix with [] in

()
