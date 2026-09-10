-- Readability passes over the generated ECMAScript AST.
--
-- The MExpr the backend receives has already been through pattern lowering,
-- which introduces a binding per match scrutinee:
--
--     let _target = lti 1 2 in match _target with true then 1 else 0
--
-- Emitted literally that is `const _target = 1 < 2; env.print(_target ? ...)`.
-- Nothing is wrong with it, but the temporary carries no meaning, and the same
-- shape appears everywhere the lowerer touches. These passes remove it, along
-- with the bindings that record projection leaves behind.
--
-- Two rewrites, both local to a statement list:
--
--   * a pure, compiler-introduced binding used exactly once is inlined at its
--     use;
--   * a pure binding never used at all is dropped.
--
-- A binding is inlined when it is *either* compiler-introduced *or* trivial:
--
--   * compiler-introduced means a leading underscore in the MExpr name -- the
--     lowerer's `_target`, and the temporaries this backend creates;
--   * trivial means the initialiser is a variable or a field access path --
--     `x`, `r.x`, `r[0].y` -- where the value already has a name at least as
--     good as the one being bound.
--
-- Literals are deliberately not trivial: `const a = 1` names something that
-- had no name, and that name is information worth keeping.
--
-- A name the programmer wrote is otherwise left alone, even when inlining it
-- would be shorter: generated code is read while debugging, and a meaningful
-- name is worth more than one fewer line. Inlining everything would turn
-- `let c = addi a b in dprint c` into `env.dprint(1 + 2)`, which is smaller
-- and worse.
--
-- The triviality half is what cleans up record projection. Source `r.x` lowers
-- to a match binding every field, plus an alias:
--
--     match r with {x = field, y = field1} in let X = field in X
--
-- None of those names begin with an underscore, but `field1` is unused and the
-- other two are trivial aliases, so the whole thing collapses back to `r.x`.
--
-- Purity is what makes this safe. Duplicating or reordering a pure expression
-- cannot change behaviour, and MExpr values are immutable, so a pure
-- expression means the same thing wherever it is evaluated. An occurrence
-- inside a nested function or loop body disqualifies inlining even so: moving
-- a computation there would change how many times it runs.
--
-- One exception breaks that reasoning: tail-call elimination *assigns* to
-- function parameters. Reading such a parameter is no longer time-invariant,
-- so an initialiser that mentions a reassigned name is never moved. Without
-- that guard, the temporaries which make the rebinding simultaneous would be
-- inlined back into the assignments and a later argument would see an
-- already-updated parameter.

include "ecmascript/ast.mc"
include "name.mc"
include "option.mc"
include "seq.mc"

let esSum : [Int] -> Int = foldl addi 0

lang ESCleanup = ESAst

  ------------
  -- PURITY --
  ------------

  -- Whether evaluating the expression can be observed. Reading a property is
  -- pure because every object this backend emits is a plain record; building a
  -- closure is pure because only calling it does anything.
  sem esIsPure : ESExpr -> Bool
  sem esIsPure =
  | ESEVar _ | ESEGlobal _ | ESEInt _ | ESEFloat _ | ESEBool _ | ESEString _
  | ESEUndefined _ | ESENull _ | ESEArrow _ -> true
  | ESEArray t -> forAll esIsPure t.exprs
  | ESEObject t -> forAll (lam f. esIsPure f.1) t.fields
  | ESEObjectWith t ->
    and (esIsPure t.base) (forAll (lam f. esIsPure f.1) t.fields)
  | ESEMember t -> esIsPure t.obj
  | ESEIndex t -> and (esIsPure t.obj) (esIsPure t.index)
  | ESEBin t -> and (esIsPure t.lhs) (esIsPure t.rhs)
  | ESEUn t -> esIsPure t.arg
  | ESECond t -> and (esIsPure t.cond) (and (esIsPure t.thn) (esIsPure t.els))
  | ESEInstanceOf t -> and (esIsPure t.lhs) (esIsPure t.rhs)
  -- A call into the runtime is pure by construction: every `$`-prefixed
  -- helper is a deterministic function of its arguments. A call to anything
  -- else could do anything, including reaching `env`.
  | ESECall t ->
    match t.callee with ESEGlobal g then
      if match g.name with "$" ++ _ then true else false
      then forAll esIsPure t.args else false
    else false
  | ESENew _ -> false

  --------------
  -- COUNTING --
  --------------

  sem esCountExpr : Name -> ESExpr -> Int
  sem esCountExpr id =
  | ESEVar t -> if nameEq t.id id then 1 else 0
  | ESEGlobal _ | ESEInt _ | ESEFloat _ | ESEBool _ | ESEString _
  | ESEUndefined _ | ESENull _ -> 0
  | ESEArray t -> esSum (map (esCountExpr id) t.exprs)
  | ESEObject t -> esSum (map (lam f. esCountExpr id f.1) t.fields)
  | ESEObjectWith t ->
    addi (esCountExpr id t.base) (esSum (map (lam f. esCountExpr id f.1) t.fields))
  | ESEMember t -> esCountExpr id t.obj
  | ESEIndex t -> addi (esCountExpr id t.obj) (esCountExpr id t.index)
  | ESECall t ->
    addi (esCountExpr id t.callee) (esSum (map (esCountExpr id) t.args))
  | ESENew t ->
    addi (esCountExpr id t.callee) (esSum (map (esCountExpr id) t.args))
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then esCountExpr id b.expr
    case ESFBBlock b then esSum (map (esCountStmt id) b.stmts)
    end
  | ESEBin t -> addi (esCountExpr id t.lhs) (esCountExpr id t.rhs)
  | ESEUn t -> esCountExpr id t.arg
  | ESECond t ->
    addi (esCountExpr id t.cond)
      (addi (esCountExpr id t.thn) (esCountExpr id t.els))
  | ESEInstanceOf t -> addi (esCountExpr id t.lhs) (esCountExpr id t.rhs)

  sem esCountStmt : Name -> ESStmt -> Int
  sem esCountStmt id =
  | ESSConst t -> esCountExpr id t.init
  | ESSLet t -> optionMapOr 0 (esCountExpr id) t.init
  | ESSAssign t -> addi (esCountExpr id t.target) (esCountExpr id t.value)
  | ESSExpr t -> esCountExpr id t.expr
  | ESSReturn t -> optionMapOr 0 (esCountExpr id) t.expr
  | ESSThrow t -> esCountExpr id t.expr
  | ESSIf t ->
    addi (esCountExpr id t.cond)
      (addi (esSum (map (esCountStmt id) t.thn))
            (esSum (map (esCountStmt id) t.els)))
  | ESSBlock t -> esSum (map (esCountStmt id) t.stmts)
  | ESSWhile t ->
    addi (esCountExpr id t.cond) (esSum (map (esCountStmt id) t.body))
  | ESSFunDecl t -> esSum (map (esCountStmt id) t.body)
  | ESSClass _ | ESSContinue _ -> 0
  | ESSExportDefault t -> esCountStmt id t.stmt

  -- Occurrences that sit inside a nested function or loop body, where the
  -- number of evaluations is not fixed.
  sem esCountDeferredExpr : Name -> ESExpr -> Int
  sem esCountDeferredExpr id =
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then esCountExpr id b.expr
    case ESFBBlock b then esSum (map (esCountStmt id) b.stmts)
    end
  | e -> esSum (map (esCountDeferredExpr id) (esExprChildren e))

  sem esCountDeferredStmt : Name -> ESStmt -> Int
  sem esCountDeferredStmt id =
  | ESSFunDecl t -> esSum (map (esCountStmt id) t.body)
  | ESSWhile t ->
    addi (esCountDeferredExpr id t.cond) (esSum (map (esCountStmt id) t.body))
  | ESSIf t ->
    addi (esCountDeferredExpr id t.cond)
      (addi (esSum (map (esCountDeferredStmt id) t.thn))
            (esSum (map (esCountDeferredStmt id) t.els)))
  | ESSBlock t -> esSum (map (esCountDeferredStmt id) t.stmts)
  | ESSExportDefault t -> esCountDeferredStmt id t.stmt
  | ESSConst t -> esCountDeferredExpr id t.init
  | ESSLet t -> optionMapOr 0 (esCountDeferredExpr id) t.init
  | ESSAssign t ->
    addi (esCountDeferredExpr id t.target) (esCountDeferredExpr id t.value)
  | ESSExpr t -> esCountDeferredExpr id t.expr
  | ESSReturn t -> optionMapOr 0 (esCountDeferredExpr id) t.expr
  | ESSThrow t -> esCountDeferredExpr id t.expr
  | ESSClass _ | ESSContinue _ -> 0

  -- Immediate expression children, for traversals that do not care about the
  -- shape of the node they are visiting.
  sem esExprChildren : ESExpr -> [ESExpr]
  sem esExprChildren =
  | ESEVar _ | ESEGlobal _ | ESEInt _ | ESEFloat _ | ESEBool _ | ESEString _
  | ESEUndefined _ | ESENull _ | ESEArrow _ -> []
  | ESEArray t -> t.exprs
  | ESEObject t -> map (lam f. f.1) t.fields
  | ESEObjectWith t -> cons t.base (map (lam f. f.1) t.fields)
  | ESEMember t -> [t.obj]
  | ESEIndex t -> [t.obj, t.index]
  | ESECall t -> cons t.callee t.args
  | ESENew t -> cons t.callee t.args
  | ESEBin t -> [t.lhs, t.rhs]
  | ESEUn t -> [t.arg]
  | ESECond t -> [t.cond, t.thn, t.els]
  | ESEInstanceOf t -> [t.lhs, t.rhs]

  ------------------
  -- SUBSTITUTION --
  ------------------

  sem esSubstExpr : Name -> ESExpr -> ESExpr -> ESExpr
  sem esSubstExpr id repl =
  | ESEVar t -> if nameEq t.id id then repl else ESEVar t
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then
      ESEArrow { t with body = ESFBExpr { expr = esSubstExpr id repl b.expr } }
    case ESFBBlock b then
      ESEArrow { t with
        body = ESFBBlock { stmts = map (esSubstStmt id repl) b.stmts } }
    end
  | e -> smapESExprESExpr (esSubstExpr id repl) e

  sem esSubstStmt : Name -> ESExpr -> ESStmt -> ESStmt
  sem esSubstStmt id repl =
  | s ->
    let s = smapESStmtESExpr (esSubstExpr id repl) s in
    smapESStmtESStmt (esSubstStmt id repl) s

  -------------
  -- THE PASS --
  -------------

  sem esCleanupExpr : ESExpr -> ESExpr
  sem esCleanupExpr =
  -- A conditional on a literal picks its branch. Dropping the other arm is
  -- always safe: a ternary never evaluates it.
  | ESECond { cond = ESEBool b, thn = thn, els = els } ->
    esCleanupExpr (if b.value then thn else els)
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then
      ESEArrow { t with body = ESFBExpr { expr = esCleanupExpr b.expr } }
    case ESFBBlock b then
      ESEArrow { t with body = ESFBBlock { stmts = esCleanupStmts b.stmts } }
    end
  | e -> smapESExprESExpr esCleanupExpr e

  sem esCleanupStmt : ESStmt -> ESStmt
  sem esCleanupStmt =
  | ESSIf t ->
    ESSIf { t with cond = esCleanupExpr t.cond
          , thn = esCleanupStmts t.thn, els = esCleanupStmts t.els }
  | ESSBlock t -> ESSBlock { stmts = esCleanupStmts t.stmts }
  | ESSWhile t ->
    ESSWhile { t with cond = esCleanupExpr t.cond, body = esCleanupStmts t.body }
  | ESSFunDecl t -> ESSFunDecl { t with body = esCleanupStmts t.body }
  | ESSExportDefault t -> ESSExportDefault { stmt = esCleanupStmt t.stmt }
  | s -> smapESStmtESExpr esCleanupExpr s

  sem esCleanupStmts : [ESStmt] -> [ESStmt]
  sem esCleanupStmts =
  | stmts -> esInlineFix (map esCleanupStmt stmts)

  -- One pass is not enough: dropping a binding can lower another binding's use
  -- count below the inlining threshold, and the pass has already walked past
  -- it. Reading `n.inner.a` is the common case -- the record pattern names
  -- both fields of `inner`, so the scrutinee starts with two uses and only
  -- drops to one once the unused field binding is removed.
  --
  -- Each rewrite deletes exactly one statement, so the length strictly
  -- decreases and comparing lengths is a sound fixpoint test.
  sem esInlineFix : [ESStmt] -> [ESStmt]
  sem esInlineFix =
  | stmts ->
    let next = esInline stmts in
    if eqi (length next) (length stmts) then next else esInlineFix next

  -- Whether a binding was introduced by the compiler rather than written by
  -- the programmer. MExpr code that wants a name preserved in the output
  -- should not begin it with an underscore.
  sem esIsTemporary : Name -> Bool
  sem esIsTemporary =
  | id -> match nameGetStr id with "_" ++ _ then true else false

  -- A path rooted at a variable: `r`, `r.x`, `r[0].y`.
  sem esIsPath : ESExpr -> Bool
  sem esIsPath =
  | ESEVar _ | ESEGlobal _ -> true
  | ESEMember t -> esIsPath t.obj
  | ESEIndex t -> and (esIsPath t.obj) (esIsPathIndex t.index)
  | _ -> false

  -- An index cheap enough to duplicate along with the path.
  sem esIsPathIndex : ESExpr -> Bool
  sem esIsPathIndex =
  | ESEVar _ | ESEGlobal _ | ESEInt _ | ESEString _ -> true
  | _ -> false

  -- Whether binding the expression to a name conveys anything the expression
  -- does not already say. `const field = r.x` says no more than `r.x`, and
  -- `const rest = slice` no more than `slice`.
  sem esIsTrivial : ESExpr -> Bool
  sem esIsTrivial =
  | ESEVar _ -> true
  | ESEMember _ & e -> esIsPath e
  | ESEIndex _ & e -> esIsPath e
  | _ -> false

  -- Names assigned to somewhere in these statements. Reading one of them is
  -- position-dependent, so an expression that does is not safe to move.
  sem esAssignedStmt : ESStmt -> [Name]
  sem esAssignedStmt =
  | ESSAssign { target = ESEVar t } -> [t.id]
  | ESSIf t ->
    concat (join (map esAssignedStmt t.thn)) (join (map esAssignedStmt t.els))
  | ESSBlock t -> join (map esAssignedStmt t.stmts)
  | ESSWhile t -> join (map esAssignedStmt t.body)
  | ESSFunDecl t -> join (map esAssignedStmt t.body)
  | ESSExportDefault t -> esAssignedStmt t.stmt
  | _ -> []

  -- `let x; if (c) { x = a; } else { x = b; }` is a ternary written long-hand.
  --
  -- The compiler cannot always spot this itself: a pattern that binds
  -- something puts those bindings in the `then` arm, so the arms are not yet
  -- single assignments when the branch is built. Once inlining has removed
  -- the bindings they are, and this recovers the ternary. Dropping the untaken
  -- arm is safe because a ternary never evaluates it.
  sem esFoldBranch : [ESStmt] -> Option [ESStmt]
  sem esFoldBranch =
  | [ESSLet { id = id, init = None _ }, ESSIf t] ++ rest ->
    match (t.thn, t.els) with ([ESSAssign a], [ESSAssign b]) then
      match (a.target, b.target) with (ESEVar av, ESEVar bv) then
        if and (nameEq av.id id) (nameEq bv.id id) then
          Some (cons (ESSConst { id = id, init = ESECond
                { cond = t.cond, thn = a.value, els = b.value } }) rest)
        else None ()
      else None ()
    else None ()
  | _ -> None ()

  sem esInline : [ESStmt] -> [ESStmt]
  sem esInline =
  | [] -> []
  | [ESSConst { id = id, init = e } & s] ++ rest ->
    if not (esIsPure e) then cons s (esInline rest)
    else
      let uses = esSum (map (esCountStmt id) rest) in
      let deferred = esSum (map (esCountDeferredStmt id) rest) in
      -- A use in the condition of the very next `if` is evaluated before
      -- anything in its arms, so assignments inside them cannot affect it.
      -- Without this, every scrutinee temporary inside a tail-call loop would
      -- survive, since the loop assigns to the parameters it reads.
      let inNextCond =
        match rest with [ESSIf t] ++ _ then eqi (esCountExpr id t.cond) 1
        else false in
      let movable = or inNextCond
        (not (any (lam n. gti (esCountExpr n e) 0)
                (join (map esAssignedStmt rest)))) in
      if and (eqi uses 0) movable then esInline rest
      else if and movable
                 (and (or (esIsTemporary id) (esIsTrivial e))
                      (and (eqi uses 1) (eqi deferred 0))) then
        esInline (map (esSubstStmt id e) rest)
      else cons s (esInline rest)
  | [s] ++ rest ->
    match esFoldBranch (cons s rest) with Some folded then esInline folded
    else cons s (esInline rest)

  sem esCleanupProg : ESProg -> ESProg
  sem esCleanupProg =
  | ESProg t -> ESProg { t with stmts = esCleanupStmts t.stmts }

end

mexpr

use ESCleanup in

let a = nameSym "_a" in
let b = nameSym "b" in
let va = ESEVar { id = a } in
let vb = ESEVar { id = b } in
let lt = ESEBin { op = ESOLt {}, lhs = ESEInt { value = 1 }, rhs = ESEInt { value = 2 } } in
let call = lam f. ESECall { callee = ESEVar { id = f }, args = [] } in

utest esIsPure lt with true in
utest esIsPure (call a) with false in
utest esIsPure (ESEMember { obj = va, prop = "x" }) with true in
utest esIsPure (ESEArray { exprs = [lt, call a] }) with false in

-- A field access is inlined whatever the binding is called, since the path
-- already names the value. This is what collapses record projection.
let obj = nameSym "r" in
let field = nameSym "field" in
utest esCleanupStmts
  [ ESSConst { id = field, init = ESEMember { obj = ESEVar { id = obj }, prop = "x" } }
  , ESSReturn { expr = Some (ESEVar { id = field }) } ]
with [ ESSReturn { expr = Some (ESEMember { obj = ESEVar { id = obj }, prop = "x" }) } ] in

-- A bare variable is trivial: an alias adds no name the value did not have.
let src = nameSym "src" in
let dst = nameSym "dst" in
utest esCleanupStmts
  [ ESSConst { id = dst, init = ESEVar { id = src } }
  , ESSReturn { expr = Some (ESEVar { id = dst }) } ]
with [ ESSReturn { expr = Some (ESEVar { id = src }) } ] in

-- A call into the runtime is pure, so an unused one is dropped.
utest esCleanupStmts
  [ ESSConst { id = dst, init = ESECall
      { callee = ESEGlobal { name = "$splitAt" }, args = [ESEVar { id = src }] } }
  , ESSReturn { expr = Some (ESEInt { value = 1 }) } ]
with [ ESSReturn { expr = Some (ESEInt { value = 1 }) } ] in

-- A conditional on a literal folds away.
utest esCleanupStmts
  [ ESSReturn { expr = Some (ESECond { cond = ESEBool { value = false }
              , thn = ESEInt { value = 1 }, els = ESEInt { value = 0 } }) } ]
with [ ESSReturn { expr = Some (ESEInt { value = 0 }) } ] in

-- A literal is not trivial: naming it is information.
let one = nameSym "one" in
utest esCleanupStmts
  [ ESSConst { id = one, init = ESEInt { value = 1 } }
  , ESSReturn { expr = Some (ESEVar { id = one }) } ]
with [ ESSConst { id = one, init = ESEInt { value = 1 } }
     , ESSReturn { expr = Some (ESEVar { id = one }) } ] in

-- A binding the programmer wrote is left alone when its initialiser actually
-- computes something.
let named = nameSym "sum" in
utest esCleanupStmts
  [ ESSConst { id = named, init = lt }
  , ESSReturn { expr = Some (ESEVar { id = named }) } ]
with [ ESSConst { id = named, init = lt }
     , ESSReturn { expr = Some (ESEVar { id = named }) } ] in

-- A pure compiler temporary used once is inlined at the use.
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }
  , ESSExpr { expr = ESECond { cond = va, thn = ESEInt { value = 1 }
                             , els = ESEInt { value = 0 } } } ]
with [ ESSExpr { expr = ESECond { cond = lt, thn = ESEInt { value = 1 }
                                , els = ESEInt { value = 0 } } } ] in

-- A pure binding never used is dropped.
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }, ESSReturn { expr = Some (ESEInt { value = 1 }) } ]
with [ ESSReturn { expr = Some (ESEInt { value = 1 }) } ] in

-- Used twice: kept, since inlining would duplicate the computation.
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }
  , ESSReturn { expr = Some (ESEBin { op = ESOAnd {}, lhs = va, rhs = va }) } ]
with [ ESSConst { id = a, init = lt }
     , ESSReturn { expr = Some (ESEBin { op = ESOAnd {}, lhs = va, rhs = va }) } ] in

-- An impure binding is kept even when used once: the call must still happen,
-- and exactly where it was written.
utest esCleanupStmts
  [ ESSConst { id = a, init = call b }, ESSReturn { expr = Some va } ]
with [ ESSConst { id = a, init = call b }, ESSReturn { expr = Some va } ] in

-- Used once, but inside a function body: not inlined, since that would change
-- how often it is evaluated.
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }
  , ESSFunDecl { id = b, params = [], body = [ESSReturn { expr = Some va }] } ]
with [ ESSConst { id = a, init = lt }
     , ESSFunDecl { id = b, params = [], body = [ESSReturn { expr = Some va }] } ] in

-- Inlining inside a branch is fine: it happens at most once.
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }
  , ESSIf { cond = ESEBool { value = true }
          , thn = [ESSReturn { expr = Some va }], els = [] } ]
with [ ESSIf { cond = ESEBool { value = true }
             , thn = [ESSReturn { expr = Some lt }], els = [] } ] in

-- Dropping an unused binding can expose another for inlining, which a single
-- left-to-right pass would miss. This is the `n.inner.a` shape.
let inner = nameSym "_t" in
let fa = nameSym "fa" in
let fb = nameSym "fb" in
let outer = nameSym "n" in
utest esCleanupStmts
  [ ESSConst { id = inner, init = ESEMember { obj = ESEVar { id = outer }, prop = "inner" } }
  , ESSConst { id = fa, init = ESEMember { obj = ESEVar { id = inner }, prop = "a" } }
  , ESSConst { id = fb, init = ESEMember { obj = ESEVar { id = inner }, prop = "b" } }
  , ESSReturn { expr = Some (ESEVar { id = fa }) } ]
with [ ESSReturn { expr = Some (ESEMember
       { obj = ESEMember { obj = ESEVar { id = outer }, prop = "inner" }
       , prop = "a" }) } ] in

-- A `let` plus a two-armed assignment is a ternary written long-hand.
let vx = nameSym "_v" in
let cnd = nameSym "c" in
utest esCleanupStmts
  [ ESSLet { id = vx, init = None () }
  , ESSIf { cond = ESEVar { id = cnd }
          , thn = [ESSAssign { target = ESEVar { id = vx }, value = ESEInt { value = 1 } }]
          , els = [ESSAssign { target = ESEVar { id = vx }, value = ESEInt { value = 0 } }] }
  , ESSReturn { expr = Some (ESEVar { id = vx }) } ]
with [ ESSReturn { expr = Some (ESECond { cond = ESEVar { id = cnd }
       , thn = ESEInt { value = 1 }, els = ESEInt { value = 0 } }) } ] in

-- A scrutinee used in the next `if` condition is inlined even when the arms
-- assign to what it reads: the condition is evaluated first.
let p = nameSym "_p" in
let cnd2 = nameSym "_c" in
utest esCleanupStmts
  [ ESSConst { id = cnd2, init = ESEBin { op = ESOLt {}
      , lhs = ESEVar { id = p }, rhs = ESEInt { value = 1 } } }
  , ESSIf { cond = ESEVar { id = cnd2 }
          , thn = [ESSReturn { expr = Some (ESEInt { value = 0 }) }]
          , els = [ESSAssign { target = ESEVar { id = p }
                             , value = ESEInt { value = 2 } }] } ]
with [ ESSIf { cond = ESEBin { op = ESOLt {}
             , lhs = ESEVar { id = p }, rhs = ESEInt { value = 1 } }
             , thn = [ESSReturn { expr = Some (ESEInt { value = 0 }) }]
             , els = [ESSAssign { target = ESEVar { id = p }
                                , value = ESEInt { value = 2 } }] } ] in

-- An initialiser reading a name that is assigned later is otherwise never
-- moved. Tail call elimination relies on this: the temporaries exist precisely
-- so that parameters are rebound simultaneously.
let n = nameSym "_n" in
let acc = nameSym "acc" in
let t1 = nameSym "_arg" in
utest esCleanupStmts
  [ ESSConst { id = t1, init = ESEBin { op = ESOSub {}
      , lhs = ESEVar { id = n }, rhs = ESEInt { value = 1 } } }
  , ESSAssign { target = ESEVar { id = n }, value = ESEVar { id = t1 } }
  , ESSContinue {} ]
with [ ESSConst { id = t1, init = ESEBin { op = ESOSub {}
       , lhs = ESEVar { id = n }, rhs = ESEInt { value = 1 } } }
     , ESSAssign { target = ESEVar { id = n }, value = ESEVar { id = t1 } }
     , ESSContinue {} ] in

-- Chained: inlining one binding exposes the next.
let c = nameSym "_c" in
utest esCleanupStmts
  [ ESSConst { id = a, init = lt }
  , ESSConst { id = c, init = ESEUn { op = ESONot {}, arg = va } }
  , ESSReturn { expr = Some (ESEVar { id = c }) } ]
with [ ESSReturn { expr = Some (ESEUn { op = ESONot {}, arg = lt }) } ] in

()
