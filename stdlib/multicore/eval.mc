-- Evaluation rules for the multicore language fragments.

include "multicore/ast.mc"
include "mexpr/eval.mc"

lang AtomicEval = AtomicAst + IntAst + BoolAst + UnknownTypeAst
  syn Const =
  | CAtomicRef {ref : ARef Expr}
  | CAtomicRefInt {ref : ARef Int}
  | CAtomicExchange2 (ARef Expr)
  | CAtomicExchangeInt2 (ARef Int)
  | CAtomicFetchAndAdd2 (ARef Int)
  | CAtomicCASInt2 (ARef Int)
  | CAtomicCASInt3 (ARef Int, Int)

  sem delta (arg : Expr) =
  | CAtomicMake _ ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CAtomicRefInt {ref = atomicMake i}}
    else
      TmConst {val = CAtomicRef {ref = atomicMake arg}, info = NoInfo()}
  | CAtomicGet _ ->
    match arg with TmConst {val = CAtomicRef {ref = r}} then
      atomicGet r
    else match arg with TmConst ({val = CAtomicRefInt {ref = r}} & t) then
      TmConst {t with val = CInt {val = atomicGet r}}
    else error "argument to atomicGet not an atomic reference"
  | CAtomicExchange _ ->
    match arg with TmConst ({val = CAtomicRef {ref = r}} & t) then
      TmConst {t with val = CAtomicExchange2 r}
    else match arg with TmConst ({val = CAtomicRefInt {ref = r}} & t) then
      TmConst {t with val = CAtomicExchangeInt2 r}
    else error "first argument to atomicExchange not an atomic reference"
  | CAtomicExchange2 r ->
    atomicExchange r arg
  | CAtomicExchangeInt2 r ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CInt {val = atomicExchange r i}}
    else error "second argument to atomicExchange not an integer"
  | CAtomicFetchAndAdd _ ->
    match arg with TmConst ({val = CAtomicRefInt {ref = r}} & t) then
      TmConst {t with val = CAtomicFetchAndAdd2 r}
    else error
       "first argument to atomicFetchAndAdd not an integer atomic reference"
  | CAtomicFetchAndAdd2 r ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CInt {val = atomicFetchAndAdd r i}}
    else error "second argument to atomicFetchAndAdd not an integer"
  | CAtomicCAS _ ->
    match arg with TmConst ({val = CAtomicRefInt {ref = r}} & t) then
      TmConst {t with val = CAtomicCASInt2 r}
    else error "first argument to atomicCAS not an integer atomic reference"
  | CAtomicCASInt2 r ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CAtomicCASInt3 (r, i)}
    else error "second argument to atomicCAS not an integer"
  | CAtomicCASInt3 (r, seen) ->
    match arg with TmConst ({val = CInt {val = i}} & t) then
      TmConst {t with val = CBool {val = atomicCAS r seen i}}
    else error "third argument to atomicCAS not an integer"
end

lang ThreadEval = ThreadAst + IntAst + UnknownTypeAst + RecordAst + AppEval
  syn Const =
  | CThread {thread : Thread Expr}
  | CThreadID {id : Tid}

  sem delta (arg : Expr) =
  | CThreadSpawn _ ->
    let app =
      TmApp {lhs = arg, rhs = unit_, info = NoInfo (), ty = TyUnknown ()}
    in
    TmConst {val = CThread {thread = threadSpawn (lam. eval {env = []} app)}
            , info = NoInfo ()
            , ty = TyUnknown ()
            }
  | CThreadJoin _ ->
    match arg with TmConst {val = CThread {thread = thread}} then
      threadJoin thread
    else error "not a threadJoin of a thread"
  | CThreadSelf _ ->
    match arg with TmRecord {bindings = []} then
      TmConst {val = CThreadID {id = threadSelf ()},
               info = NoInfo (), ty = TyUnknown ()}
    else error "Argument in threadSelf is not unit"
  | CThreadGetID _ ->
    match arg with TmConst ({val = CThread {thread = thread}} & t) then
      TmConst {t with val = CThreadID {id = threadGetID thread}}
    else error "Argument in threadGetID is not a thread"
  | CThreadID2Int _ ->
    match arg with TmConst ({val = CThreadID {id = id}} & t) then
      TmConst {t with val = CInt {val = threadID2int id}}
    else error "Argument to threadID2int not a thread ID"
  | CThreadWait _ ->
    match arg with TmRecord {bindings = []} then
      threadWait ();
      unit_
    else error "Argument to threadWait is not unit"
  | CThreadNotify _ ->
    match arg with TmConst ({val = CThreadID {id = id}} & t) then
      threadNotify id;
      unit_
    else error "Argument to threadNotify not a thread ID"
  | CThreadCriticalSection _ ->
    let app =
      TmApp {lhs = arg, rhs = unit_, info = NoInfo (), ty = TyUnknown ()}
    in threadCriticalSection (lam. eval {env = []} app)
  | CThreadCPURelax _ ->
    match arg with TmRecord {bindings = []} then
      threadCPURelax ();
      unit_
    else error "Argument to threadCPURelax is not unit"
end

lang MExprParEval = MExprEval + AtomicEval + ThreadEval + MExprPrettyPrint

mexpr

use MExprParEval in

-- Evaluation shorthand used in tests below
let eval =
  lam t. eval {env = assocEmpty} (symbolize t) in

-- Atomic references
let p = ulet_ "r" (atomicMake_ (int_ 0)) in
utest eval (bind_ p (atomicGet_ (var_ "r"))) with int_ 0 in
utest eval (bind_ p (atomicExchange_ (var_ "r") (int_ 1))) with int_ 0 in
utest eval (bind_ p (bindall_
  [ ulet_ "_" (atomicExchange_ (var_ "r") (int_ 1))
  , atomicExchange_ (var_ "r") (int_ 2)
  ]))
with int_ 1 in
utest eval (bind_ p (atomicFetchAndAdd_ (var_ "r") (int_ 3))) with int_ 0 in
utest eval (bind_ p (atomicCAS_ (var_ "r") (int_ 0) (int_ 1))) with true_ in

let p = ulet_ "r" (atomicMake_ (float_ 0.0)) in
utest eval (bind_ p (atomicGet_ (var_ "r"))) with float_ 0.0 in
utest eval (bind_ p (atomicExchange_ (var_ "r") (float_ 1.0))) with float_ 0.0 in
utest eval (bind_ p (bindall_
  [ ulet_ "_" (atomicExchange_ (var_ "r") (float_ 1.0))
  , atomicExchange_ (var_ "r") (float_ 2.0)
  ]))
with float_ 1.0 in

utest eval (bindall_
  [ ucondef_ "Foo"
  , ulet_ "r" (atomicMake_ (conapp_ "Foo" (int_ 1)))
  , ulet_ "foo2" (conapp_ "Foo" (int_ 2))
  , ulet_ "foo1" (atomicExchange_ (var_ "r") (var_ "foo2"))
  , match_ (var_ "foo1") (pcon_ "Foo" (pint_ 1)) true_ false_
  ]
)
with true_ in

-- Threads
utest eval (bindall_
  [ ulet_ "v" (int_ 43)
  , ulet_ "t" (threadSpawn_ (ulam_ "_" (addi_ (var_ "v") (int_ 1))))
  , threadJoin_ (var_ "t")
  ])
with int_ 44 in

utest eval (bindall_
  [ ulet_ "t" (threadSpawn_ (TmConst {val = CThreadSelf {}, ty = TyUnknown (), info = NoInfo ()}))
  , ulet_ "tid" (threadGetID_ (var_ "t"))
  , eqi_ (threadID2Int_ (var_ "tid")) (threadID2Int_ (threadJoin_ (var_ "t")))
  ])
with true_ in

let waitForFlag = ureclet_ "waitForFlag" (ulam_ "flag"
  (if_ (atomicGet_ (var_ "flag"))
       unit_
       (bind_
          (ulet_ "_" (threadCPURelax_ unit_))
          (app_ (var_ "waitForFlag") (var_ "flag")))))
in

utest eval (bindall_
  [ ulet_ "inCriticalSection" (atomicMake_ false_)
  , ulet_ "afterWait" (atomicMake_ false_)
  , ulet_ "t" (threadSpawn_ (ulam_ "_" (threadCriticalSection_
      (ulam_ "_" (
        bindall_
          [ ulet_ "_" (atomicExchange_ (var_ "inCriticalSection") true_)
          , ulet_ "_" (threadWait_ unit_)
          , ulet_ "_" (sleepMs_ (int_ 100))
          , ulet_ "_" (atomicExchange_ (var_ "afterWait") true_)
          , int_ 42
          ])))))
  , waitForFlag
  , ulet_ "_" (app_ (var_ "waitForFlag") (var_ "inCriticalSection"))
  , ulet_ "v1" (atomicGet_ (var_ "afterWait"))
  , ulet_ "_" (threadNotify_ (threadGetID_ (var_ "t")))
  , ulet_ "v2" (atomicGet_ (var_ "afterWait"))
  , seq_ [var_ "v1", var_ "v2", threadJoin_ (var_ "t")]
  ])
with seq_ [false_, true_, int_ 42] in

()
