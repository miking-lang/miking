include "map.mc"
include "set.mc"
include "log.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/pprint.mc"
include "mexpr/boot-parser.mc"
include "mexpr/side-effect.mc"

let astBuilder = lam info.
  use MExprAst in
  let tyunknown_ = TyUnknown { info = info } in
  let uconst = lam c. TmConst { val = c, info = info, ty = tyunknown_ } in
  let app = tmApp info tyunknown_ in
  let app2 = lam f. lam a. lam b. app (app f a) b in
  {
    app = app,
    app2 = app2,
    appSeq = foldl (tmApp info tyunknown_),
    uconst = uconst,
    nulam = lam id. lam body. tmLam info tyunknown_ id tyunknown_ body,
    var = lam id. TmVar {
      ident = id,
      info = info,
      ty = tyunknown_,
      frozen = false
    },
    nulet = lam id. lam body. TmLet {
      ident = id,
      tyAnnot = tyunknown_,
      tyBody = tyunknown_,
      body = body,
      inexpr = uunit_,
      ty = tyunknown_,
      info = info
    },
    int = lam n. uconst (CInt { val = n }),
    muli = app2 (uconst (CMuli ())),
    negi = app (uconst (CNegi ())),
    float = lam f. uconst (CFloat { val = f }),
    mulf = app2 (uconst (CMulf ())),
    negf = app (uconst (CNegf ()))
  }

lang PEvalCtx = Eval + SideEffect
  type PEvalCtx = {
    env : EvalEnv,
    freeVar : Set Name,
    effectEnv : SideEffectEnv,
    maxRecDepth : Int
  }

  sem pevalCtxEmpty : () -> PEvalCtx
  sem pevalCtxEmpty =| _ -> {
    env = evalEnvEmpty (),
    freeVar = setEmpty nameCmp,
    effectEnv = sideEffectEnvEmpty (),
    maxRecDepth = 2
  }
end

lang PEval = PEvalCtx + Eval + PrettyPrint
  sem peval : Expr -> Expr
  sem peval =| t -> pevalExpr (pevalCtxEmpty ()) t

  sem pevalExpr : PEvalCtx -> Expr -> Expr
  sem pevalExpr ctx =| t -> pevalReadback (pevalBind ctx (lam x. x) t)

  sem pevalIsValue : Expr -> Bool
  sem pevalIsValue =
  | t ->
    errorSingle [infoTm t] (join ["pevalIsValue: undefined for:\n", expr2str t])

  sem pevalBind : PEvalCtx -> (Expr -> Expr) -> Expr -> Expr
  sem pevalBind ctx k =| t ->
    pevalEval ctx
      (lam t.
        if pevalIsValue t then k t
        else
          let b = astBuilder (infoTm t) in
          let ident = nameSym "t" in
          bind_ (b.nulet ident t) (k (b.var ident)))
      t

  sem pevalEval : PEvalCtx -> (Expr -> Expr) -> Expr -> Expr
  sem pevalEval ctx k =
  | t -> errorSingle [infoTm t] (join ["peval: undefined for:\n", expr2str t])

  sem pevalReadback : Expr -> Expr
  sem pevalReadback =| t -> pevalReadbackExpr (pevalCtxEmpty ()) t

  sem pevalReadbackExpr : PEvalCtx -> Expr -> Expr
  sem pevalReadbackExpr ctx =| t -> (pevalReadbackH ctx t).1

  sem pevalReadbackH : PEvalCtx -> Expr -> (PEvalCtx, Expr)
  sem pevalReadbackH ctx =| t -> smapAccumL_Expr_Expr pevalReadbackH ctx t
end

lang AppPEval = PEval + AppAst
  sem pevalIsValue =
  | TmApp _ -> false

  sem pevalApply : Info -> PEvalCtx -> (Expr -> Expr) -> (Expr, Expr) -> Expr
  sem pevalApply info ctx k =
  | (f, arg) ->
    errorSingle [info]
      (join [
        "Bad application between:\n",
        expr2str f,
        "\nand:\n",
        expr2str arg
      ])

  sem pevalEval ctx k =
  | TmApp r ->
    pevalBind ctx
      (lam lhs.
        pevalBind ctx
          (lam rhs. pevalApply r.info ctx k (lhs, rhs))
          r.rhs)
      r.lhs
end

lang VarPEval = PEval + VarAst + AppPEval
  sem pevalIsValue =
  | TmVar _ -> true

  sem pevalApply info ctx k =
  | (f & TmVar _, arg) -> k (app_ f arg)

  sem pevalEval ctx k =
  | t & TmVar r ->
    match evalEnvLookup r.ident ctx.env with Some t then k t
    else k t

  sem pevalReadbackH ctx =
  | t & TmVar r -> ({ ctx with freeVar = setInsert r.ident ctx.freeVar }, t)
end

lang LamPEval = PEval + LamAst + ClosAst + AppEval
  sem pevalIsValue =
  | TmClos _ -> true

  sem pevalApply info ctx k =
  | (TmClos r, arg) ->
    pevalEval { ctx with env = evalEnvInsert r.ident arg (r.env ()) } k r.body

  sem pevalEval ctx k =
  | TmLam r ->
    k (TmClos { ident = r.ident, body = r.body, env = lam. ctx.env, info = r.info })
  | TmClos r -> k (TmClos r)

  sem pevalReadbackH ctx =
  | TmClos r ->
    match
      pevalReadbackH
        ctx (pevalBind { ctx with env = r.env () } (lam x. x) r.body)
      with (ctx, body)
    in
    let b = astBuilder r.info in
    (ctx, b.nulam r.ident body)
end

lang LetPEval = PEval + LetAst
  sem pevalIsValue =
  | TmLet _ -> false

  sem pevalEval ctx k =
  | TmLet r ->
    pevalBind ctx
      (lam body.
        if pevalIsValue body then
          pevalBind
            { ctx with env = evalEnvInsert r.ident body ctx.env } k r.inexpr
        else
          TmLet { r with body = body, inexpr = pevalBind ctx k r.inexpr })
      r.body

  sem pevalReadbackH ctx =
  | TmLet r ->
    match pevalReadbackH ctx r.inexpr with (inexprCtx, inexpr) in
    match pevalReadbackH inexprCtx r.body with (ctx, body) in
    if setMem r.ident inexprCtx.freeVar then
      (ctx, TmLet { r with body = body, inexpr = inexpr })
    else
      if exprHasSideEffect ctx.effectEnv body then
        (ctx, TmLet { r with body = body, inexpr = inexpr })
      else
        (inexprCtx, inexpr)
end

lang RecLetsPEval = PEval + RecLetsAst + ClosAst + LamAst
  sem pevalIsValue =
  | TmRecLets _ -> false

  sem pevalEval ctx k =
  | TmRecLets r ->
    recursive let envPrime : Int -> Lazy EvalEnv = lam n. lam.
      let wraplambda = lam n. lam bind.
        if geqi n ctx.maxRecDepth then TmVar {
          ident = bind.ident,
          info = bind.info,
          ty = bind.tyBody,
          frozen = false
        }
        else
          match bind.body with TmLam r then TmClos {
            ident = r.ident,
            body = r.body,
            env = envPrime (succ n),
            info = r.info
          }
          else
            errorSingle [infoTm bind.body]
              "Right-hand side of recursive let must be a lambda"
      in
      foldl
        (lam env. lam bind.
          evalEnvInsert bind.ident (wraplambda n bind) env)
        ctx.env r.bindings
    in
    let bindings =
      map
        (lam bind. { bind with body = pevalBind ctx (lam x. x) bind.body })
        r.bindings
    in
    TmRecLets {
      r with
      bindings = bindings,
      inexpr = pevalBind { ctx with env = envPrime 0 () } k r.inexpr
    }

  sem pevalReadbackH ctx =
  | TmRecLets r ->
    let fv = setOfSeq nameCmp (map (lam bind. bind.ident) r.bindings) in
    match pevalReadbackH ctx r.inexpr with (inexprCtx, inexpr) in
    if
      forAll (lam bind. not (setMem bind.ident inexprCtx.freeVar)) r.bindings
    then
      (inexprCtx, inexpr)
    else
      let ctx = { inexprCtx with freeVar = setUnion inexprCtx.freeVar fv } in
    match
      mapAccumL
        (lam ctx. lam bind.
          match pevalReadbackH ctx bind.body with (bodyCtx, body) in
          (bodyCtx, { bind with body = body }))
        ctx
        r.bindings
      with (ctx, bindings)
    in
    (ctx, TmRecLets { r with bindings = bindings, inexpr = inexpr })
end

lang RecordPEval = PEval + RecordAst + VarAst
  sem pevalIsValue =
  -- NOTE(oerikss, 2022-02-15): We do not have to check inside the record as the
  -- bindings vill always bind to values after the PEval transformation.
  | TmRecord _ -> true
  | TmRecordUpdate _ -> false

  sem pevalEval ctx k =
  | TmRecord r ->
    mapMapK
      (lam t. lam k. pevalBind ctx k t)
      r.bindings
      (lam bs. k (TmRecord { r with bindings = bs }))
  | TmRecordUpdate r1 ->
    pevalBind ctx
      (lam rec.
        pevalBind ctx
          (lam value.
            switch rec
            case TmRecord r2 then
              let r2 =
                { r2 with bindings = mapInsert r1.key value r2.bindings }
              in
              k (TmRecord r2)
            case TmVar _ then
              k (TmRecordUpdate { r1 with rec = rec, value = value })
            end)
          r1.value)
      r1.rec
end

lang SeqPEval = PEval + SeqAst
  -- NOTE(oerikss, 2022-02-15): We do not have to check inside the sequences as the
  -- elements vill always be values in the PEval transformation.
  sem pevalIsValue =
  | TmSeq _ -> true

  sem pevalEval ctx k =
  | TmSeq r ->
    mapK
      (lam t. lam k. pevalBind ctx k t)
      r.tms
      (lam tms. k (TmSeq { r with tms = tms }))
end

lang ConstPEval = PEval + ConstEval
  sem pevalReadbackH ctx =
  | TmConstApp r ->
    match mapAccumL pevalReadbackH ctx r.args with (ctx, args) in
    let b = astBuilder r.info in
    (ctx, b.appSeq (b.uconst r.const) args)

  sem pevalIsValue =
  | TmConst _ -> true
  | TmConstApp _ -> true
  -- NOTE(oerikss, 2022-02-15): We treat partially applied constants as
  -- values. We then have to make sure to transform these to normal TmApp's to
  -- avoid re-computations when we see that we cannot statically evaluate the
  -- constant.

  sem pevalEval ctx k =
  | t & (TmConst _ | TmConstApp _) -> k t

  sem pevalApply info ctx k =
  | (TmConst r, arg) -> k (delta info (r.val, [arg]))
  | (TmConstApp r, arg) -> k (delta info (r.const, snoc r.args arg))
end

lang MatchPEval = PEval + MatchEval + NeverAst + VarAst
  sem pevalIsValue =
  | TmMatch _ -> false

  sem pevalEval ctx k =
  | TmMatch r ->
    pevalBind ctx
      (lam target.
        switch target
        case TmVar _ then
          k (TmMatch {r with
                      target = target,
                      thn = pevalBind ctx (lam x. x) r.thn,
                      els = pevalBind ctx (lam x. x) r.els
          })
        case t & TmNever _ then k t
        case _ then
          match tryMatch ctx.env target r.pat with Some env then
            pevalBind { ctx with env = env } k r.thn
          else pevalBind ctx k r.els
        end)
      r.target
end

lang NeverPEval = PEval + NeverAst
  sem pevalIsValue =
  | TmNever _ -> true

  sem pevalEval ctx k =
  | t & TmNever _ -> k t

  sem pevalApply info ctx k =
  | (t & TmNever _, _) -> k t
end

lang ArithIntPEval = ArithIntEval + VarAst
  sem delta info =
  | (c & (CAddi _ | CMuli _), args & [TmVar _, TmConst _]) ->
    -- NOTE(oerikss, 2022-02-15): We move constants to the lhs for associative
    -- operators to make later simplifications easier.
    delta info (c, reverse args)
  | (c & CAddi _, args & [TmConst {val = CInt x}, y & TmVar _]) ->
    if eqi x.val 0 then y
    else
      let b = astBuilder info in
      b.appSeq (b.uconst c) args
  | (c & CAddi _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.muli (b.int 2) y
    else b.appSeq (b.uconst c) [x, y]
  | (c & CMuli _, args & [TmConst {val = CInt x}, y & TmVar _]) ->
    let b = astBuilder info in
    switch x.val
    case 0 then b.int 0
    case 1 then y
    case _ then b.appSeq (b.uconst c) args
    end
  | (c & CSubi _, args & [TmConst {val = CInt x}, y & TmVar _]) ->
    let b = astBuilder info in
    if eqi x.val 0 then b.negi y else b.appSeq (b.uconst c) args
  | (c & CSubi _, args & [x & TmVar _, TmConst {val = CInt y}]) ->
    let b = astBuilder info in
    if eqi y.val 0 then x else b.appSeq (b.uconst c) args
  | (c & CSubi _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.int 0
    else b.appSeq (b.uconst c) [x, y]
  | (c & (CDivi _), args & [TmConst {val = CInt x}, y & TmVar _]) ->
    let b = astBuilder info in
    if eqi x.val 0 then b.int 0 else b.appSeq (b.uconst c) args
  | (c & (CDivi _), args & [x, TmConst {val = CInt y}]) ->
    let b = astBuilder info in
    switch y.val
    case 0 then errorSingle [info] "Division by zero"
    case 1 then x
    case _ then b.appSeq (b.uconst c) args
    end
  | (c & (CModi _), args & [TmConst {val = CInt x}, TmVar _]) ->
    let b = astBuilder info in
    if eqi x.val 0 then b.int 0 else b.appSeq (b.uconst c) args
  | (c & (CModi _), args & [TmVar _, TmConst {val = CInt y}]) ->
    let b = astBuilder info in
    switch y.val
    case 0 then errorSingle [info] "Division by zero"
    case 1 then b.int 0
    case _ then b.appSeq (b.uconst c) args
    end
  | (c & (CAddi _ | CMuli _ | CSubi _ | CDivi _ | CModi _),
     args & [TmVar _, TmVar _]) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
  | (c & CNegi _, [a & TmVar _]) ->
    let b = astBuilder info in
    b.app (b.uconst c) a
end

lang ArithFloatPEval = ArithFloatEval + VarAst
  sem pevalReadbackH ctx =
  | t & TmConst (r & { val = CFloat v }) ->
    if ltf v.val 0. then
      let b = astBuilder r.info in
      (ctx, b.negf (b.float (negf v.val)))
    else (ctx, t)

  sem delta info =
  | (c & (CAddf _ | CMulf _), args & [TmVar _, TmConst _]) ->
    -- NOTE(oerikss, 2022-02-15): We move constants to the lhs for associative
    -- operators to make later simplifications easier.
    delta info (c, reverse args)
  | (c & CAddf _, args & [TmConst {val = CFloat x}, y & TmVar _]) ->
    if eqf x.val 0. then y else
      let b = astBuilder info in
      b.appSeq (b.uconst c) args
  | (c & CAddf _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.mulf (b.float 2.) y
    else b.appSeq (b.uconst c) [x, y]
  | (c & CMulf _, args & [TmConst {val = CFloat x}, y & TmVar _]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.float 0.
    else if eqf x.val 1. then y
    else b.appSeq (b.uconst c) args
  | (c & CSubf _, args & [TmConst {val = CFloat x}, y & TmVar _]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.negf y else b.appSeq (b.uconst c) args
  | (c & CSubf _, args & [x & TmVar _, TmConst {val = CFloat y}]) ->
    let b = astBuilder info in
    if eqf y.val 0. then x else b.appSeq (b.uconst c) args
  | (c & CSubf _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.float 0.
    else b.appSeq (b.uconst c) [x, y]
  | (c & (CDivf _), args & [TmConst {val = CFloat x}, y & TmVar _]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.float 0. else b.appSeq (b.uconst c) args
  | (c & (CDivf _), args & [x, TmConst {val = CFloat y}]) ->
    let b = astBuilder info in
    if eqf y.val 0. then errorSingle [info] "Division by zero"
    else if eqf y.val 1. then x
    else b.appSeq (b.uconst c) args
  | (c & (CAddf _ | CMulf _ | CSubf _ | CDivf _),
     args & [TmVar _, TmVar _]) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
  | (c & CNegf _, [a & TmVar _]) ->
    let b = astBuilder info in
    b.app (b.uconst c) a
end

lang CmpFloatPEval = CmpFloatEval + VarAst
  sem delta info =
  | (c & (CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _),
     args & ([TmVar _, TmVar _] | [!TmVar _, TmVar _] | [TmVar _, !TmVar _])) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
end

lang CmpIntPEval = CmpIntEval + VarAst
  sem delta info =
  | (c & (CEqi _ | CLti _ | CLeqi _ | CGti _ | CGeqi _ | CNeqi _),
     args & ([TmVar _, TmVar _] | [!TmVar _, TmVar _] | [TmVar _, !TmVar _])) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
end

lang CmpCharPEval = CmpCharEval + VarAst
  sem delta info =
  | (c & CEqc _, args & ([TmVar _, _] | [_, TmVar _])) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
end

lang IOPEval = IOAst + SeqAst + IOArity
  sem delta info =
  | (c & (CPrint _ | CPrintError _), args & [TmSeq s]) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
  | (c & (CDPrint _ | CFlushStdout _ | CFlushStderr _ | CReadLine _),
     args & [_]) ->
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
end

lang SysPEval = SysAst + VarAst + PEval
  sem delta info =
  | (c & (CError _ | CCommand _ | CExit _), args) ->
    -- Always delay such side effects until program is executed
    let b = astBuilder info in
    b.appSeq (b.uconst c) args
end

lang MExprPEval =
  -- Terms
  VarPEval + LamPEval + AppPEval + RecordPEval + ConstPEval + LetPEval +
  RecLetsPEval + MatchPEval + NeverPEval + SeqPEval +

  -- Constants
  ArithIntPEval + ArithFloatPEval + CmpIntPEval + CmpFloatPEval + IOPEval +
  CmpCharPEval + SysPEval +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval +

  -- Side effects
  MExprSideEffect
end

lang TestLang = MExprPEval + MExprPrettyPrint + MExprEq + BootParser end

mexpr

use TestLang in

let _test = lam expr.
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "Before peval",
      expr2str expr
    ]);
  let expr = symbolizeAllowFree expr in
  match pevalExpr { pevalCtxEmpty () with maxRecDepth = 2 } expr with expr in
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "After peval",
      expr2str expr
    ]);
  expr
in

let _parse =
  parseMExprString
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in


------------------------------
-- Test closure application --
------------------------------

let prog = _parse "lam x. x" in
utest _test prog with _parse "lam x. x" using eqExpr in

let prog = _parse "(lam x. x) (lam z. z)" in
utest _test prog with _parse "lam z. z" using eqExpr in

let prog = _parse "(lam x. x y) (lam z. z)" in
utest _test prog with _parse "y" using eqExpr in

let prog = _parse "(lam x. y y x) (lam z. z)" in
utest _test prog with _parse "
let t =
  y
    y
in
let t1 =
  t
    (lam z.
       z)
in
t1
  "
  using eqExpr
in

-----------------------------
-- Test integer arithmetic --
-----------------------------

let prog = _parse "lam x. addi x 0" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. addi x 1" in
utest _test prog with _parse "
lam x.
  let t =
    addi
      1
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. addi 0 x" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. addi 1 x" in
utest _test prog with _parse "
lam x.
  let t =
    addi
      1
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. addi x x" in
utest _test prog with _parse "
lam x.
  let t =
    muli
      2
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. muli x 0" in
utest _test prog with _parse "lam x. 0"
  using eqExpr
in

let prog = _parse "lam x. muli 0 x" in
utest _test prog with _parse "lam x. 0"
  using eqExpr
in

let prog = _parse "lam x. muli 1 x" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. muli x 1" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. muli 2 x" in
utest _test prog with _parse "
lam x.
  let t =
    muli
      2
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. muli x 2" in
utest _test prog with _parse "
lam x.
  let t =
    muli
      2
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. divi x 1" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. divi 0 x" in
utest _test prog with _parse "lam x. 0"
  using eqExpr
in

let prog = _parse "lam x. modi x 1" in
utest _test prog with _parse "lam x. 0" using eqExpr in

let prog = _parse "lam x. modi 0 x" in
utest _test prog with _parse "lam x. 0" using eqExpr in

------------------------------------
-- Test floating point arithmetic --
------------------------------------

let prog = _parse "lam x. addf x 0." in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. addf x 1." in
utest _test prog with _parse "
lam x.
  let t =
    addf
      1.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. addf 0. x" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. addf 1. x" in
utest _test prog with _parse "
lam x.
  let t =
    addf
      1.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. addf x x" in
utest _test prog with _parse "
lam x.
  let t =
    mulf
      2.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. mulf x 0." in
utest _test prog with _parse "lam x. 0."
  using eqExpr
in

let prog = _parse "lam x. mulf 0. x" in
utest _test prog with _parse "lam x. 0."
  using eqExpr
in

let prog = _parse "lam x. mulf 1. x" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. mulf x 1." in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. mulf 2. x" in
utest _test prog with _parse "
lam x.
  let t =
    mulf
      2.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. mulf x 2." in
utest _test prog with _parse "
lam x.
  let t =
    mulf
      2.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam x. divf x 1." in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "lam x. divf 0. x" in
utest _test prog with _parse "lam x. 0."
  using eqExpr
in


-------------------------------------------
-- Test Composite Arithmetic Expressions --
-------------------------------------------

let prog = _parse "lam x. mulf (addf 1. x) 1." in
utest _test prog with _parse "
lam x.
  let t =
    addf
      1.
      x
  in
  t
  "
  using eqExpr
in

let prog = _parse "lam y. (lam x. mulf x x) (mulf (mulf 2. y) y)" in
utest _test prog with _parse "
lam y.
  let t =
    mulf
      2.
      y
  in
  let t1 =
    mulf
      t
      y
  in
  let t2 =
    mulf
      t1
      t1
  in
  t2
  "
  using eqExpr
in

----------------------------------------
-- Test Record Updates and Projection --
----------------------------------------

let prog = _parse "{ a = 1, b = 2}.b" in
utest _test prog with _parse "2"
  using eqExpr
in

let prog = _parse "{ a = 1, b = 2}.a" in
utest _test prog with _parse "1"
  using eqExpr
in

let prog = _parse "lam x. x.a" in
utest _test prog with _parse "
lam x.
  let t =
    x.a
  in
  t
  "
  using eqExpr
in

let prog = _parse "{{ a = 1, b = 2} with a = 3}.a" in
utest _test prog with _parse "3"
  using eqExpr
in

let prog = _parse "{x with a = 3}.a" in
utest _test prog with _parse "
let t =
  { x
    with
    a =
      3 }
in
let t1 =
  t.a
in
t1
  "
  using eqExpr
in

---------------------------
-- Test Pattern Matching --
---------------------------

let prog = _parse "lam x. match (lam z. (1, z)) x with (u, v) in v" in
utest _test prog with _parse "lam x. x"
  using eqExpr
in

let prog = _parse "
lam x. match x with (f, g) then (lam x. x) (f, g) else (lam x. x) (lam z. z)
  " in
utest _test prog with _parse "
lam x.
  let t =
    match
      x
    with
      (f, g)
    then
      (f, g)
    else
      lam z.
        z
  in
  t
  "
  using eqExpr
in

-------------------------
-- Test Recursive Lets --
-------------------------

let prog = _parse "
recursive let pow = lam n. lam x.
  if eqi n 0 then 1.
  else
    if eqi n 1 then x
    else mulf (pow (subi n 1) x) x
in lam x. pow 10 x
  " in
utest _test prog with _parse "
recursive let pow = lam n. lam x.
  let t4 = eqi n 0 in
  let t5 = match t4 with true then 1.
    else
      let t6 = eqi n 1 in
      let t7 =
        match t6 with true then x
        else
          let t8 = subi n 1 in
          let t9 = pow t8 in
          let t10 = t9 x in
          let t11 = mulf t10 x in
          t11
      in
      t7
  in
  t5
in
lam x.
  let t = pow 8 in
  let t1 = t x in
  let t2 = mulf t1 x in
  let t3 = mulf t2 x in
  t3
  "
  using eqExpr
in

let prog = _parse "
recursive let pow = lam n. lam x.
  if eqi n 0 then 1.
  else
    if eqi n 1 then x
    else mulf (pow (subi n 1) x) x
in lam x. pow 2 x
  " in
utest _test prog with _parse "
lam x. let t = mulf x x in t
  "
  using eqExpr
in

let prog = _parse "
recursive
let odd = lam n.
    if eqi n 1 then true
    else if lti n 1 then false
    else even (subi n 1)
let even = lam n.
    if eqi n 0 then true
    else if lti n 0 then false
    else odd (subi n 1)
in
odd 2
  " in
utest _test prog with _parse "
recursive
  let odd = lam n.
      let t1 = eqi n 1 in
      let t2 =
        match t1 with true then true
        else
          let t3 = lti n 1 in
          let t4 =
            match t3 with true then false
            else
              let t5 = subi n 1 in
              let t6 = even t5 in t6
          in
          t4
      in
      t2
  let even = lam n.
      let t7 = eqi n 0 in
      let t8 =
        match t7 with true then true
        else
          let t9 = lti n 0 in
          let t10 =
            match t9 with true then false
            else
              let t11 = subi n 1 in
              let t12 = odd t11 in
              t12
          in
          t10
      in
      t8
in
let t = odd 0 in t
  "
  using eqExpr
in


let prog = _parse "
recursive
let odd = lam n.
    if eqi n 1 then true
    else if lti n 1 then false
    else even (subi n 1)
let even = lam n.
    if eqi n 0 then true
    else if lti n 0 then false
    else odd (subi n 1)
in
odd 1
  " in
utest _test prog with _parse "
true
  "
  using eqExpr
in

--------------------------------
-- Test Dead Code Elimination --
--------------------------------

let prog = _parse "
lam y. (lam x. mulf x 0.) (addf y y)
  " in
utest _test prog with _parse "lam y. 0."
  using eqExpr
in

let prog = _parse "
lam y. (lam x. mulf x 0.) (addf (print \"hello\"; y) y)
  " in
utest _test prog with _parse "
lam t.
  let t = print \"hello\" in
  0.
  "
  using eqExpr
in

-- logSetLogLevel logLevel.debug;

let prog = _parse "
lam x.
    (lam x1. lam x2. addf x1 x2)
      ((lam y. addf y y) x)
      ((lam z. addf z z) x)
  " in
utest _test prog with _parse "
lam x.
  let t =
    mulf
      2.
      x
  in
  let t1 =
    mulf
      2.
      x
  in
  let t2 =
    addf
      t
      t1
  in
  t2
  "
  using eqExpr
in

--------------------------------
-- Test System Calls --
--------------------------------

let prog = _parse "
  error \"abc\";
  exit 1;
  command \"echo\"
" in

utest _test prog with _parse "
  let t = error \"abc\" in
  let t1 = exit 1 in
  let t2 = command \"echo\" in
  t2
" using eqExpr in


--------------------------------
-- Test Char Comparison --
--------------------------------

let prog = _parse "
  eqc 'v' x
" in

utest _test prog with _parse "
  let t = eqc 'v' x in
  t" using eqExpr in

let prog = _parse "
  eqc 'v' 'a'" in

utest _test prog with _parse "false" using eqExpr in


()
