include "map.mc"
include "set.mc"
include "log.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/pprint.mc"
include "mexpr/boot-parser.mc"
include "mexpr/side-effect.mc"
include "mexpr/constant-fold.mc"

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
    negf = app (uconst (CNegf ())),
    seq = lam tms. TmSeq {
      tms = tms,
      info = info,
      ty = tyunknown_
    }
  }

lang PEvalCtx = Eval + SideEffect
  type PEvalCtx = {
    env : EvalEnv,
    freeVar : Set Name,
    effectEnv : SideEffectEnv,
    maxRecDepth : Int,
    recFlag : Bool
  }

  sem pevalCtxEmpty : () -> PEvalCtx
  sem pevalCtxEmpty =| _ -> {
    env = evalEnvEmpty (),
    freeVar = setEmpty nameCmp,
    effectEnv = sideEffectEnvEmpty (),
    maxRecDepth = 2,
    recFlag = true
  }
end

lang PEval = PEvalCtx + Eval + PrettyPrint
  sem peval : Expr -> Expr
  sem peval =| t -> pevalExpr (pevalCtxEmpty ()) t

  sem pevalExpr : PEvalCtx -> Expr -> Expr
  sem pevalExpr ctx =| t -> pevalReadback (pevalBind ctx (lam x. x) t)

  sem pevalWithEnv : EvalEnv -> Expr -> Expr
  sem pevalWithEnv env =
  | ast ->
    let ctx = {pevalCtxEmpty () with env = env} in
    pevalExpr ctx ast

  sem pevalBindThis : Expr -> Bool
  sem pevalBindThis =
  | t ->
    errorSingle [infoTm t] (join ["pevalBindThis: undefined for:\n", expr2str t])

  sem pevalBind : PEvalCtx -> (Expr -> Expr) -> Expr -> Expr
  sem pevalBind ctx k =| t ->
    pevalEval ctx
      (lam t.
        if pevalBindThis t then
          let b = astBuilder (infoTm t) in
          let ident = nameSym "t" in
          bind_ (b.nulet ident t) (k (b.var ident))
        else
          k t)
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
  sem pevalBindThis =
  | TmApp _ -> true

  sem pevalApply : Info -> PEvalCtx -> (Expr -> Expr) -> (Expr, Expr) -> Expr
  sem pevalApply info ctx k =
  | (f, arg) -> k (app_ f arg)

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
  sem pevalBindThis =
  | TmVar _ -> false

  sem pevalEval ctx k =
  | t & TmVar r ->
    match evalEnvLookup r.ident ctx.env with Some t then k t
    else k t

  sem pevalReadbackH ctx =
  | t & TmVar r -> ({ ctx with freeVar = setInsert r.ident ctx.freeVar }, t)
end

lang LamPEval = PEval + VarAst + LamAst + ClosAst + AppEval
  sem pevalBindThis =
  | TmClos _ -> false

  sem pevalApply info ctx k =
  | (TmClos r, arg) ->
    let env = evalEnvInsert r.ident arg (r.env ()) in
    pevalEval { ctx with env = env } k r.body

  sem pevalEval ctx k =
  | TmLam r ->
    k (TmClos {
      ident = r.ident, body = r.body, env = lam. ctx.env, info = r.info
    })
  | TmClos r -> k (TmClos r)

  sem pevalReadbackH ctx =
  | TmClos r ->
    let b = astBuilder r.info in
    let newident = nameSetNewSym r.ident in
    let env = evalEnvInsert r.ident (b.var newident) (r.env ()) in
    match
      pevalReadbackH ctx (pevalBind { ctx with env = env } (lam x. x) r.body)
      with (ctx, body)
    in
    (ctx, b.nulam newident body)
end

lang ClosPAst = ClosAst
  syn Expr =
  | TmClosP {
    cls : {ident : Name, body : Expr, env : Lazy EvalEnv, info : Info},
    ident : Name,
    isRecursive : Bool
  }

  sem infoTm =
  | TmClosP r -> r.cls.info

  sem withInfo info =
  | TmClosP r -> TmClosP { r with cls = { r.cls with info = info } }
end

lang LetPEval = PEval + LetAst
  sem pevalBindThis =
  | TmLet _ -> true

  sem pevalEval ctx k =
  | TmLet r ->
    pevalBind ctx
      (lam body.
        if pevalBindThis body then
          TmLet { r with body = body, inexpr = pevalBind ctx k r.inexpr }
        else
          pevalBind
            { ctx with env = evalEnvInsert r.ident body ctx.env } k r.inexpr)
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

-- NOTE(oerikss, 2023-08-14): We currently do not partially evaluate recursive
-- calls.
lang RecLetsPEval = PEval + RecLetsAst + ClosPAst + LamAst
  sem pevalBindThis =
  | TmRecLets _ -> true

  sem pevalEval ctx k =
  | TmRecLets r ->
    let bindings =
      map
        (lam bind. { bind with body = pevalBind ctx (lam x. x) bind.body })
        r.bindings
    in
    TmRecLets {
      r with
      bindings = bindings,
      inexpr = pevalBind ctx k r.inexpr
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
  sem pevalBindThis =
  -- NOTE(oerikss, 2022-02-15): We do not have to check inside the record as the
  -- bindings vill always bind to values after the PEval transformation.
  | TmRecord _ -> false
  | TmRecordUpdate _ -> true

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
            case _ then
              k (TmRecordUpdate { r1 with rec = rec, value = value })
            end)
          r1.value)
      r1.rec
end

lang TypePEval = PEval + TypeAst
  sem pevalBindThis =
  | TmType _ -> true

  sem pevalEval ctx k =
  | TmType t -> TmType {t with inexpr = pevalBind ctx k t.inexpr}
end

lang DataPEval = PEval + DataAst
  sem pevalBindThis =
  | TmConDef _ -> true
  | TmConApp _ -> false

  sem pevalEval ctx k =
  | TmConDef t -> TmConDef {t with inexpr = pevalBind ctx k t.inexpr}
  | TmConApp t -> pevalBind ctx (lam body. k (TmConApp {t with body = body})) t.body
end

lang SeqPEval = PEval + SeqAst
  -- NOTE(oerikss, 2022-02-15): We do not have to check inside the sequences as the
  -- elements vill always be values in the PEval transformation.
  sem pevalBindThis =
  | TmSeq _ -> false

  sem pevalEval ctx k =
  | TmSeq r ->
    mapK
      (lam t. lam k. pevalBind ctx k t)
      r.tms
      (lam tms. k (TmSeq { r with tms = tms }))
end

lang ConstPEval = PEval + ConstEvalNoDefault
  sem pevalReadbackH ctx =
  | TmConstApp r ->
    match mapAccumL pevalReadbackH ctx r.args with (ctx, args) in
    let b = astBuilder r.info in
    (ctx, b.appSeq (b.uconst r.const) args)

  sem pevalBindThis =
  | TmConst _ -> false
  | TmConstApp _ -> false
  -- NOTE(oerikss, 2022-02-15): We treat partially applied constants as
  -- values. We then have to make sure to transform these to normal TmApp's to
  -- avoid re-computations when we see that we cannot statically evaluate the
  -- constant.

  sem pevalEval ctx k =
  | t & (TmConst _ | TmConstApp _) -> k t

  sem delta info =
  | (const, args) ->
    if lti (length args) (constArity const) then
      -- Accumulate arguments if still not a complete application
      TmConstApp {const = const, args = args, info = info}
    else
      -- No available pattern, don't do any partial evaluation
      let b = astBuilder info in
      b.appSeq (b.uconst const) args

  sem pevalApply info ctx k =
  | (TmConst r, arg) -> k (delta info (r.val, [arg]))
  | (TmConstApp r, arg) -> k (delta info (r.const, snoc r.args arg))
end

lang MatchPEval =
  PEval + MatchEval + RecordAst + ConstAst + DataAst + SeqAst + NeverAst + VarAst

  sem pevalBindThis =
  | TmMatch _ -> true

  sem pevalEval ctx k =
  | TmMatch r ->
    pevalBind ctx
      (lam target.
        switch target
        case t & TmNever _ then k t
          -- TODO(oerikss, 2023-07-07): This check is not exhaustive, we must
          -- probably redefine tryMatch and handle each particular pattern type.
        case TmRecord _ | TmConst _ | TmConApp _ | TmSeq _ then
          match tryMatch ctx.env target r.pat with Some env then
            pevalBind { ctx with env = env } k r.thn
          else pevalBind ctx k r.els
        case _ then
          let ctx = { ctx with recFlag = false } in
          k (TmMatch {r with
                      target = target,
                      thn = pevalBind ctx (lam x. x) r.thn,
                      els = pevalBind ctx (lam x. x) r.els
          })
        end)
      r.target
end

lang UtestPEval = PEval + UtestAst
  sem pevalBindThis =
  | TmUtest _ -> true

  sem pevalEval ctx k =
  | TmUtest t ->
    pevalBind ctx
      (lam test.
         pevalBind ctx
           (lam expected.
             let inner = lam x.
               match x with (tusing, tonfail) in
                TmUtest { t with
                          test = test,
                          expected = expected,
                          next = pevalBind ctx k t.next,
                          tusing = tusing,
                          tonfail = tonfail
                }
               in
               switch (t.tusing, t.tonfail)
               case (Some tusing, Some tonfail) then
                 pevalBind ctx
                   (lam tusing.
                     pevalBind ctx
                       (lam tonfail. inner (Some tusing, Some tonfail))
                       tonfail)
                   tusing
               case (Some tusing, None ()) then
                 pevalBind ctx (lam tusing. inner (Some tusing, None ())) tusing
               case (None (), Some tonfail) then
                 pevalBind ctx (lam tonfail. inner (None (), Some tonfail)) tonfail
               case (None (), None ()) then inner (None (), None ())
               end)
           t.expected)
      t.test
end

lang NeverPEval = PEval + NeverAst
  sem pevalBindThis =
  | TmNever _ -> false

  sem pevalEval ctx k =
  | t & TmNever _ -> k t

  sem pevalApply info ctx k =
  | (t & TmNever _, _) -> k t
end

lang ExtPEval = PEval + ExtAst
  sem pevalBindThis =
  | TmExt _ -> true

  sem pevalEval ctx k =
  | TmExt t -> TmExt {t with inexpr = pevalBind ctx k t.inexpr}
end

lang ArithIntPEval = ArithIntEval + VarAst
  sem delta info =
  | (c & (CAddi _ | CMuli _), args & [!TmConst _, TmConst _]) ->
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
  | (c & (CDivi _),
     args & [TmConst {val = CInt x}, y & !TmConst {val = CInt _}]) ->
    let b = astBuilder info in
    if eqi x.val 0 then b.int 0 else b.appSeq (b.uconst c) args
  | (c & (CDivi _), args & [x, TmConst {val = CInt y}]) ->
    let b = astBuilder info in
    switch y.val
    case 0 then errorSingle [info] "Division by zero"
    case 1 then x
    case _ then b.appSeq (b.uconst c) args
    end
  | (c & (CModi _), args & [TmConst {val = CInt x}, !TmConst {val = CInt _}]) ->
    let b = astBuilder info in
    if eqi x.val 0 then b.int 0 else b.appSeq (b.uconst c) args
  | (c & (CModi _), args & [!TmConst {val = CInt _}, TmConst {val = CInt y}]) ->
    let b = astBuilder info in
    switch y.val
    case 0 then errorSingle [info] "Division by zero"
    case 1 then b.int 0
    case _ then b.appSeq (b.uconst c) args
    end
end

lang ArithFloatPEval = ArithFloatEval + VarAst
  sem pevalReadbackH ctx =
  | t & TmConst (r & { val = CFloat v }) ->
    if ltf v.val 0. then
      let b = astBuilder r.info in
      (ctx, b.negf (b.float (negf v.val)))
    else (ctx, t)

  sem delta info =
  | (c & (CAddf _ | CMulf _), args & [!TmConst _, TmConst _]) ->
    -- NOTE(oerikss, 2022-02-15): We move constants to the lhs for associative
    -- operators to make later simplifications easier.
    delta info (c, reverse args)
  | (c & CAddf _,
     args & [TmConst {val = CFloat x}, y & !TmConst {val = CFloat _}]) ->
    if eqf x.val 0. then y else
      let b = astBuilder info in
      b.appSeq (b.uconst c) args
  | (c & CAddf _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.mulf (b.float 2.) y
    else b.appSeq (b.uconst c) [x, y]
  | (c & CMulf _,
     args & [TmConst {val = CFloat x}, y & !TmConst {val = CFloat _}]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.float 0.
    else if eqf x.val 1. then y
    else b.appSeq (b.uconst c) args
  | (c & CSubf _,
     args & [TmConst {val = CFloat x}, y & !TmConst {val = CFloat _}]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.negf y else b.appSeq (b.uconst c) args
  | (c & CSubf _, args & [x & !TmConst {val = CFloat _}, TmConst {val = CFloat y}]) ->
    let b = astBuilder info in
    if eqf y.val 0. then x else b.appSeq (b.uconst c) args
  | (c & CSubf _, [x & TmVar r1, y & TmVar r2]) ->
    let b = astBuilder info in
    if nameEqSymUnsafe r1.ident r2.ident then b.float 0.
    else b.appSeq (b.uconst c) [x, y]
  | (c & (CDivf _), args & [TmConst {val = CFloat x}, y & !TmConst {val = CFloat _}]) ->
    let b = astBuilder info in
    if eqf x.val 0. then b.float 0. else b.appSeq (b.uconst c) args
  | (c & (CDivf _), args & [x, TmConst {val = CFloat y}]) ->
    let b = astBuilder info in
    if eqf y.val 0. then errorSingle [info] "Division by zero"
    else if eqf y.val 1. then x
    else b.appSeq (b.uconst c) args
end

lang CmpFloatPEval = CmpFloatEval + VarAst end

lang CmpIntPEval = CmpIntEval + VarAst end

lang CmpCharPEval = CmpCharEval + VarAst end

lang IOPEval = IOAst + SeqAst + IOArity end

lang SeqOpPEval = PEval + SeqOpEvalFirstOrder + AppAst + ConstAst + VarAst
  sem pevalBindThis =
  | TmApp {
    lhs = TmApp {
      lhs = TmConst { val = CGet _},
      rhs = TmVar _
    },
    rhs = TmConst { val = CInt _} | TmVar _
  } -> false

  sem pevalApply info ctx k =
  | (TmConstApp {const = CMap _, args = [f]}, TmSeq s) ->
    let f = lam x. lam k.
      pevalApply info ctx (pevalBind ctx k) (f, x)
    in
    mapK f s.tms (lam tms. k (TmSeq { s with tms = tms }))
  | (TmConstApp {const = CMapi _, args = [f]}, TmSeq s) ->
    let f = lam i. lam x. lam k.
      pevalApply info ctx
        (pevalBind ctx (lam f.
          pevalApply info ctx (pevalBind ctx k) (f, x)))
        (f, (int_ i))
    in
    mapiK f s.tms (lam tms. k (TmSeq { s with tms = tms }))
  | (TmConstApp {const = CFoldl _, args = [f, acc]}, TmSeq s) ->
    let f = lam acc. lam x. lam k.
      pevalApply info ctx
        (pevalBind ctx (lam f.
          pevalApply info ctx (pevalBind ctx k) (f, x)))
        (f, acc)
    in
    foldlK f acc s.tms k
end

-- NOTE(oerikss, 2023-08-14): WIP handling of recursion and better handling of
-- closures. It avoids code-swell due to closure inlineing. This fragment is not
-- correct for functions returning functions.
lang LamRecLetsPEval = PEval + VarAst + LamAst + RecLetsAst + ClosPAst + AppEval
  sem pevalBindThis =
  | TmClosP _ -> false
  | TmRecLets _ -> true

  sem pevalApply info ctx k =
  | (TmClosP r, arg) ->
    if and (not ctx.recFlag) r.isRecursive then
      let b = astBuilder r.cls.info in k (b.app (b.var r.ident) arg)
    else
      let env = evalEnvInsert r.cls.ident arg (r.cls.env ()) in
      pevalEval { ctx with env = env } k r.cls.body

  sem pevalEval ctx k =
  | TmLam r ->
    let b = astBuilder r.info in
    let cls =
      { ident = r.ident, body = r.body, env = lam. ctx.env, info = r.info }
    in
    let newident = nameSetNewSym r.ident in
    let env = evalEnvInsert r.ident (b.var newident) ctx.env in
    let body =
      (pevalBind { ctx with env = env } (lam x. x) r.body)
    in
    let ident = nameSym "t" in
    bind_
      (b.nulet ident (TmLam { r with ident = newident, body = body }))
      (k (TmClosP { cls = cls, ident = ident, isRecursive = false }))
  | TmClosP r -> k (TmClosP r)
  | TmRecLets r ->
    recursive let envPrime : Int -> Lazy EvalEnv = lam n. lam.
      let wraplambda = lam bind.
        if geqi n ctx.maxRecDepth then TmVar {
          ident = bind.ident,
          info = bind.info,
          ty = bind.tyBody,
          frozen = false
        }
        else
          match bind.body with TmLam r then TmClosP {
            cls = {
              ident = r.ident,
              body = r.body,
              env = envPrime (succ n),
              info = r.info
            },
            ident = bind.ident,
            isRecursive = true
          }
          else
            errorSingle [infoTm bind.body]
              "Right-hand side of recursive let must be a lambda"
      in
      foldl
        (lam env. lam bind.
          evalEnvInsert bind.ident (wraplambda bind) env)
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
  | TmClosP r ->
    let b = astBuilder r.cls.info in
    ({ ctx with freeVar = setInsert r.ident ctx.freeVar }, b.var r.ident)
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


lang MExprPEval =
  -- Terms
  VarPEval + LamPEval + AppPEval + RecordPEval + ConstPEval + LetPEval +
  RecLetsPEval + MatchPEval + NeverPEval + DataPEval + TypePEval + SeqPEval +
  UtestPEval + ExtPEval + SeqOpPEval +

  -- Constants
  ArithIntPEval + ArithFloatPEval + CmpIntPEval + CmpFloatPEval + IOPEval +
  CmpCharPEval +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval +

  -- Side effects
  MExprSideEffect
end

lang TestLang =
  MExprPEval + MExprPrettyPrint + MExprEq + BootParser + MExprConstantFold
end

-- NOTE(oerikss, 2023-08-14): This new language supports recursion and tries to
-- to avoid code-swell from substitution of closures.
lang MExprPEvalNew =
  -- Terms
  VarPEval + LamRecLetsPEval + AppPEval + RecordPEval + ConstPEval + LetPEval +
  MatchPEval + NeverPEval + DataPEval + TypePEval + SeqPEval +
  UtestPEval + ExtPEval + SeqOpPEval +

  -- Constants
  ArithIntPEval + ArithFloatPEval + CmpIntPEval + CmpFloatPEval + IOPEval +
  CmpCharPEval +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval +

  -- Side effects
  MExprSideEffect
end

lang TestLangNew =
  MExprPEvalNew + MExprPrettyPrint + MExprEq + BootParser + MExprConstantFold
end

mexpr

utest
  ----------------------------------
  -- Test standard implementation --
  ----------------------------------
  use TestLang in

  let _test = lam expr.
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "Before peval",
        expr2str expr
      ]);
    let expr = symbolizeAllowFree expr in
    match pevalExpr (pevalCtxEmpty ()) expr with expr in
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "After peval",
        expr2str expr
      ]);
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "After peval (folded)",
        expr2str (constantfoldLets expr)
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
  let t1 =
    y
      y
  in
  let t2 =
    t1
      (lam z. z)
  in
  t2
    "
    using eqExpr
  in

  let prog = _parse "(lam f. (f, f)) (lam z. z)" in
  utest _test prog with _parse "
  (lam z. z, lam z. z)
    " using eqExpr in

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
        lam z. z
    in
    t
    "
    using eqExpr
  in

  ---------------
  -- Test Lets --
  ---------------

  let prog = _parse "
    lam y. let f = lam x. x in f y
    " in
  utest _test prog with _parse "
    lam y. y
    "
    using eqExpr
  in

  let prog = _parse "
    lam y. let f = y (lam x. x) in f (lam x. x)
    " in
  utest _test prog with _parse "
    lam y.
      let t1 = y (lam x. x) in
      let t2 = t1 (lam x. x) in
      t2
    "
    using eqExpr
  in

  let prog = _parse "
    (lam f. (f, f)) (lam x. x)
    " in
  utest _test prog with _parse "
    (lam x. x, lam x. x)
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

  --------------------------
  -- Test Char Comparison --
  --------------------------

  let prog = _parse "
  lam x.
    eqc 'v' x
  " in

  utest _test prog with _parse "
  lam x.
    let t = eqc 'v' x in
    t
  "
    using eqExpr in

  let prog = _parse "
    eqc 'v' 'a'" in

  utest _test prog with _parse "false" using eqExpr in

  -------------------------
  -- Test Seq Operations --
  -------------------------

  let prog = _parse "map (addi 1) [1, 2, 3]" in
  utest _test prog with _parse "[2, 3, 4]" using eqExpr in

  let prog = _parse "lam x. map (addi x) [1, 2, 3]" in
  utest _test prog with _parse "
  lam x.
    let t1 = addi 1 x in
    let t2 = addi 2 x in
    let t3 = addi 3 x in
    [t1, t2, t3]
    "
    using eqExpr
  in

  let prog = _parse "mapi addi [1, 2, 3]" in
  utest _test prog with _parse "[1, 3, 5]" using eqExpr in

  let prog = _parse "lam x. mapi (lam i. lam y. muli i (addi x y)) [1, 2, 3]" in
  utest _test prog with
    _parse "
  lam x.
    let t1 = addi 2 x in
    let t2 = addi 3 x in
    let t3 = muli 2 t2 in
    [0, t1, t3]
      "
    using eqExpr
  in

  let prog = _parse "foldl addi 0 [1, 2, 3]" in
  utest _test prog with _parse "6" using eqExpr in

  let prog = _parse "lam x. foldl addi x [1, 2, 3]" in
  utest _test prog with _parse "
  lam x.
    let t = addi 1 x in
    let t1 = addi 2 t in
    let t2 = addi 3 t1 in
    t2
    " using eqExpr in

  let prog = _parse "lam x. lam y. [get x y, get x 1, get x 2]" in
  utest _test prog with _parse "
    lam x.
      lam y. [get x y, get x 1, get x 2]
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
  utest constantfoldLets (_test prog) with _parse "
  recursive let pow = lam n. lam x.
    if eqi n 0 then 1.
    else
      if eqi n 1 then x
      else mulf (pow (subi n 1) x) x
  in lam x. pow 10 x
    "
    using eqExpr
  in

  let prog = _parse "
  recursive let pow = lam n. lam x.
    if eqi n 0 then 1.
    else
      if eqi n 1 then x
      else mulf (pow (subi n 1) x) x
  in lam x. x
    " in
  utest constantfoldLets (_test prog) with _parse "
    lam x. x
    "
    using eqExpr
  in
  ()
  with () in

utest
  -----------------------------
  -- Test new implementation --
  -----------------------------
  use TestLangNew in

  let _test = lam expr.
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "Before peval",
        expr2str expr
      ]);
    let expr = symbolizeAllowFree expr in
    match pevalExpr { pevalCtxEmpty () with maxRecDepth = 10 } expr with expr in
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "After peval",
        expr2str expr
      ]);
    logMsg logLevel.debug (lam.
      strJoin "\n" [
        "After peval (folded)",
        expr2str (constantfoldLets expr)
      ]);
    expr
  in

  let _parse =
    parseMExprString
      { _defaultBootParserParseMExprStringArg () with allowFree = true }
  in

  ----------------------------------
  -- Test new closure application --
  ----------------------------------

  let prog = _parse "lam x. x" in
  utest _test prog with _parse "let f = lam x. x in f" using eqExpr in

  let prog = _parse "(lam x. x) (lam z. z)" in
  utest _test prog with _parse "let f = lam z. z in f" using eqExpr in

  let prog = _parse "(lam x. x y) (lam z. z)" in
  utest _test prog with _parse "y" using eqExpr in

  let prog = _parse "(lam x. y y x) (lam z. z)" in
  utest _test prog with _parse "
  let t =  lam z. z in
  let t1 =
    y
      y
  in
  let t2 =
    t1
      t
  in
  t2
    "
    using eqExpr
  in

  let prog = _parse "(lam f. (f, f)) (lam z. z)" in
  utest _test prog with _parse "
  let t =
    lam z.
      z
  in
  (t, t)
    " using eqExpr in

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
  utest constantfoldLets (_test prog) with _parse "
  lam x.
    mulf (mulf (mulf (mulf (mulf (mulf (mulf (mulf (mulf x x) x) x) x) x) x) x) x) x
    "
    using eqExpr
  in

  let prog = _parse "
  recursive let pow = lam n. lam x.
    if eqi n 0 then 1.
    else
      if eqi n 1 then x
      else mulf (pow (subi n 1) x) x
  in lam x. lam n. (pow 10 x, pow n x)
    " in
  utest constantfoldLets (_test prog) with _parse "
  recursive let pow = lam n. lam x.
    match eqi n 0 with true then 1.
    else match eqi n 1 with true then x
         else mulf (pow (subi n 1) x) x
  in
  lam x. lam n.
    (mulf (mulf (mulf (mulf (mulf (mulf (mulf (mulf (mulf x x) x) x) x) x) x) x) x) x,
     match eqi n 0 with true then 1.
     else
       match eqi n 1 with true then x
       else mulf (pow (subi n 1) x) x)
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
  let f = lam x. let t = mulf x x in t in f
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
  odd 9
    " in
  utest constantfoldLets (_test prog) with _parse "
  true
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
  odd 10
    " in
  utest constantfoldLets (_test prog) with _parse "
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
  odd 0
    "
    using eqExpr
  in

  let prog = _parse "
  recursive let pow = lam x. lam n.
    if eqi n 0 then 1.
    else mulf x (pow x (subi n 1))
  in
  lam x. [
    pow x 0,
    pow x 1,
    pow x 2,
    pow x 3,
    pow x 4,
    pow x 5,
    pow x 6,
    pow x 7,
    pow x 8,
    pow x 9,
    pow x 10
  ]
    " in

  utest constantfoldLets (_test prog) with _parse "
  recursive let pow = lam x. lam n.
    if eqi n 0 then 1.
    else mulf x (pow x (subi n 1))
  in
  lam x.
    [ 1.,
      x,
      mulf
        x
        x,
      mulf
        x
        (mulf
           x
           x),
      mulf
        x
        (mulf
           x
           (mulf
              x
              x)),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 x))),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 (mulf
                    x
                    x)))),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 (mulf
                    x
                    (mulf
                       x
                       x))))),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 (mulf
                    x
                    (mulf
                       x
                       (mulf
                          x
                          x)))))),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 (mulf
                    x
                    (mulf
                       x
                       (mulf
                          x
                          (mulf
                             x
                             x))))))),
      mulf
        x
        (mulf
           x
           (mulf
              x
              (mulf
                 x
                 (mulf
                    x
                    (mulf
                       x
                       (mulf
                          x
                          (mulf
                             x
                             (mulf
                                x
                                (mulf
                                   x
                                   (pow
                                      x
                                      0)))))))))) ]
    "
    using eqExpr
  in

  let prog = _parse "
  lam p.
  recursive let pow = lam x. lam n.
    if eqi n 0 then 1.
    else mulf x (pow x (subi n 1))
  in
  recursive let powpp = lam xpp. lam npp.
      match lti npp 1 with true then (1., 0., 0.)
      else
        let t = powpp xpp (subi npp 1) in
        (mulf xpp.0 t.0
        ,addf (mulf xpp.0 t.1) (mulf xpp.1 t.0)
        ,addf
           (addf (mulf xpp.0 t.2) (mulf 2. (mulf xpp.1 t.1)))
           (mulf xpp.2 t.0))
  in
  lam y. lam yp. {
    r0 = subf (get yp 1) (mulf (get y 0) (get y 4)),
    r1 = subf (get yp 3) (subf (mulf (get y 2) (get y 4)) 1.),
    r2 = addf
      (powpp (get y 0, get y 1, get yp 1) p).2
      (powpp (get y 2, get y 3, get yp 3) p).2,
    r3 =
      subf
        (get y 5)
        (addf
          (pow x 2)
          (pow x 3)),
    r4 = subf (get y 1) (get yp 0),
    r5 = subf (get y 3) (get yp 2)
  }
    " in

  utest constantfoldLets (_test prog) with _parse "
  lam p.
    recursive let powpp = lam xpp. lam npp.
      match lti npp 1 with true then (1., 0., 0.)
      else
        let t2 = powpp xpp (subi npp 1) in
        (mulf xpp.0 t2.0
        ,addf (mulf xpp.0 t2.1) (mulf xpp.1 t2.0)
        ,addf
           (addf (mulf xpp.0 t2.2) (mulf 2. (mulf xpp.1 t2.1)))
           (mulf xpp.2 t2.0))
    in
    lam y. lam yp. {
      r0 = subf (get yp 1) (mulf (get y 0) (get y 4)),
      r1 = subf (get yp 3) (subf (mulf (get y 2) (get y 4)) 1.),
      r2 =
      addf
        (match lti p 1 with true then (1., 0., 0.)
         else
          let t = powpp (get y 0, get y 1, get yp 1) (subi p 1) in
          (mulf (get y 0) t.0
          ,addf (mulf (get y 0) t.1) (mulf (get y 1) t.0)
          ,addf
             (addf
                (mulf (get y 0) t.2)
                (mulf 2. (mulf (get y 1) t.1)))
             (mulf (get yp 1) t.0))).2
        (match lti p 1 with true then (1., 0., 0.)
         else
          let t1 = powpp (get y 2, get y 3, get yp 3) (subi p 1) in
          (mulf (get y 2) t1.0
          ,addf
             (mulf (get y 2) t1.1)
             (mulf (get y 3) t1.0)
          ,addf
             (addf
                (mulf (get y 2) t1.2)
                (mulf 2. (mulf (get y 3) t1.1)))
             (mulf (get yp 3) t1.0))).2,
      r3 = subf (get y 5) (addf (mulf x x) (mulf x (mulf x x))),
      r4 = subf (get y 1) (get yp 0),
      r5 = subf (get y 3) (get yp 2)
    }
    "
    using eqExpr
  in
  () with () in

()
