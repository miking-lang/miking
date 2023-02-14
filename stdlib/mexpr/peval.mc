include "map.mc"
include "log.mc"

include "ast.mc"
include "ast-builder.mc"
include "eval.mc"
include "pprint.mc"
include "boot-parser.mc"

lang PEvalCtx = Eval
  type PEvalCtx = { env : EvalEnv }

  sem pevalCtxEmpty : () -> PEvalCtx
  sem pevalCtxEmpty =| _ ->
    { env = evalEnvEmpty () }
end

lang PEval = PEvalCtx + Eval + PrettyPrint
  sem peval : Expr -> Expr
  sem peval =| t -> pevalReadback (pevalBind (pevalCtxEmpty ()) (lam x. x) t)

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
          let ident = nameSym "t" in
          bind_ (nulet_ ident t) (k (nvar_ ident)))
      t

  sem pevalEval : PEvalCtx -> (Expr -> Expr) -> Expr -> Expr
  sem pevalEval ctx k =
  | t -> errorSingle [infoTm t] (join ["peval: undefined for:\n", expr2str t])

  sem pevalReadback : Expr -> Expr
  sem pevalReadback =| t -> smap_Expr_Expr pevalReadback t
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
end

lang LamPEval = PEval + LamAst + ClosAst + AppEval
  sem pevalIsValue =
  | TmClos _ -> true

  sem pevalApply info ctx k =
  | (TmClos r, arg) ->
    pevalEval { ctx with env = evalEnvInsert r.ident arg (r.env ()) } k r.body

  sem pevalEval ctx k =
  | TmLam t -> k (TmClos { ident = t.ident, body = t.body, env = lam. ctx.env })
  | TmClos t -> k (TmClos t)

  sem pevalReadback =
  | TmClos r ->
    let body =
      pevalReadback
        (pevalBind { (pevalCtxEmpty ()) with env = r.env () } (lam x. x) r.body)
    in
    nulam_ r.ident body
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

lang ConstPEval = PEval + ConstEval
  sem pevalReadback =
  | TmConstApp r ->
    let args = map pevalReadback r.args in
    appSeq_ (uconst_ r.const) args

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
  | (c & CAddi _, args & [TmConst {val = CInt a}, b & TmVar _]) ->
    if eqi a.val 0 then b else appSeq_ (uconst_ c) args
  | (c & CAddi _, [a & TmVar r1, b & TmVar r2]) ->
    if nameEqSymUnsafe r1.ident r2.ident then muli_ (int_ 2) b
    else appSeq_ (uconst_ c) [a, b]
  | (c & CMuli _, args & [TmConst {val = CInt a}, b & TmVar _]) ->
    switch a.val
    case 0 then int_ 0
    case 1 then b
    case _ then appSeq_ (uconst_ c) args
    end
  | (c & CSubi _, args & [TmConst {val = CInt a}, b & TmVar _]) ->
    if eqi a.val 0 then negi_ b else appSeq_ (uconst_ c) args
  | (c & CSubi _, args & [a & TmVar _, TmConst {val = CInt b}]) ->
    if eqi b.val 0 then a else appSeq_ (uconst_ c) args
  | (c & CSubi _, [a & TmVar r1, b & TmVar r2]) ->
    if nameEqSymUnsafe r1.ident r2.ident then int_ 0
    else appSeq_ (uconst_ c) [a, b]
  | (c & (CDivi _), args & [TmConst {val = CInt a}, b & TmVar _]) ->
    if eqi a.val 0 then int_ 0 else appSeq_ (uconst_ c) args
  | (c & (CDivi _), args & [a, TmConst {val = CInt b}]) ->
    switch b.val
    case 0 then errorSingle [info] "Division by zero"
    case 1 then a
    case _ then appSeq_ (uconst_ c) args
    end
  | (c & (CModi _), args & [TmConst _, b & TmVar _]) ->
    appSeq_ (uconst_ c) args
  | (c & (CAddi _ | CMuli _ | CSubi _ | CDivi _ | CModi _),
     args & [TmVar _, TmVar _]) ->
    appSeq_ (uconst_ c) args
  | (c & CNegi _, [a & TmVar _]) -> app_ (uconst_ c) a
end

lang ArithFloatPEval = ArithFloatEval + VarAst
  sem pevalReadback =
  | t & TmConst (r & { val = CFloat v }) ->
    if ltf v.val 0. then
      app_
        (uconst_ (CNegf ()))
        (TmConst { r with val = CFloat { v with val = (negf v.val)}})
    else t

  sem delta info =
  | (c & (CAddf _ | CMulf _), args & [TmVar _, TmConst _]) ->
    -- NOTE(oerikss, 2022-02-15): We move constants to the lhs for associative
    -- operators to make later simplifications easier.
    delta info (c, reverse args)
  | (c & CAddf _, args & [TmConst {val = CFloat a}, b & TmVar _]) ->
    if eqf a.val 0. then b else appSeq_ (uconst_ c) args
  | (c & CAddf _, [a & TmVar r1, b & TmVar r2]) ->
    if nameEqSymUnsafe r1.ident r2.ident then mulf_ (float_ 2.) b
    else appSeq_ (uconst_ c) [a, b]
  | (c & CMulf _, args & [TmConst {val = CFloat a}, b & TmVar _]) ->
    if eqf a.val 0. then float_ 0.
    else if eqf a.val 1. then b
    else appSeq_ (uconst_ c) args
  | (c & CSubf _, args & [TmConst {val = CFloat a}, b & TmVar _]) ->
    if eqf a.val 0. then negf_ b else appSeq_ (uconst_ c) args
  | (c & CSubf _, args & [a & TmVar _, TmConst {val = CFloat b}]) ->
    if eqf b.val 0. then a else appSeq_ (uconst_ c) args
  | (c & CSubf _, [a & TmVar r1, b & TmVar r2]) ->
    if nameEqSymUnsafe r1.ident r2.ident then float_ 0.
    else appSeq_ (uconst_ c) [a, b]
  | (c & (CDivf _), args & [TmConst {val = CFloat a}, b & TmVar _]) ->
    if eqf a.val 0. then float_ 0. else appSeq_ (uconst_ c) args
  | (c & (CDivf _), args & [a, TmConst {val = CFloat b}]) ->
    if eqf b.val 0. then errorSingle [info] "Division by zero"
    else if eqf b.val 1. then a
    else appSeq_ (uconst_ c) args
  | (c & (CAddf _ | CMulf _ | CSubf _ | CDivf _),
     args & [TmVar _, TmVar _]) ->
    appSeq_ (uconst_ c) args
  | (c & CNegf _, [a & TmVar _]) -> app_ (uconst_ c) a
end

lang CmpFloatPEval = CmpFloatEval + VarAst
  sem delta info =
  | (c & (CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _),
     args & ([TmVar _, TmVar _] | [!TmVar _, TmVar _] | [TmVar _, !TmVar _])) ->
    appSeq_ (uconst_ c) args
end

lang MExprPEval =
  -- Terms
  VarPEval + LamPEval + AppPEval + RecordPEval + ConstPEval + LetPEval +
  MatchPEval + NeverPEval +

  -- Constants
  ArithIntPEval + ArithFloatPEval + CmpFloatPEval +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval
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
  match peval expr with expr in
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

-- logSetLogLevel logLevel.debug;

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

()
