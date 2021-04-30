include "mexpr/eval.mc"

lang TensorOpEval = TensorOpAst + SeqAst + IntAst + FloatAst + TensorEval + ConstEval
  syn Const =
  | CTensorCreate2 [Int]
  | CTensorGetExn2 T
  | CTensorSetExn2 T
  | CTensorSetExn3 (T, [Int])
  | CTensorReshapeExn2 T
  | CTensorCopyExn2 T
  | CTensorSliceExn2 T
  | CTensorSubExn2 T
  | CTensorSubExn3 (T, Int)
  | CTensorIteri2 Expr

  sem _ofTmSeq =
  | TmSeq { tms = tms } ->
    map (lam tm. match tm with TmConst { val = CInt { val = n }} then n
                 else error "Not an integer sequence")
        tms
  | tm -> dprint tm; error "Not an integer sequence"

  sem _toTmSeq =
  | is ->
    let tms = map (lam i. int_ i) is in
    seq_ tms

  sem apply (ctx : {env : Env}) (arg : Expr) =
  | TmConst { val = CTensorCreate2 shape } ->
    let is0 = create (length shape) (lam. 0) in -- First index

    -- Value when applying f to the first index. This determines the type of
    -- the tensor.
    let res0 = apply ctx (_toTmSeq is0) arg in

    -- The structure of f is reusable for all types of tensors.
    let mkf = lam resf. lam x0. lam is.
      if eqSeq eqi is is0 then x0
      else
        let res = apply ctx (_toTmSeq is) arg in
        resf res
    in

    match res0 with TmConst { val = CInt { val = n0 } } then
      let resf = lam res.
          match res with TmConst { val = CInt { val = n } } then n
          else error "Expected integer from f in CTensorCreate"
      in
      let f = mkf resf n0 in
      TmTensor { val = TInt (tensorCreate shape f) }
    else match res0 with TmConst { val = CFloat { val = r0 } } then
      let resf = lam res.
          match res with TmConst { val = CFloat { val = r } } then r
          else error "Expected float from f in CTensorCreate"
      in
      let f = mkf resf r0 in
      TmTensor { val = TFloat (tensorCreate shape f) }
    else
      let f = mkf (lam x. x) res0 in
      TmTensor { val = TExpr (tensorCreate shape f) }
  | TmConst { val = CTensorIteri2 f } ->
    match arg with TmTensor { val = t } then

      let mkg = lam mkt. lam i. lam r.
        let res =
          apply ctx (TmTensor { val = mkt r })  (apply ctx (int_ i) f)
        in
        ()
      in

      match t with TInt t then
        let g = mkg (lam t. TInt t) in
        tensorIteri g t;
        unit_
      else match t with TFloat t then
        let g = mkg (lam t. TFloat t) in
        tensorIteri g t;
        unit_
      else match t with TExpr t then
        let g = mkg (lam t. TExpr t) in
        tensorIteri g t;
        unit_
      else never
    else error "Second argument to CTensorIteri not a tensor"

  sem delta (arg : Expr) =
  | CTensorCreate _ ->
    let val = CTensorCreate2 (_ofTmSeq arg) in
    uconst_ val
  | CTensorGetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorGetExn2 t in
      uconst_ val
    else error "First argument to CTensorGetExn not a tensor"
  | CTensorGetExn2 t ->
    let is = _ofTmSeq arg in
    match t with TInt t then
      let val = tensorGetExn t is in
      int_ val
    else match t with TFloat t then
      let val = tensorGetExn t is in
      float_ val
    else match t with TExpr t then
      let val = tensorGetExn t is in
      val
    else never
  | CTensorSetExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSetExn2 t in
      uconst_ val
    else error "First argument to CTensorSetExn not a tensor"
  | CTensorSetExn2 t ->
    let is = _ofTmSeq arg in
    let val = CTensorSetExn3 (t, is) in
    uconst_ val
  | CTensorSetExn3 (t, is) ->
    match (t, arg) with (TInt t, TmConst { val = CInt { val = v } }) then
      tensorSetExn t is v;
      unit_
    else
    match (t, arg) with (TFloat t, TmConst { val = CFloat { val = v } }) then
      tensorSetExn t is v;
      unit_
    else
    match (t, arg) with (TExpr t, v) then
      tensorSetExn t is v;
      unit_
    else error "Tensor and value type does not match in CTensorSetExn"
  | CTensorRank _ ->
    match arg with TmTensor { val = t } then
      match t with TInt t | TFloat t | TExpr t then
        let val = tensorRank t in
        int_ val
      else never
    else error "First argument to CTensorRank not a tensor"
  | CTensorShape _ ->
    match arg with TmTensor { val = t } then
      match t with TInt t | TFloat t | TExpr t then
        let shape = tensorShape t in
        _toTmSeq shape
      else never
    else error "First argument to CTensorRank not a tensor"
  | CTensorReshapeExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorReshapeExn2 t in
      uconst_ val
    else error "First argument to CTensorReshapeExn not a tensor"
  | CTensorReshapeExn2 t ->
    let is = _ofTmSeq arg in
    match t with TInt t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TInt view }
    else match t with TFloat t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TFloat view }
    else match t with TExpr t then
      let view = tensorReshapeExn t is in
      TmTensor { val = TExpr view }
    else never
  | CTensorCopyExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorCopyExn2 t in
      uconst_ val
    else error "First argument to CTensorCopyExn not a tensor"
  | CTensorCopyExn2 t1 ->
    match arg with TmTensor { val = t2 } then
      match (t1, t2) with (TInt t1, TInt t2) then
        tensorCopyExn t1 t2;
        unit_
      else match (t1, t2) with (TFloat t1, TFloat t2) then
        tensorCopyExn t1 t2;
        unit_
      else match (t1, t2) with (TExpr t1, TExpr t2) then
        tensorCopyExn t1 t2;
        unit_
      else error "Tensor type mismatch in CTensorCopyExn"
    else error "First argument to CTensorCopyExn not a tensor"
  | CTensorSliceExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSliceExn2 t in
      uconst_ val
    else error "First argument to CTensorSliceExn not a tensor"
  | CTensorSliceExn2 t ->
    let is = _ofTmSeq arg in
    match t with TInt t then
      let view = tensorSliceExn t is in
      TmTensor { val = TInt view }
    else match t with TFloat t then
      let view = tensorSliceExn t is in
      TmTensor { val = TFloat view }
    else match t with TExpr t then
      let view = tensorSliceExn t is in
      TmTensor { val = TExpr view }
    else never
  | CTensorSubExn _ ->
    match arg with TmTensor { val = t } then
      let val = CTensorSubExn2 t in
      uconst_ val
    else error "First argument to CTensorSubExn not a tensor"
  | CTensorSubExn2 t ->
    match arg with TmConst { val = CInt { val = ofs }} then
      let val = CTensorSubExn3 (t, ofs) in
      uconst_ val
    else error "Second argument to CTensorSubExn not an integer"
  | CTensorSubExn3 (t, ofs) ->
    match arg with TmConst { val = CInt { val = len }} then
      match t with TInt t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TInt view }
      else match t with TFloat t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TFloat view }
      else match t with TExpr t then
        let view = tensorSubExn t ofs len in
        TmTensor { val = TExpr view }
      else never
    else error "Second argument to CTensorSubExn not an integer"
  | CTensorIteri _ ->
    let val = CTensorIteri2 arg in
    uconst_ val
end

lang MExprEval = MExprEval + TensorOpEval

lang TestLang = MExprEval + MExprPrettyPrint + MExprEq + MExprSym

mexpr

use TestLang in

let evalNoSymbolize : Expr -> Expr =
  lam t : Expr. eval {env = mapEmpty nameCmp} t in

let eval : Expr -> Expr =
  lam t : Expr. evalNoSymbolize (symbolize t) in

-- Tensors
let testTensors = lam v : (a,a,a).
  let t0 = eval (utensorCreate_ (seq_ []) (ulam_ "x" v.0)) in
  let t1 = eval (utensorCreate_ (seq_ [int_ 4]) (ulam_ "x" v.0)) in
  let t2 = eval (utensorCreate_ (seq_ [int_ 4]) (ulam_ "x" v.1)) in

  let evaln = evalNoSymbolize in

  utest evaln (utensorGetExn_ t0 (seq_ [])) with v.0 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 0])) with v.0 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 1])) with v.0 using eqExpr in

  utest evaln (utensorSetExn_ t0 (seq_ []) v.1) with unit_ using eqExpr in
  utest evaln (utensorSetExn_ t1 (seq_ [int_ 0]) v.1) with unit_ using eqExpr in
  utest evaln (utensorSetExn_ t1 (seq_ [int_ 1]) v.2) with unit_ using eqExpr in

  utest evaln (utensorGetExn_ t0 (seq_ [])) with v.1 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 0])) with v.1 using eqExpr in
  utest evaln (utensorGetExn_ t1 (seq_ [int_ 1])) with v.2 using eqExpr in

  utest evaln (utensorRank_ t0) with int_ 0 using eqExpr in
  utest evaln (utensorRank_ t1) with int_ 1 using eqExpr in

  utest evaln (utensorShape_ t0) with seq_ [] using eqExpr in
  utest evaln (utensorShape_ t1) with seq_ [int_ 4] using eqExpr in

  utest evaln (utensorShape_ (utensorReshapeExn_ t0 (seq_ [int_ 1])))
  with seq_ [int_ 1] using eqExpr in

  utest evaln (utensorShape_ (utensorReshapeExn_ t1 (seq_ [int_ 2, int_ 2])))
  with seq_ [int_ 2, int_ 2] using eqExpr in

  utest evaln (utensorCopyExn_ t1 t2) with unit_ using eqExpr in

  utest evaln (utensorRank_ (utensorSliceExn_ t1 (seq_ [int_ 0])))
  with int_ 0 using eqExpr in

  utest evaln (utensorShape_ (utensorSliceExn_ t1 (seq_ [int_ 0])))
  with seq_ [] using eqExpr in

  utest evaln (utensorRank_ (utensorSubExn_ t1 (int_ 0) (int_ 2)))
  with int_ 1 using eqExpr in

  utest evaln (utensorShape_ (utensorSubExn_ t1 (int_ 0) (int_ 2)))
  with seq_ [int_ 2] using eqExpr in

  let t3 = eval (utensorCreate_ (seq_ [int_ 3]) (ulam_ "x" v.0)) in
  let f = eval (ulam_ "i"
                  (ulam_ "x"
                     (utensorCopyExn_ (var_ "x") (var_ "x"))))
  in
  utest evaln (utensorIteri_ f t3) with unit_ using eqExpr in
  ()
in

let t3 = eval (utensorCreate_ (seq_ [int_ 3]) (ulam_ "x" (int_ 0))) in
let f = eval (ulam_ "i"
                (ulam_ "x"
                   (utensorSetExn_ (var_ "x") (seq_ []) (var_ "i"))))
in

let evaln = evalNoSymbolize in

utest evaln (utensorIteri_ f t3) with unit_ using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 0])) with int_ 0 using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 1])) with int_ 1 using eqExpr in
utest evaln (utensorGetExn_ t3 (seq_ [int_ 2])) with int_ 2 using eqExpr in

testTensors (int_ 0, int_ 1, int_ 2);
testTensors (float_ 0., float_ 1., float_ 2.);
testTensors (seq_ [int_ 0], seq_ [int_ 1], seq_ [int_ 2]);

()
