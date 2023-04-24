
include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/cfa.mc" -- only for freevariables
include "mexpr/symbolize.mc"

include "mexpr/mexpr.mc"

include "list.mc"
include "seq.mc"
include "set.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"
include "either.mc"

lang SpecializeLift = SpecializeAst + SpecializeUtils + MExprAst + ClosAst

  type LiftResult = (SpecializeArgs, Expr)

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : SpecializeNames -> SpecializeArgs -> Expr -> LiftResult
  sem liftExpr names args = | t -> printLn "Don't know how to lift this yet!"; (args, t)

  sem liftExprAccum : SpecializeNames -> SpecializeArgs -> [Expr] ->
                      (SpecializeArgs, [Expr])
  sem liftExprAccum names args =
  | xs -> mapAccumL (lam args. lam e. liftExpr names args e) args xs

  sem createConApp : SpecializeNames ->  (SpecializeNames -> Name)
                    -> [(String, Expr)]
                    -> Expr -- TmConApp
  sem createConApp names getName =
  | bindings ->
    let rec = urecord_ bindings in
    nconapp_ (getName names) rec

  sem createConAppInfo names getName bindings =
  | info -> let bindings = cons ("info", liftInfo names info) bindings in
            createConApp names getName bindings

  sem createConAppExpr names getName bindings typ =
  | info -> let bindings = cons ("ty", liftType names typ) bindings in
            createConAppInfo names getName bindings info

  sem liftType : SpecializeNames -> Type -> Expr
  sem liftType names =
  | t -> match tyConInfo t with (info, getName) in
    createConAppInfo names getName [] info

  sem tyConInfo : Type -> (Info, (SpecializeNames -> Name))
  sem tyConInfo =
  -- Right now, the partial evaluator is not able to propagate types,
  -- so we need to type check the AST later anyhow. Hence, use unknown type.
  | t -> (NoInfo(), tyUnknownName)

  sem liftName : SpecializeArgs -> Name -> LiftResult
  sem liftName args = | name ->
    match mapLookup name args.idMapping with Some t then
      (args, utuple_ [str_ name.0, nvar_ t])
    else let idm = nameSym "idm" in
      let args = {args with idMapping = mapInsert name idm args.idMapping} in
      (args, utuple_ [str_ name.0, nvar_ idm])

  sem liftInfo : SpecializeNames -> Info -> Expr
  sem liftInfo names =
  | _ -> createConApp names noInfoName []
    
  sem liftStringToSID : SpecializeNames -> String -> Expr
  sem liftStringToSID names = | x ->
   app_ (nvar_ (stringToSidName names)) (str_ x)

end

lang SpecializeLiftApp = SpecializeLift + AppAst

  sem liftExpr names args =
  | TmApp {lhs = lhs, rhs = rhs, info = info, ty=typ} ->
    match liftExprAccum names args [lhs, rhs] with (args, [lhs, rhs]) in
    let bindings = [("lhs", lhs), ("rhs", rhs)] in
    (args, createConAppExpr names tmAppName bindings typ info)

  sem tyConInfo =
  | TyApp {info = info, lhs = lhs, rhs=rhs} -> (info, tyAppName)
end

lang SpecializeLiftVar = SpecializeLift + VarAst

  sem liftViaType : SpecializeNames -> SpecializeArgs -> Name -> Type -> Option LiftResult
  sem liftViaType names args varName =
  | TyUnknown _ | TyArrow _ ->
    match mapLookup varName args.lib with Some t then
      let args = updateClosing args false in
      Some (liftExpr names args t)
    else None ()
  | t ->
    match liftViaTypeH names varName t with Some t then Some (args, t)
    else None ()

  sem _liftBasicType : SpecializeNames -> Name -> Type -> Option Expr
  sem _liftBasicType names varName =
  | typ -> let biStr =
  switch typ
    case TyInt _ then "int"
    case TyFloat _ then "float"
    case TyBool _ then "bool"
    case TyChar _ then "char"
    case _ then error "Cannot lift via this type"
  end in
  let lv = TmVar {ident = varName, ty=typ, info = NoInfo (), frozen = false} in
  let bindings = [("val", lv)] in
  let const = createConApp names (getBuiltinName biStr) bindings in
  let bindings = [("val", const)] in
  Some (createConAppExpr names tmConstName bindings typ (NoInfo ()))

  -- NOTE(adamssonj, 2023-03-31): Can't do anything with e.g. [(a->b)] aon
  sem liftViaTypeH : SpecializeNames -> Name -> Type -> Option Expr
  sem liftViaTypeH names varName =
  | t & (TyInt _ | TyFloat _ | TyChar _ | TyBool _) ->
    _liftBasicType names varName t
  | TySeq {info = info, ty = ty} & typ->
    let sq = TmVar {ident = varName, ty=typ, info = NoInfo (),
                    frozen = false} in
    -- TODO: Should not be unsymbolized "x"
    match liftViaTypeH names (nameNoSym "x") ty with Some t then
        let convert = (lam_ "x" ty t) in
        let tms = map_ convert sq in
        let bindings = [("tms", tms)] in
        Some (createConAppExpr names tmSeqName bindings ty info)
    else None () -- We don't know how to lift element types
  | TyRecord {info=info, fields=fields} & typ ->
    -- fields : Map SID Type
    let rec = TmVar {ident = varName, ty = typ, info = NoInfo (),
                    frozen = false} in

    let seqFields = mapToSeq fields in
    let patternList = map (lam x. let s = sidToString x.0 in
                        (s, pvar_ s)) seqFields in

    let pat = prec_ patternList in
    -- Create one lifted type per record entry
    -- Should probably do it only once per type, and map id -> typelift
    let seqFieldsWithLift = map (lam x. (x.0, x.1,
                 liftViaTypeH names (nameNoSym "x") x.1)) seqFields in

    -- If we cannot lift any of the present types
    if any (lam x. optionIsNone x.2) seqFieldsWithLift then None ()
    else
    let s = seq_ (map (lam x.
      let s = sidToString x.0 in
      match x.2 with Some t in
        let convert = (lam_ "x" x.1 t) in
        let liftedType = app_ convert (var_ s) in
        utuple_ [liftStringToSID names s, liftedType]) seqFieldsWithLift)
      in
    let thn = appf2_ (nvar_ (mapFromSeqName names)) (uconst_ (CSubi ())) s in
    let mbind = matchex_ rec pat thn in

    let bindings = [("bindings", mbind)] in
    Some (createConAppExpr names tmRecName bindings typ info)
  | t -> None ()


  sem liftExpr names args =
  | TmVar {ident = id, ty = typ, info = info, frozen = frozen} ->
    match liftName args id with (args, lIdent) in
    let bindings = [("ident", lIdent),
                    ("frozen", bool_ frozen)] in
    (args, createConAppExpr names tmVarName bindings typ info)

  sem tyConInfo =
  | TyVar {info = info, ident = id, level = lv} -> (info, tyVarName)

end

lang SpecializeLiftRecord = SpecializeLift + RecordAst

  sem liftExpr names args =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    match unzip (mapToSeq binds) with (ids, exprs) in
    match liftExprAccum names args exprs with (args, lExprs) in
    let binSeq = zip ids lExprs in
    let exprs =  seq_ (map (lam x. utuple_
      [liftStringToSID names (sidToString x.0) ,x.1]) binSeq) in
    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let bin = appf2_ lhs rhs exprs in
    let bindings = [("bindings", bin)] in
    (args, createConAppExpr names tmRecName bindings typ info)
end

lang SpecializeLiftSeq = SpecializeLift
  sem liftExpr names args =
  | TmSeq {tms = exprs, ty = typ, info = info} ->
    match liftExprAccum names args exprs with (args, lExprs) in
    let bindings = [("tms", seq_ lExprs)] in
    (args, createConAppExpr names tmSeqName bindings typ info)
end

lang SpecializeLiftConst = SpecializeLift + ConstAst

  sem buildConstBindings : Const -> [(String, Expr)]
  sem buildConstBindings =
  | CInt {val = v} -> [("val", int_ v)]
  | CFloat {val = v} -> [("val", float_ v)]
  | CBool {val = v} -> [("val", bool_ v)]
  | CChar {val = v} -> [("val", char_ v)]
  | CSymb {val = v} -> error "Cannot lift symbols as consts"
  | t -> []

  sem liftExpr names args =
  | TmConst {val = const, ty = typ, info = info} ->
    let bindings = buildConstBindings const in
    -- Build "Const"
    let const = createConApp names (getBuiltinNameFromConst const) bindings in
    let bindings = [("val", const)] in
    (args, createConAppExpr names tmConstName bindings typ info)

  sem tyConInfo =
  | TyInt {info = info} -> (info, tyIntName)
  | TyBool {info = info} -> (info, tyBoolName)
  | TyFloat {info = info} -> (info, tyFloatName)
  | TyChar {info = info} -> (info, tyCharName)

end


lang SpecializeLiftSpecialize = SpecializeLift + VarAst + SpecializeAst

  sem liftExpr names args =
  | TmSpecialize {e = expr, info = info} ->
    error "Nested peval"
end


lang SpecializeLiftLam = SpecializeLift + LamAst + MExprFreeVars + SpecializeLiftVar

  sem liftConsList : SpecializeNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) -> let bindings = [("0", a), ("1", liftConsList names b)] in
        createConApp names listConsName bindings
  | Nil _ -> createConApp names listNilName []

  sem buildEnv : SpecializeNames -> SpecializeArgs -> Map Name Type -> LiftResult
  sem buildEnv names args =
  | fvs ->
    let fvs = mapToSeq fvs in -- [(Name, Type])
    match liftAllViaType names args fvs with (args, liftedEnvItems) in
    match eitherPartition liftedEnvItems with (fvs, liftedExprs) in
    -- For the fvs that we couldn't lift, there's a chance they're reclet binds
    match handleRecLet names args fvs with (args, liftedEnvItems) in
    let liftedExprs = concat liftedExprs (filterOption liftedEnvItems) in
    let lenv = liftConsList names (listFromSeq liftedExprs) in
    (args, lenv)


  sem handleRecLet : SpecializeNames -> SpecializeArgs -> [Name] ->
                     (SpecializeArgs, [Option Expr])
  sem handleRecLet names args =
  | ns ->
    -- [([Name], RecLetBinding)]
    let binds = filterOption (map (lam name. mapLookup name args.rlMapping) ns) in
    let ns = join (map (lam bs:([Name], RecLetBinding). bs.0) binds) in
    let ns = setToSeq (setOfSeq nameCmp ns) in -- [Name] unique
    mapAccumL (lam acc. lam name.
        match mapLookup name args.rlMapping with Some t then
          -- Reclet bindings should have a rhs that is a TmLam
          -- I.e. liftViaType <=> liftExpr
          match t with (_, rlb) in
          match liftExpr names args rlb.body with (acc, liftedExpr) in
          match liftName acc name with (acc, liftedName) in
           (acc, Some (utuple_ [liftedName, liftedExpr]))
        else (acc, None ())) args ns

  sem liftAllViaType : SpecializeNames -> SpecializeArgs -> [(Name, Type)] ->
                      (SpecializeArgs, [Either Name Expr])
  sem liftAllViaType names args =
  | ts -> mapAccumL (lam acc. lam t : (Name, Type).
    match liftViaType names acc t.0 t.1 with Some (acc, expr) then
      match liftName acc t.0 with (acc, liftedName) in
        (acc, Right (utuple_ [liftedName, expr]))
    else (acc, Left (t.0))) args ts

  sem getTypesOfVars : Set Name -> Map Name Type -> Expr -> Map Name Type
  sem getTypesOfVars freeVars varMapping =
  | TmVar {ident=id, ty=ty} ->
    if setMem id freeVars then mapInsert id ty varMapping
    else varMapping
  | ast -> sfold_Expr_Expr (getTypesOfVars freeVars) varMapping ast

  sem getLiftedEnv : SpecializeNames -> SpecializeArgs -> [Name] -> Expr -> LiftResult
  sem getLiftedEnv names args exclude =
  | expr ->
    -- From /mexpr/cfa.mc
    let fvs = freeVars expr in
    let fvs = setSubtract fvs (setOfSeq nameCmp exclude) in
    let typedFvs = getTypesOfVars fvs (mapEmpty nameCmp) expr in
    buildEnv names args typedFvs

  sem liftExpr names args =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
    if isClosing args then -- TmLam
      match liftExpr names args body with (args, lExpr) in
      match liftName args id with (args, lName) in
      let dummyType = liftType names tyunknown_ in
      let bindings = [("ident", liftName names id), ("body", lBody),
                      ("tyAnnot", dummyType), ("tyParam", dummyType)] in
      createConAppExpr names tmLamName bindings typ info
    else -- Create closure
      let args = updateClosing args true in
      match liftExpr names args body with (args, lBody) in
      match getLiftedEnv names args [id] body with (args, liftedEnv) in
      match liftName args id with (args, liftedName) in
      let lazyLEnv = lam_ "t" tyunit_ liftedEnv in
      let bindings = [("ident", liftedName), ("body", lBody),
                      ("env", lazyLEnv)] in
      (args, createConAppInfo names tmClosName bindings info)
end


lang SpecializeLiftMatch = SpecializeLift + MatchAst

  sem liftPatName names args =
  | PName id -> match liftName args id with (args, lName) in
    let v = nconapp_ (pNameName names) lName in
    (args, v)
  | PWildcard _ -> let v = createConApp names pWildcardName [] in
    (args, v)

  sem liftPattern names args =
  | PatInt {val = v, info = info, ty=ty} ->
    let bindings = [("val", int_ v)] in
    (args, createConAppExpr names patIntName bindings ty info)
  | PatNamed {ident=ident, info=info, ty=ty} ->
    match liftPatName names args ident with (args, lPatName) in
    let bindings = [("ident", lPatName)] in
    (args, createConAppExpr names patNamedName bindings ty info)

  sem liftExpr names args =
  | TmMatch {target=target, pat=pat, thn=thn, els=els, ty=ty, info=info} ->
    match liftPattern names args pat with (args, lPat) in
    match liftExprAccum names args [target, thn, els]
      with (args, [lTarget, lThn, lEls]) in
    let bindings = [("target", lTarget), ("pat", lPat),
                    ("thn", lThn), ("els", lEls)] in
    (args, createConAppExpr names tmMatchName bindings ty info)
end


lang SpecializeLiftLet = SpecializeLift + LetAst

  sem liftExpr names args =
  | TmLet {ident=ident, body=body, inexpr=inexpr, ty=ty, info=info} ->
    match liftExprAccum names args [body, inexpr] with (args, [lBody, lInex]) in
    match liftName args ident with (args, lName) in
    let dummyType = liftType names tyunknown_ in
    let bindings = [("ident", lName), ("body", lBody), ("inexpr", lInex),
                  ("tyAnnot", dummyType), ("tyBody", dummyType)] in
    (args, createConAppExpr names tmLetName bindings ty info)

end

lang SpecializeLiftMExpr =
    SpecializeLiftApp + SpecializeLiftVar + SpecializeLiftRecord +
    SpecializeLiftSeq + SpecializeLiftConst + SpecializeLiftLam + SpecializeLiftSpecialize +
    SpecializeLiftMatch + SpecializeLiftLet

end


lang TestLang = SpecializeLiftMExpr + MExprPrettyPrint + MExprEval + MExprSym
                + MExprEq
end

lang SetupLang = SpecializeInclude + SpecializeUtils end

let _setup =
  use SetupLang in
  let ast = ulet_ "t" (int_ 3) in
  match includeSpecialize ast with (ast, pevalNames) in
  match includeConstructors ast with ast in
  -- Find the names of the functions and constructors needed later
  let names = createNames ast pevalNames in
  (ast, names)

mexpr
-- Possible idea:
--  Define expr:
--      1. Lift expr
--      2. Pprint lifted expr, and then interpret it. Is this = to interpreting expr directly?
use TestLang in
--
---- Dummy AST s.t. constructors and funcs can be included and used in lifting
match _setup with (startAst, names) in

let args = initArgs () in


let _parse =
  parseMExprString
    (_defaultBootParserParseMExprStringArg ())
in

let _eval = lam x.
  let x = symbolize x in
  eval (evalCtxEmpty ()) x in

let _parseEval = lam x:String. 
  let x = _parse x in 
  _eval x in

let _liftExpr = lam names. lam args. lam e.
  match liftExpr names args e with (_, k) in k
in
--
------------ TmApp -----------------
--

let e = addi_ (int_ 1) (int_ 3) in -- 1 + 3
let k = _liftExpr names args e in

let expected = nconapp_ (tmAppName names) (urecord_
    [("lhs", _liftExpr names args (app_ (uconst_ (CAddi ())) (int_ 1))),
     ("rhs", _liftExpr names args (int_ 3)),
     ("ty", liftType names tyunknown_),
     ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmVar -----------------
--

let e = var_ "t" in
let k = _liftExpr names args e in

let expected = nconapp_ (tmVarName names) (urecord_
    [("ident", utuple_ [str_ "t", nvar_ (noSymbolName names)]),
     ("frozen", bool_ false),
     ("ty", liftType names tyunknown_),
     ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmRecord -----------------
let e = urecord_ [("a", int_ 3), ("b", int_ 4)] in
let k = liftExpr names args e in

------------ TmSeq -------------------

let e = seq_ (map int_ [1,2,3]) in
let k = liftExpr names args e in

------------ TmConst -----------------

let e = int_ 3 in
let k = liftExpr names args e in

--
------------ TmLam -----------------
----

let e = ulam_ "x" (addi_ (var_ "x") (int_ 3)) in
let k = liftExpr names args e in

--
------------ TmMatch -----------------
--

let e = match_ (int_ 3) (pvar_ "wo") (int_ 5) (int_ 6) in
let k = liftExpr names args e in

--
------------ TmLet -----------------
--

let e = bind_ (ulet_ "x" (int_ 3)) (addi_ (int_ 4) (var_ "x")) in
let k = liftExpr names args e in


()
