
include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"
include "mexpr/cfa.mc" -- only for freevariables

include "list.mc"
include "set.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"


lang SpecializeLift = SpecializeAst + SpecializeUtils + MExprAst + ClosAst

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : SpecializeNames -> Map Name Expr -> Bool -> Expr -> Expr
  sem liftExpr names lib closing = | t -> printLn "Don't know how to lift this yet!"; t

  sem createConApp : SpecializeNames ->  (SpecializeNames -> Name)
                    -> [(String, Expr)] -> Type
                    -> Expr -- TmConApp
  sem createConApp names getName bindings =
  | typ -> --let ltype = liftType names typ in
           let rec = urecord_ bindings in
           nconapp_ (getName names) rec

  sem createConAppInfo names getName bindings typ =
  | info -> let bindings = cons ("info", liftInfo names info) bindings in
            createConApp names getName bindings typ


  sem createConAppExpr names getName bindings typ =
  | info -> let bindings = cons ("ty", liftType names typ) bindings in
            createConAppInfo names getName bindings typ info

  sem liftType : SpecializeNames -> Type -> Expr
  sem liftType names =
  | t -> match tyConInfo t with (info, getName) in
    createConAppInfo names getName [] tyunknown_ info

  sem tyConInfo : Type -> (Info, (SpecializeNames -> Name))
  sem tyConInfo =
  | TyUnknown {info = info} -> (info, tyUnknownName) 
  -- | TyArrow {info = info, from = from, to = to} -> (info, tyArrowName)
  | t -> printLn "Don't know how to lift this type"; (NoInfo(), tyUnknownName)

  sem liftName : SpecializeNames -> (String, Symbol) -> Expr
  sem liftName names = | tup ->
    --TODO(adamssonj, 2023-03-30): Should try to preserve the symbol
    let nosym = nvar_ (noSymbolName names) in
    utuple_ [str_ tup.0, symb_ tup.1]

  sem liftInfo : SpecializeNames -> Info -> Expr
  sem liftInfo names =
  | _ -> createConApp names noInfoName [] tyunknown_
    

  sem liftStringToSID : SpecializeNames -> String -> Expr
  sem liftStringToSID names = | x ->
   app_ (nvar_ (stringToSidName names)) (str_ x)

end

lang SpecializeLiftApp = SpecializeLift + AppAst

  sem liftExpr names lib closing =
  | TmApp {lhs = lhs, rhs = rhs, info = info, ty=typ} ->
    let lhs = liftExpr names lib closing lhs in -- Should be either TmVar or TmConst
    let rhs = liftExpr names lib closing rhs in
    let bindings = [("lhs", lhs), ("rhs", rhs)] in
    createConAppExpr names tmAppName bindings typ info

  sem tyConInfo =
  | TyApp {info = info, lhs = lhs, rhs=rhs} -> (info, tyAppName)
end

lang SpecializeLiftVar = SpecializeLift + VarAst

  sem liftViaType : SpecializeNames -> Map Name Expr -> Name -> Type -> Option Expr
  sem liftViaType names lib varName =
  | TyInt {info = info} & typ ->
    let lv = TmVar {ident = varName, ty=typ, info = NoInfo (), frozen = false} in
    let bindings = [("val", lv)] in
    let const = createConApp names (getBuiltinName "int") bindings typ in
    let bindings = [("val", const)] in
    Some (createConAppExpr names tmConstName bindings typ info)
  | TySeq {info = info, ty = ty} & typ->
    let sq = TmVar {ident = varName, ty=typ, info = NoInfo (),
                    frozen = false} in
    -- TODO: Should not be unsymbolized "x"
    match liftViaType names lib (nameNoSym "x") ty with Some t then
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
                 liftViaType names lib (nameNoSym "x") x.1)) seqFields in

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

  | ty ->
    match mapLookup varName lib with Some t then
      Some (liftExpr names lib false t)
    else
      None () -- We don't know how to lift this type and don't have its def.

  sem liftExpr names lib closing =
  | TmVar {ident = id, ty = typ, info = info, frozen = frozen} ->
    let bindings = [("ident", liftName names id),
                    ("frozen", bool_ frozen)] in
    createConAppExpr names tmVarName bindings typ info

  sem tyConInfo =
  | TyVar {info = info, ident = id, level = lv} -> (info, tyVarName)

end

lang SpecializeLiftRecord = SpecializeLift + RecordAst

  sem liftExpr names lib closing =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    let binSeq = mapToSeq binds in
    let exprs =  seq_ (map (lam x. utuple_
                      [liftStringToSID names (sidToString x.0), liftExpr names lib closing x.1])
                      binSeq) in
    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let bin = appf2_ lhs rhs exprs in
--    let lhs = app_ lhs rhs in
--    let bin = app_ lhs exprs in
    let bindings = [("bindings", bin)] in
    createConAppExpr names tmRecName bindings typ info

    
end

lang SpecializeLiftSeq = SpecializeLift
  sem liftExpr names lib closing =
  | TmSeq {tms = exprs, ty = typ, info = info} ->
    let exprs = map (liftExpr names lib closing) exprs in
    let bindings = [("tms", seq_ exprs)] in
    createConAppExpr names tmSeqName bindings typ info

end

lang SpecializeLiftConst = SpecializeLift + ConstAst

  sem buildConstBindings : Const -> [(String, Expr)]
  sem buildConstBindings =
  | CInt {val = v} -> [("val", int_ v)]
  | CFloat {val = v} -> [("val", float_ v)]
  | CBool {val = v} -> [("val", bool_ v)]
  | CChar {val = v} -> [("val", char_ v)]
  | CSymb {val = v} -> [("val", symb_ v)]
  | t -> []

  sem liftExpr names lib closing =
  | TmConst {val = const, ty = typ, info = info} & t ->
    let bindings = buildConstBindings const in
    -- Build "Const"
    let const = createConApp names (getBuiltinNameFromConst const) bindings typ in
    let bindings = [("val", const)] in
    createConAppExpr names tmConstName bindings typ info

  sem tyConInfo =
  | TyInt {info = info} -> (info, tyIntName)
  | TyBool {info = info} -> (info, tyBoolName)
  | TyFloat {info = info} -> (info, tyFloatName)
  | TyChar {info = info} -> (info, tyCharName)

end


lang SpecializeLiftSpecialize = SpecializeLift + VarAst + SpecializeAst

  sem liftExpr names lib closing =
  | TmSpecialize {e = expr, info = info} ->
    error "Nested peval"
end


lang SpecializeLiftLam = SpecializeLift + LamAst + MExprFreeVars + SpecializeLiftVar

  sem liftConsList : SpecializeNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) -> let bindings = [("0", a), ("1", liftConsList names b)] in
        createConApp names listConsName bindings tyunknown_
  | Nil _ -> createConApp names listNilName [] tyunknown_


  sem gg : SpecializeNames -> Map Name Expr -> List Expr -> Name -> Type -> List Expr
  sem gg names lib ls id =
  | typ ->
    match liftViaType names lib id typ with Some expr then
    listCons (utuple_ [liftName names id, expr]) ls
    else ls

  sem buildEnv : SpecializeNames -> Map Name Expr -> Map Name Type -> List Expr
  sem buildEnv names lib =
  | fvs -> mapFoldWithKey (gg names lib) listEmpty fvs

  sem getTypesOfVars : Set Name -> Map Name Type -> Expr -> Map Name Type
  sem getTypesOfVars freeVars varMapping =
  | TmVar {ident=id, ty=ty} ->
    if setMem id freeVars then mapInsert id ty varMapping
    else varMapping
  | ast -> sfold_Expr_Expr (getTypesOfVars freeVars) varMapping ast

  sem getLiftedEnv : SpecializeNames -> Map Name Expr -> [Name] -> Expr -> Expr
  sem getLiftedEnv names lib exclude =
  | expr ->
    -- From /mexpr/cfa.mc
    let fvs = freeVars expr in
    let fvs = setSubtract fvs (setOfSeq nameCmp exclude) in
    let typedFvs = getTypesOfVars fvs (mapEmpty nameCmp) expr in
    let env = buildEnv names lib typedFvs in
    liftConsList names env

  sem liftExpr names lib closing =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
    if closing then
      let lBody = liftExpr names lib closing body in
      let dummyType = liftType names tyunknown_ in
      let bindings = [("ident", liftName names id), ("body", lBody),
                      ("tyAnnot", dummyType), ("tyParam", dummyType)] in
      createConAppExpr names tmLamName bindings typ info
    else -- Create closure
      let lBody = liftExpr names lib true body in
      let liftedEnv = getLiftedEnv names lib [id] body in
      let lazyLEnv = lam_ "t" tyunit_ liftedEnv in
      let bindings = [("ident", liftName names id), ("body", lBody),
                      ("env", lazyLEnv)] in
      -- TmClos lazy evalEnv
      createConAppInfo names tmClosName bindings typ info

end

lang SpecializeLiftMExpr =
    SpecializeLiftApp + SpecializeLiftVar + SpecializeLiftRecord +
    SpecializeLiftSeq + SpecializeLiftConst + SpecializeLiftLam + SpecializeLiftSpecialize
end


lang TestLang = SpecializeLiftMExpr + MExprPrettyPrint + MExprEval + MExprTypeCheck + MExprSym
                + MExprEq + MExprEval
end

lang SetupLang = SpecializeInclude + SpecializeUtils end

let _setup =
  use SetupLang in
  let ast = ulet_ "t" (int_ 3) in
  match includeSpecialize ast with (ast, pevalNames) in
  match includeConstructors ast with ast in
  -- Find the names of the functions and constructors needed later
  let names = createNames ast pevalNames in
  names

mexpr
-- Possible idea:
--  Define expr:
--      1. Lift expr
--      2. Pprint lifted expr, and then interpret it. Is this = to interpreting expr directly?
use TestLang in
--
---- Dummy AST s.t. constructors and funcs can be included and used in lifting
let names = _setup in
--
--let lib : Map Name Expr = (mapEmpty nameCmp) in
--
------------ TmApp -----------------
--
------------ TmVar -----------------
--
--let expr = var_ "f" in
--let lift = liftExpr names lib expr in
--
--
------------ TmRecord -----------------

let x = nameSym "x" in 

let expr = urecord_ [("abc", int_ 3), ("def", int_ 4)] in
let lift = liftExpr names expr in

printLn (mexprToString lift);

------------ TmSeq -----------------
--
------------ TmConst -----------------
--
------------ TmLam -----------------
--
()
