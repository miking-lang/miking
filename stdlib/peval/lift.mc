-- Include here all the lifting that is now performed inside compile.mc
-- Not sure yet whether to include the name handling
-- That should probably go in a different file, or utils?
--
--
-- Should also make sure that every lift works as expected by having at least one test per
-- constructor here
--

include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/eval.mc"

include "list.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"


lang SpecializeLift = SpecializeAst + SpecializeUtils + MExprAst + ClosAst

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : SpecializeNames -> Map Name Expr -> Expr -> Expr
  sem liftExpr names lib = | t -> printLn "Don't know how to lift this yet!"; t

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

  sem liftName : (String, Symbol) -> Expr
  sem liftName = | tup ->
    utuple_ [str_ tup.0, symb_ tup.1]

  sem liftInfo : SpecializeNames -> Info -> Expr
  sem liftInfo names =
--  | Info _ -> {col1=c1, col2=c2, row1=r1, row2=r2, filename=fn} 
--    ->
--    let bindings = [("col1", int_ c1), ("col2", int_ c2), ("row1", int_ r1),
--                    ("row2", int_ r2), ("filename", str_ fn)] in
--    createConApp names infoName bindings tyunknown_
  | _ -> createConApp names noInfoName [] tyunknown_
    

  -- Parse tuple to expr
  sem envItemToTuple : SpecializeNames -> Map Name Expr -> (Name, Expr) -> Expr
  sem envItemToTuple names lib = | tup ->
    let name = liftName tup.0 in
    let expr = liftExpr names lib tup.1 in
    utuple_ [name, expr]

end

lang SpecializeLiftApp = SpecializeLift + AppAst

  sem liftExpr names lib =
  | TmApp {lhs = lhs, rhs = rhs, info = info, ty=typ} ->
    let lhs = liftExpr names lib lhs in -- Should be either TmVar or TmConst
    let rhs = liftExpr names lib rhs in
    let bindings = [("lhs", lhs), ("rhs", rhs)] in
    createConAppExpr names tmAppName bindings typ info

  sem tyConInfo =
  | TyApp {info = info, lhs = lhs, rhs=rhs} -> (info, tyAppName)
end

lang SpecializeLiftVar = SpecializeLift + VarAst

--  sem liftViaType : SpecializeNames -> Name -> Info -> Type  -> Expr
--  sem liftViaType names varName info =
--  | TyInt {info = info} & typ ->
--    let bindings = [("val", liftName varName)] in
--    createConApp names (getBuiltinName "int") bindings tyunknown_ info
--  | typ -> let bindings = [("ident", liftName varName)] in
--    createConApp names tmVarName bindings typ inf

-- Var x 
-- int_ x. createConApp TmConst "val", "val, var x"
--
-- TmConst {val=CInt{val=x}}
-- Int => Rec => Seq

  sem liftExpr names lib =
  | TmVar {ident = id, ty = typ, info = info} ->
    let bindings = [("ident", liftName id)] in
    createConAppExpr names tmVarName bindings typ info

  sem tyConInfo =
  | TyVar {info = info, ident = id, level = lv} -> (info, tyVarName)

end

lang SpecializeLiftRecord = SpecializeLift + RecordAst

  sem liftExpr names lib =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    let binSeq = mapToSeq binds in
    let bindings = map (lam x.  (sidToString x.0, liftExpr names lib x.1)) binSeq in
    createConAppExpr names tmRecName bindings typ info
end

lang SpecializeLiftSeq = SpecializeLift
  sem liftExpr names lib =
  | TmSeq {tms = exprs, ty = typ, info = info} ->
    let exprs = map (liftExpr names lib) exprs in
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

  sem liftExpr names lib =
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

  sem buildClosureEnv (lib : Map Name Expr) (env : EvalEnv) =
  | TmVar t -> match mapLookup t.ident lib with Some b then
             evalEnvInsert t.ident b env else env
  | t -> sfold_Expr_Expr (buildClosureEnv lib) env t

  sem expandSpecialize (names : SpecializeNames) (lib : Map Name Expr) =
  | TmSpecialize e & pe ->
    liftExpr names lib pe
  | t -> smap_Expr_Expr (expandSpecialize names lib) t

  sem liftConsList : SpecializeNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) -> let bindings = [("0", a), ("1", liftConsList names b)] in
        createConApp names listConsName bindings tyunknown_
  | Nil _ -> createConApp names listNilName [] tyunknown_

  sem liftExpr names lib =
  | TmSpecialize {e = expr, info = info} ->
      let env = buildClosureEnv lib (evalEnvEmpty ()) expr in -- List (Name, Expr)
      let liftedEnv = listMap (envItemToTuple names lib) env in -- List Expr
      let liftedList = liftConsList names liftedEnv in -- Expr

      -- Probably wrong. Type checks but break when r.env () is called in peval.mc
      let reallyLiftedEnv = lam_ "t" tyunit_ liftedList in

      let body = liftExpr names lib expr in
      let bindings = [("body", body), ("env", reallyLiftedEnv),
                      ("ident", liftName (nameNoSym "t"))] in
      let clos = createConAppInfo names tmClosName bindings tyunknown_ info in
      let lhs = nvar_ (pevalName names) in
      tmApp info tyunknown_ lhs clos
end


lang SpecializeLiftLam = SpecializeLift + LamAst
  sem liftExpr names lib =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
        let body = liftExpr names lib body in
        let bindings = [("ident", liftName id), ("body", body)] in
        createConAppExpr names tmLamName bindings typ info
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
()
-- Possible idea:
--  Define expr:
--      1. Lift expr
--      2. Pprint lifted expr, and then interpret it. Is this = to interpreting expr directly?
--use TestLang in
--
---- Dummy AST s.t. constructors and funcs can be included and used in lifting
--let names = _setup in
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
--
--
------------ TmSeq -----------------
--
------------ TmConst -----------------
--
------------ TmLam -----------------
--
--()
