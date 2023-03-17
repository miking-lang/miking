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
include "ocaml/generate.mc"
include "ocaml/generate-env.mc"


include "list.mc"
include "string.mc"
include "stringid.mc"
include "error.mc"


lang SpecializeLift = SpecializeAst + SpecializeUtils --+  MExprAst + ClosAst + SpecializeInclude + SpecializeExtract

  -- liftExpr should produce an Expr s.t. when evaluated produces its original input argument
  -- In that sense liftExpr can be considered an inverse of 'eval'
  sem liftExpr : SpecializeNames -> Map Name Expr -> Expr -> Expr
  sem liftExpr names lib = | t -> printLn "Don't know how to lift this yet!"; t

  sem createConApp : SpecializeNames ->  (SpecializeNames -> Name) 
                    -> [(String, Expr)] -> Type -> Info 
                    -> Expr -- TmConApp
  sem createConApp names getName bindings typ =
  | info -> let ltype = liftType names typ in
            let rec = tmRecord info ltype bindings in
            nconapp_ (getName names) rec

  sem liftType : SpecializeNames -> Type -> Type
  sem liftType names =
  | TyUnknown {info = info} ->
    TyCon {info = info, ident = (tyUnknownName names)}
  | t -> printLn "Don't know how to lift this TYPE yet: ";
         printLn (typeToString pprintEnvEmpty t); t

  sem liftName : (String, Symbol) -> Expr
  sem liftName = | tup -> 
    utuple_ [str_ tup.0, symb_ tup.1]
    
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
    createConApp names tmAppName bindings typ info
end

lang SpecializeLiftVar = SpecializeLift + VarAst

--  sem liftViaType : SpecializeNames -> Name -> Info -> Type  -> Expr
--  sem liftViaType names varName info =
--  | TyInt {info = info} & typ ->
--    let bindings = [("val", liftName varName)] in
--    createConApp names (getBuiltinName "int") bindings tyunknown_ info
--  | typ -> let bindings = [("ident", liftName varName)] in
--    createConApp names tmVarName bindings typ inf

  sem liftExpr names lib =
  | TmVar {ident = id, ty = typ, info = info} ->
    let bindings = [("ident", liftName id)] in
    createConApp names tmVarName bindings typ info
end

lang SpecializeLiftRecord = SpecializeLift + RecordAst

  sem liftExpr names lib =
  | TmRecord {bindings = binds, info=info, ty = typ} -> 
    let binSeq = mapToSeq binds in
    let bindings = map (lam x.  (sidToString x.0, liftExpr names lib x.1)) binSeq in
    createConApp names tmRecName bindings typ info
end

lang SpecializeLiftSeq = SpecializeLift
  sem liftExpr names lib =
  | TmSeq {tms = exprs, ty = typ, info = info} -> 
    let exprs = map (liftExpr names lib) exprs in
    let bindings = [("tms", seq_ exprs)] in
    createConApp names tmSeqName bindings typ info
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
    let const = createConApp names (getBuiltinNameFromConst const) bindings typ info in
    let bindings = [("val", const)] in
    createConApp names tmConstName bindings typ info
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

  sem liftExpr names lib =
  | TmSpecialize {e = expr, info = info} -> 
      let env = buildClosureEnv lib (evalEnvEmpty ()) expr in -- List (Name, Expr)
      let liftedEnv = seq_ (map (envItemToTuple names lib) (listToSeq env)) in
      let body = liftExpr names lib expr in 
      let bindings = [("body", body), ("env", liftedEnv)] in
      let clos = createConApp names tmClosName bindings tyunknown_ info in
      let lhs = nvar_ (pevalName names) in
      tmApp info tyunknown_ lhs clos

  sem liftType names =
  | TyVar {info = info, ident = ident, level = lv} ->
    TyCon {info = info, ident = (tyVarName names)}
end 


lang SpecializeLiftLam = SpecializeLift + LamAst
  sem liftExpr names lib =
  | TmLam {body = body, ty = typ, info = info} -> 
        let body = liftExpr names lib body in
        let bindings = [("body", body)] in
        createConApp names tmLamName bindings typ info
end

lang SpecializeLiftMExpr = 
    SpecializeLiftApp + SpecializeLiftVar + SpecializeLiftRecord +
    SpecializeLiftSeq + SpecializeLiftConst + SpecializeLiftLam + SpecializeLiftSpecialize
end


lang TestLang = SpecializeLiftMExpr + MExprPrettyPrint + MExprEval + MExprTypeCheck + MExprSym
                + MExprEq + OCamlGenerate
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

use TestLang in


-- Dummy AST s.t. constructors and funcs can be included and used in lifting
let names = _setup in

let lib : Map Name Expr = (mapEmpty nameCmp) in

---------- TmApp -----------------

--let expr =  (var_ "f") in
--printLn (mexprToString expr);
--let n = liftExpr names lib expr in
--printLn (mexprToString n);
--
--let e = generate (emptyGenerateEnv) n in
--
--printLn (mexprToString e);
--



---------- TmVar -----------------


---------- TmRecord -----------------


---------- TmSeq -----------------

---------- TmConst -----------------

---------- TmLam -----------------

()
