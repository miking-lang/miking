-- Defines a set of language fragments for lifting MExpr constructs, including
-- patterns and expressions. Semantically, liftExpr should satisfy
-- lower (liftExpr x) = x. The implementation uses the TmConApp term 
 
include "peval/extract.mc"
include "peval/ast.mc"
include "peval/utils.mc"

include "mexpr/ast-builder.mc"
include "mexpr/free-vars.mc"

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
  sem liftExpr names args = | t ->
    error (join ["Don't know how to lift this yet: ", (expr2str t)])

  sem liftExprAccum : SpecializeNames -> SpecializeArgs -> [Expr] -> (SpecializeArgs, [Expr])
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
  | info ->
    let bindings = cons ("info", liftInfo names info) bindings in
    createConApp names getName bindings

  sem createConAppExpr names getName bindings typ =
  | info ->
    let bindings = cons ("ty", liftType names typ) bindings in
    createConAppInfo names getName bindings info

  sem liftType : SpecializeNames -> Type -> Expr
  sem liftType names =
  | t -> match tyConInfo t with (info, getName) in
    createConAppInfo names getName [] info

  sem tyConInfo : Type -> (Info, (SpecializeNames -> Name))
  sem tyConInfo =
  -- Right now, the partial evaluator is not able to propagate types,
  -- so we need to type check the AST later anyhow.
  | t -> (NoInfo(), tyUnknownName)

  sem liftName : SpecializeNames -> SpecializeArgs -> Name -> LiftResult
  sem liftName names args = | name ->
    if nameHasSym name then
      match mapLookup name args.idMapping with Some t then
        (args, utuple_ [str_ name.0, nvar_ t])
      else let idm = nameSym "idm" in
        let args = {args with idMapping = mapInsert name idm args.idMapping} in
        (args, utuple_ [str_ name.0, nvar_ idm])
    else (args, utuple_ [str_ name.0, nvar_ (noSymbolName names)])


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
  | TyApp {info = info} -> (info, tyAppName)
end

lang SpecializeLiftVar = SpecializeLift + VarAst

  sem liftViaType : SpecializeNames -> SpecializeArgs -> Name -> Type -> Option LiftResult
  sem liftViaType names args varName =
  | TyUnknown _ | TyArrow _ ->
    None ()
  | t ->
    match liftViaTypeH args names varName t with Some t then Some t
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

  sem liftViaTypeH : SpecializeArgs -> SpecializeNames -> Name -> Type -> Option LiftResult
  sem liftViaTypeH args names varName =
  | t & (TyInt _ | TyFloat _ | TyChar _ | TyBool _) ->
    match _liftBasicType names varName t with Some res in
    Some (args, res)
  | TySeq {info = info, ty = ty} & typ->
    let sq = TmVar {ident = varName, ty=typ, info = NoInfo (),
                    frozen = false} in
    let mapArg = nameSym "x" in
    match liftViaTypeH args names mapArg ty with Some (args, t) then
      let convert = (nlam_ mapArg ty t) in
      let tms = map_ convert sq in
      let bindings = [("tms", tms)] in
      Some (args, createConAppExpr names tmSeqName bindings ty info)
    else None () -- We don't know how to lift element types
  | TyRecord {info=info, fields=fields} & typ ->
    -- fields : Map SID Type
    let rec = TmVar {ident = varName, ty = typ, info = NoInfo (),
                    frozen = false} in

    let seqFields = map (lam x: (SID, Type).
      let str = sidToString x.0 in {str = str, ty = x.1, name = nameSym str}
      ) (mapToSeq fields) in

    let patternList = map (lam x. (x.str, npvar_ x.name)) seqFields in
    let pat = prec_ patternList in

    -- Create one lifted type per record entry
    -- Should probably do it only once per type, and map id -> typelift
    match mapAccumL (lam args. lam x.
      match
        match liftViaTypeH args names x.name x.ty with Some t then t
        else let v =
          TmVar {ident = x.name, ty = x.ty, info = NoInfo (), frozen=false} in
          liftExpr names args v
      with (args, lift) in (args, {str = x.str, lift = lift})) args seqFields
    with (args, newBindings) in

    let s = seq_ (map (lam x.
      utuple_ [liftStringToSID names x.str, x.lift]) newBindings)
    in
    -- "subi" = cmpSID
    let thn = appf2_ (nvar_ (mapFromSeqName names)) (uconst_ (CSubi ())) s in
    let matchbind = matchex_ rec pat thn in
    let bindings = [("bindings", matchbind)] in
    Some (args, createConAppExpr names tmRecName bindings typ info)
  | _ -> None ()

  sem liftExpr names args =
  | TmVar {ident = id, ty = typ, info=info, frozen=frozen} & t->
    match liftName names args id with (args, lIdent) in
    let bindings = [("ident", lIdent), ("frozen", bool_ frozen)] in
    (args, createConAppExpr names tmVarName bindings typ info)

  sem tyConInfo =
  | TyVar {info = info} -> (info, tyVarName)

end

lang SpecializeLiftRecord = SpecializeLift + RecordAst

  sem liftExpr names args =
  | TmRecord {bindings = binds, info=info, ty = typ} ->
    match unzip (mapToSeq binds) with (ids, exprs) in
    match liftExprAccum names args exprs with (args, lExprs) in

    let liftedBindings = seq_
      (zipWith (lam id. lam lExpr.
        let lId = liftStringToSID names (sidToString id) in
        utuple_ [lId, lExpr]) ids lExprs) in

    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let bin = appf2_ lhs rhs liftedBindings in
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
  | TmSpecialize _ ->
    error "Nested specialize"
end


lang SpecializeLiftLam = SpecializeLift + LamAst + MExprFreeVars + SpecializeLiftVar

  sem liftConsList : SpecializeNames -> List Expr -> Expr
  sem liftConsList names =
  | Cons (a, b) ->
    let bindings = [("0", a), ("1", liftConsList names b)] in
    createConApp names listConsName bindings
  | Nil _ -> createConApp names listNilName []

  sem buildEnv : SpecializeNames -> SpecializeArgs -> Map Name Type -> LiftResult
  sem buildEnv names args =
  | fvs ->
    let fvs = mapToSeq fvs in -- [(Name, Type])
    match liftAllViaType names args fvs with (args, liftedEnvItems) in
    -- "fvs" holds the free variables that we were unable to lift
    match eitherPartition liftedEnvItems with (fvs, liftedExprs) in
    let lenv = liftConsList names (listFromSeq liftedExprs) in
    (args, lenv)

  sem liftAllViaType : SpecializeNames -> SpecializeArgs -> [(Name, Type)] ->
                      (SpecializeArgs, [Either Name Expr])
  sem liftAllViaType names args =
  | ts -> mapAccumL (lam acc. lam t : (Name, Type).
    match liftViaType names acc t.0 t.1 with Some (acc, expr) then
      match liftName names acc t.0 with (acc, liftedName) in
        (acc, Right (utuple_ [liftedName, expr]))
    else (acc, Left (t.0))) args ts

  sem getTypesOfVars : Set Name -> Map Name Type -> Expr -> Map Name Type
  sem getTypesOfVars freeVars varMapping =
  | TmVar {ident=id, ty=ty} ->
    if setMem id freeVars then mapInsert id ty varMapping
    else varMapping
  | ast -> sfold_Expr_Expr (getTypesOfVars freeVars) varMapping ast

  sem getLiftedEnv : SpecializeNames -> SpecializeArgs -> Expr -> LiftResult
  sem getLiftedEnv names args =
  | expr ->
    let fvs = freeVars expr in
    let typedFvs = getTypesOfVars fvs (mapEmpty nameCmp) expr in
    buildEnv names args typedFvs

  sem liftExpr names args =
  | TmLam {ident=id, body = body, ty = typ, info = info} ->
    match liftExpr names args body with (args, lExpr) in
    match liftName names args id with (args, lName) in
    let dummyType = liftType names tyunknown_ in
    let bindings = [("ident", lName), ("body", lExpr),
                    ("tyAnnot", dummyType), ("tyParam", dummyType)] in
    (args, createConAppExpr names tmLamName bindings typ info)
end


lang SpecializeLiftMatch = SpecializeLift + MatchAst

  sem liftPatName names args =
  | PName id -> match liftName names args id with (args, lName) in
    let v = nconapp_ (pNameName names) lName in
    (args, v)
  | PWildcard _ -> let v = createConApp names pWildcardName [] in
    (args, v)

  sem _liftListOfPatterns names args =
  | pats ->
    mapAccumL (lam args. lam pat.
      liftPattern names args pat) args pats

  sem liftPattern names args =
  | PatInt {val = v, info = info, ty=ty} ->
    let bindings = [("val", int_ v)] in
    (args, createConAppExpr names patIntName bindings ty info)
  | PatNamed {ident=ident, info=info, ty=ty} ->
    match liftPatName names args ident with (args, lPatName) in
    let bindings = [("ident", lPatName)] in
    (args, createConAppExpr names patNamedName bindings ty info)
  | PatBool {val=v, ty=ty, info=info} ->
    let bindings = [("val", bool_ v)] in
    (args, createConAppExpr names patBoolName bindings ty info)
  | PatChar {val=v, ty=ty, info=info} ->
    let bindings = [("val", char_ v)] in
    (args, createConAppExpr names patCharName bindings ty info)
  | PatSeqTot {pats=pats, info=info, ty=ty} ->
    match _liftListOfPatterns names args pats with (args, pats) in
    let bindings = [("pats", seq_ pats)] in
    (args, createConAppExpr names patSeqTotName bindings ty info)
  | PatSeqEdge {prefix=pres, middle=mid, postfix=posts, info=info, ty=ty} ->
    match liftPatName names args mid with (args, mid) in
    match _liftListOfPatterns names args pres with (args, pres) in
    match _liftListOfPatterns names args posts with (args, posts) in
    let bindings = [("prefix", seq_ pres), ("middle", mid),
                    ("postfix", seq_ posts)] in
    (args, createConAppExpr names patSeqEdgeName bindings ty info)
  | PatRecord {bindings=bindings, info=info, ty=ty} ->
    -- bindings : Map SID Pat
    match unzip (mapToSeq bindings) with (ids, pats) in
    match _liftListOfPatterns names args pats with (args, pats) in
    let liftedBindings = seq_
      (zipWith (lam id. lam lPat.
        let lId = liftStringToSID names (sidToString id) in
        utuple_ [lId, lPat]) ids pats) in
    let lhs = nvar_ (mapFromSeqName names) in
    -- cmpSID = subi
    let rhs = (uconst_ (CSubi ())) in
    let binds = appf2_ lhs rhs liftedBindings in
    let lhs = nvar_ (mapFromSeqName names) in
    let bindings = [("bindings", binds)] in
    (args, createConAppExpr names patRecName bindings ty info)
  | PatCon {ident=ident, subpat=subpat, info=info, ty=ty} ->
    match liftName names args ident with (args, ident) in
    match liftPattern names args subpat with (args, subpat) in
    let bindings = [("ident", ident), ("subpat", subpat)] in
    (args, createConAppExpr names patConName bindings ty info)
  | PatAnd {lpat=lpat, rpat=rpat, info=info, ty=ty} ->
    match liftPattern names args lpat with (args, lpat) in
    match liftPattern names args rpat with (args, rpat) in
    let bindings = [("lpat", lpat), ("rpat", rpat)] in
    (args, createConAppExpr names patAndName bindings ty info)
  | PatOr {lpat=lpat, rpat=rpat, info=info, ty=ty} ->
    match liftPattern names args lpat with (args, lpat) in
    match liftPattern names args rpat with (args, rpat) in
    let bindings = [("lpat", lpat), ("rpat", rpat)] in
    (args, createConAppExpr names patOrName bindings ty info)
  | PatNot {subpat=subpat, info=info, ty=ty} ->
    match liftPattern names args subpat with (args, subpat) in
    let bindings = [("subpat", subpat)] in
    (args, createConAppExpr names patNotName bindings ty info)

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
    match liftName names args ident with (args, lName) in
    let dummyType = liftType names tyunknown_ in
    let bindings = [("ident", lName), ("body", lBody), ("inexpr", lInex),
                  ("tyAnnot", dummyType), ("tyBody", dummyType)] in
    (args, createConAppExpr names tmLetName bindings ty info)

end

lang SpecializeLiftRecLets = SpecializeLift + RecLetsAst

  sem liftRecLetsBindings names args =
  | binds ->
    let dummyInfo = liftInfo names (NoInfo ()) in
    let dummyType = liftType names tyunknown_ in
    let res = mapAccumL (lam acc. lam bind.
      match liftName names acc bind.ident with (acc, lName) in
      match liftExpr names acc bind.body with (acc, lBody) in
      (acc, urecord_ [("ident", lName), ("body", lBody),
                      ("tyBody", dummyType), ("tyAnnot", dummyType),
                      ("info", dummyInfo)])) args binds in
    match res with (args, lBinds) in
    let lBinds = seq_ lBinds in
    (args, lBinds)

  sem liftExpr names args =
  | TmRecLets {bindings = binds, inexpr = inexpr, ty=ty, info=info} ->
    match liftExpr names args inexpr with (args, lInexpr) in
    match liftRecLetsBindings names args binds with (args, lBinds) in
    let bindings = [("bindings", lBinds), ("inexpr", lInexpr)] in
    (args, createConAppExpr names tmRecLetsName bindings ty info)
end

lang SpecializeLiftDataAst = SpecializeLift + DataAst

  sem liftExpr names args =
  | TmConDef {ident=ident, tyIdent=tyId, inexpr=inexpr, ty=ty, info=info} ->
    match liftName names args ident with (args, ident) in
    match liftExpr names args inexpr with (args, inexpr) in
    let tyId = liftType names tyId in
    let bindings = [("ident", ident), ("tyIdent", tyId), ("inexpr", inexpr)] in
    (args, createConAppExpr names tmConDefName bindings ty info)
  | TmConApp {ident=ident, body=body, ty=ty, info=info} ->
    match liftName names args ident with (args, ident) in
    match liftExpr names args body with (args, body) in
    let bindings = [("ident", ident), ("body", body)] in
    (args, createConAppExpr names tmConAppName bindings ty info)
end

lang SpecializeLiftTypeAst = SpecializeLift + TypeAst

  sem liftExpr names args =
  | TmType {ident=ident, params=params, tyIdent=tyId, inexpr=inexpr,
            ty=ty, info=info} ->
    match liftName names args ident with (args, ident) in
    match (mapAccumL (lam args. lam name.
      liftName names args name) args params) with (args, params) in
    match liftExpr names args inexpr with (args, inexpr) in
    let tyId = liftType names tyId in
    let bindings = [("ident", ident), ("tyIdent", tyId),
                    ("params", seq_ params), ("inexpr", inexpr)] in
    (args, createConAppExpr names tmTypeName bindings ty info)
end


lang SpecializeLiftNever = SpecializeLift + NeverAst

  sem liftExpr names args =
  | TmNever {ty=ty, info=info} ->
    (args, createConAppExpr names tmNeverName [] ty info)
end

lang SpecializeLiftMExpr =
    SpecializeLiftApp + SpecializeLiftVar + SpecializeLiftRecord +
    SpecializeLiftSeq + SpecializeLiftConst + SpecializeLiftLam + SpecializeLiftSpecialize +
    SpecializeLiftMatch + SpecializeLiftLet + SpecializeLiftRecLets + SpecializeLiftDataAst +
    SpecializeLiftTypeAst + SpecializeLiftNever
end


lang TestLang = SpecializeLiftMExpr + MExprPrettyPrint + MExprEval + MExprSym
                + MExprEq
end

lang SetupLang = SpecializeInclude + SpecializeUtils end

let _createFakeNames = lam.
  use SetupLang in
  let toNameMap = lam ls. mapFromSeq cmpString (
    map (lam str. (str, nameSym str)) ls) in
  let pevalNames = toNameMap includeSpecializeNames in
  let consNames = toNameMap includeConsNames in
  let builtinsNames = toNameMap includeBuiltins in
  let tyConsNames = toNameMap includeTyConsNames in
  let otherFuncs = toNameMap includeOtherFuncs in
  {pevalNames = pevalNames,
   consNames = consNames,
   builtinsNames = builtinsNames,
   tyConsNames = tyConsNames,
   otherFuncs=otherFuncs}

let _setup =
  use SetupLang in
  let ast = ulet_ "t" (int_ 3) in
  let names = _createFakeNames () in
  (ast, names)

mexpr

use TestLang in

match _setup with (_, names) in

let args = initArgs (mapEmpty nameCmp) in

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


let someSym = nameSym "t" in
let e = nvar_ someSym in
match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someSym args.idMapping with Some t
  then t else someSym in

let expected = nconapp_ (tmVarName names) (urecord_
  [("ident", utuple_ [str_ "t", nvar_ newSymbol]),
   ("frozen", bool_ false),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmRecord -----------------
let e = urecord_ [("a", int_ 3), ("b", int_ 4)] in
let k = _liftExpr names args e in

-- Lift bindings map of record term ----
let bindings = seq_ [
  utuple_ [liftStringToSID names "a", _liftExpr names args (int_ 3)],
  utuple_ [liftStringToSID names "b", _liftExpr names args (int_ 4)]
] in

let liftedMap = appf2_ (nvar_ (mapFromSeqName names))
                       (uconst_ (CSubi ())) bindings in

let expected = nconapp_ (tmRecName names) (urecord_
  [("bindings", liftedMap),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

------------ TmSeq -------------------

let e = seq_ (map int_ [1,2,3]) in
let k = _liftExpr names args e in

match e with TmSeq {tms = tms} in
let liftedSeq = seq_ (map (_liftExpr names args) tms) in

let expected = nconapp_ (tmSeqName names) (urecord_
  [("tms", liftedSeq),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

------------ TmConst -----------------

let e = int_ 3 in
let k = _liftExpr names args e in

match e with TmConst {val = const} in

let lConst = nconapp_ (getBuiltinNameFromConst const names) (urecord_
  [("val", int_ 3)]) in

let expected = nconapp_ (tmConstName names) (urecord_
  [("val", lConst),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmLam -----------------
----

let someSym = nameSym "t" in

let e = nulam_ someSym (nvar_ someSym) in

match liftExpr names args e with (args, k) in
let newSymbol = match mapLookup someSym args.idMapping with Some t
  then t else someSym in

let ltype = liftType names tyunknown_ in

let expected = nconapp_ (tmLamName names) (urecord_
  [("ident",  utuple_ [str_ "t", nvar_ newSymbol]),
   ("tyAnnot", ltype),
   ("tyParam", ltype),
   ("body", _liftExpr names args (nvar_ someSym)),
   ("ty", ltype),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmMatch -----------------
--

let someSym = nameSym "t" in
let e = match_ (int_ 3) (npvar_ someSym) (int_ 5) (nvar_ someSym) in
match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someSym args.idMapping with Some t
  then t else someSym in

let pat = nconapp_ (patNamedName names) (urecord_
  [("ident", nconapp_ (pNameName names) (utuple_ [str_ "t", nvar_ newSymbol])),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

let expected = nconapp_ (tmMatchName names) (urecord_
  [("target", _liftExpr names args (int_ 3)),
   ("pat", pat),
   ("thn", _liftExpr names args (int_ 5)),
   ("els", _liftExpr names args (nvar_ someSym)),
   ("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmLet -----------------
--

let someSym = nameSym "t" in

let e = bind_ (nulet_ someSym (int_ 3)) (addi_ (int_ 4) (nvar_ someSym)) in

match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someSym args.idMapping with Some t
  then t else someSym in

let ltype = liftType names tyunknown_ in

let expected = nconapp_ (tmLetName names) (urecord_
  [("ident", utuple_ [str_ "t", nvar_ newSymbol]),
   ("body", _liftExpr names args (int_ 3)),
   ("inexpr", _liftExpr names args (addi_ (int_ 4) (nvar_ someSym))),
   ("tyAnnot", ltype),
   ("tyBody", ltype),
   ("ty", ltype),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmRecLets -----------------
--

let someSymbol = nameSym "n" in
let facSym = nameSym "factorial" in

let facBody = nulam_ someSymbol (
    if_ (eqi_ (nvar_ someSymbol) (int_ 0))
      (int_ 1)
      (muli_ (nvar_ someSymbol)
        (app_ (nvar_ facSym) (subi_ (nvar_ someSymbol) (int_ 1))))) in

let factorial = nureclets_ [
  (facSym, facBody)
] in

match liftExpr names args factorial with (args, k) in

let newSymbol = match mapLookup facSym args.idMapping with Some t
  then t else someSym in

let ltype = liftType names tyunknown_ in

let lrl = [urecord_ [("ident", utuple_ [str_ "factorial", nvar_ newSymbol]),
  ("tyAnnot", ltype), ("tyBody", ltype), ("info", liftInfo names (NoInfo ())),
  ("body", _liftExpr names args facBody)]] in

let expected = nconapp_ (tmRecLetsName names) (urecord_
  [("bindings", seq_ lrl),
   ("inexpr", _liftExpr names args (unit_)),
   ("ty", ltype),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmConDef -----------------
--

let someName = nameSym "test" in
let e = ncondef_ someName tyunknown_ in

match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someName args.idMapping with Some t
  then t else someName in

let dummyType = liftType names tyunknown_ in

let expected = nconapp_ (tmConDefName names) (urecord_
  [("ident", utuple_ [str_ "test", nvar_ newSymbol]),
   ("tyIdent", dummyType),
   ("ty", dummyType),
   ("inexpr", _liftExpr names args uunit_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmConApp -----------------
--

let someName = nameSym "test" in
let e = nconapp_ someName uunit_ in

match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someName args.idMapping with Some t
  then t else someName in

let dummyType = liftType names tyunknown_ in

let expected = nconapp_ (tmTypeName names) (urecord_
  [("ident", utuple_ [str_ "test", nvar_ newSymbol]),
   ("body", _liftExpr names args uunit_),
   ("ty", dummyType),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmType -----------------
--

let someName = nameSym "test" in
let e = ntype_ someName [] tyunknown_ in

match liftExpr names args e with (args, k) in

let newSymbol = match mapLookup someName args.idMapping with Some t
  then t else someName in

let dummyType = liftType names tyunknown_ in

let expected = nconapp_ (tmTypeName names) (urecord_
  [("ident", utuple_ [str_ "test", nvar_ newSymbol]),
   ("tyIdent", dummyType),
   ("ty", dummyType),
   ("inexpr", _liftExpr names args uunit_),
   ("params", seq_ []),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

--
------------ TmNever -----------------
--

let e = never_ in

let k = _liftExpr names args e in

let expected = nconapp_ (tmNeverName names) (urecord_
  [("ty", liftType names tyunknown_),
   ("info", liftInfo names (NoInfo ()))]) in

utest expected with k using eqExpr in

()
