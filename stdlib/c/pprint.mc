include "ast.mc"

include "mexpr/pprint.mc"

-------------
-- HELPERS --
-------------

let _par = lam str. join ["(",str,")"] in

lang CPrettyPrint = CAst + PrettyPrint

  -------------------
  -- C IDENTIFIERS --
  -------------------
  sem printId (env: PprintEnv) =
  -- TODO: Throw error if id is not a valid C identifier
  | id -> pprintEnvGetStr env id


  -------------------
  -- C EXPRESSIONS --
  -------------------

  sem printExpr (env: PprintEnv) =

  | TmVar { id = id } -> printId env id

  | TmApp { fun = fun, args = args} ->
    match prindId env fun with (env,fun) then
      match mapAccumL printExpr env args with (env,args) then
        (env, _par (join [fun, "(", (strJoin ", " args)], ")"))
      else never
    else never

  | TmInt   { i = i } -> (env, int2string i)
  | TmFloat { f = f } -> (env, float2string f)
  | TmChar  { c = c } -> (env, ['\'', c, '\''])

  | TmUnOp { op = op, arg = arg } ->
    match printExpr env arg with (env,arg) then (env, _par (printUnOp arg op))
    else never

  | TmBinOp { op = op, lhs = lhs, rhs = rgs } ->
    match printExpr env lhs with (env,lhs) then
      match printExpr env rhs with (env,rhs) then
        (env, _par (printBinOp lhs rhs op))
      else never
    else never

  | TmMemb { lhs = lhs, id = id } ->
    match printExpr env lhs with (env,lhs) then
      match printId env id with (env,id)
        (env, _par (join [lhs, ".", id]))
      else never
    else never

  | TmCast { ty = ty, rhs = rhs } ->
    match printType env ty with (env,ty) then
      match printExpr env rhs with (env,rhs)
        (env, _par (join ["(",ty,") ", rhs]))
      else never
    else never

  | TmSizeOfType { ty = ty } ->
    match printType env ty with (env,ty) then
      (env, _par (join ["sizeof ", ty]))
    else never

  sem printBinOp (lhs: String) (rhs: String) =
  | OAssg   {} -> join [lhs, " = ", rhs]
  | OSubScr {} -> join [lhs, "[", rhs, "]"]
  | OOr     {} -> join [lhs, " || ", rhs]
  | OAnd    {} -> join [lhs, " && ", rhs]
  | OEq     {} -> join [lhs, " == ", rhs]
  | ONeq    {} -> join [lhs, " != ", rhs]
  | OLt     {} -> join [lhs, " < ", rhs]
  | OGt     {} -> join [lhs, " > ", rhs]
  | OLe     {} -> join [lhs, " <= ", rhs]
  | OGe     {} -> join [lhs, " >= ", rhs]
  | OShiftL {} -> join [lhs, " << ", rhs]
  | OShiftR {} -> join [lhs, " >> ", rhs]
  | OAdd    {} -> join [lhs, " + ", rhs]
  | OSub    {} -> join [lhs, " - ", rhs]
  | OMul    {} -> join [lhs, " * ", rhs]
  | ODiv    {} -> join [lhs, " / ", rhs]
  | OMod    {} -> join [lhs, " % ", rhs]
  | OBOr    {} -> join [lhs, " | ", rhs]
  | OBAnd   {} -> join [lhs, " & ", rhs]
  | OBXor   {} -> join [lhs, " ^ ", rhs]

  sem printUnOp (arg: String) =
  | OSizeOf {} -> join ["sizeof ", arg]
  | ODeref  {} -> join ["*", arg]
  | OAddrOf {} -> join ["&", arg]
  | ONeg    {} -> join ["-", arg]
  | ONot    {} -> join ["~", arg]


  -------------
  -- C TYPES --
  -------------

  sem printType (env: PprintEnv) =
  | TyIdent  { id = id } -> printId env id
  | TyChar   { }         -> (env,"char")
  | TyInt    { }         -> (env,"int")
  | TyDouble { }         -> (env,"double")
  | TyVoid   { }         -> (env,"void")


  -------------------
  -- C DEFINITIONS --
  -------------------

  sem printDef (env: PprintEnv) =
  | DVar { ty = ty, id = id, init = init } ->
    match printType env ty with (env,ty) then
      match printId env id with (env,id) then
        let decl = join [ty, " ", id] in
        match init with Some init then
          match printInit env init with (env,init) then
            (env, join [decl, " = ", init ";"])
          else never
        else (env, join [decl, ";"])
      else never
    else never

  sem printInit (env: PprintEnv) =
  | IExpr { expr = expr } -> printExpr env expr

  | IList { inits = inits } ->
    match mapAccumL printInit env inits with (env,inits) then
      (env, join ["{ ", strJoin ", " inits, " }"])
    else never


  ------------------
  -- C STATEMENTS --
  ------------------

  sem printStmt (indent : Int) (env: PprintEnv) =
  | SDef { def = def } -> printDef env def

  | SIf { cond = cond, thn = thn, els = els } ->
    let i = indent in
    let ii = pprintIncr i in
    match printExpr env cond with (env,cond) then
      match printStmt ii env thn with (env,thn) then
        match printStmt ii env els with (env,els) then
          (env, join ["if (", cond, ")", pprintNewline ii,
                      thn, pprintNewline i,
                      "else", pprintNewline ii, els])
        else never
      else never
    else never

  | SSwitch { cond = cond, body = body, default = default } ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    let iv = pprintIncr iii in
    match printExpr env cond with (env,cond) then
      let f = lam env. lam t.
        match printStmt iv env t.1 with (env,t1) then (t.0, t1) else never in
      match mapAccumL f env body with (env,body) then
        let f = lam t.
          join ["case ", int2string t.0, ":", pprintNewline iv, t.1] in
        let body = strJoin (pprintNewline iii) (map f body) in
        let str = join ["switch (", cond, ")", pprintNewline ii,
                        "{", body] in
        match default with Some default then
          match printStmt iv default with (env,default) then
            (env join [str, pprintNewline iii,
                       "default:", pprintNewline iv,
                       default, pprintNewline ii,
                       "}"])
          else never
        else (env, join [str, pprintNewline ii, "}"])
      else never
    else never

  | SWhile { cond = cond, body = body } ->
    let i = indent in
    let ii = pprintIncr i in
    match printExpr env cond with (env,cond) then
      match printStmt ii env body with (env,body) then
        (env, join ["while (", cond, ")", pprintNewline ii, body])
      else never
    else never

  | SExpr { expr = expr } ->
    match printExpr env expr with (env,expr) then
      (env, join [expr, ";"])
    else never

  | SComp { stmts = stmts } ->
    let i = indent in
    let ii = pprintIncr i in
    match mapAccumL printStmt ii env stmts with (env,stmts) then
      let stmts = strJoin (pprintNewline ii) stmts in
      (env, join ["{", pprintNewline ii, stmts, pprintNewline i, "}"]
    else never

  | SRet { val = val } ->
    match val with Some val then
      match printExpr env val with (env,val) then
        (env, join ["return", expr, ";"])
      else never
    else (env, "return;")

  | SCont { } -> (env, "cont;")
  | SBreak { } -> (env, "break;")


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem printTop (indent : Int) (env: PprintEnv) =
  | TDef      { def = def } ->
  | TPtrTy    { ty = ty, id = id} ->
  | TFunTy    { ret = ret, id = id, params = params} ->
  | TArrTy    { ty = ty, size = size} ->
  | TStructTy { id = id, mem = mem} ->
  | TUnionTy  { id = id, mem = mem} ->
  | TEnumTy   { id = id, mem = mem} ->
  | TFun      { ty = ty, id = id, params = params, body = body} ->

  sem printProg =
  | CProg { tops = tops} ->

end
