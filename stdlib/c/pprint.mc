include "ast.mc"

include "mexpr/pprint.mc"

-------------
-- HELPERS --
-------------

let _par = lam str. join ["(",str,")"]

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

  | EVar { id = id } -> printId env id

  | EApp { fun = fun, args = args} ->
    match printId env fun with (env,fun) then
      match mapAccumL printExpr env args with (env,args) then
        (env, _par (join [fun, "(", (strJoin ", " args)], ")"))
      else never
    else never

  | EInt    { i = i } -> (env, int2string i)
  | EFloat  { f = f } -> (env, float2string f)
  | EChar   { c = c } -> (env, ['\'', c, '\''])

  -- TODO(dlunde,2020-10-29): Escape characters
  | EString { s = s } -> (env, join ["\"", s, "\""])

  | EUnOp { op = op, arg = arg } ->
    match printExpr env arg with (env,arg) then
      (env, _par (printUnOp arg op))
    else never

  | EBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match printExpr env lhs with (env,lhs) then
      match printExpr env rhs with (env,rhs) then
        (env, _par (printBinOp lhs rhs op))
      else never
    else never

  | EMemb { lhs = lhs, id = id } ->
    match printExpr env lhs with (env,lhs) then
      match printId env id with (env,id) then
        (env, _par (join [lhs, ".", id]))
      else never
    else never

  | ECast { ty = ty, rhs = rhs } ->
    match printType env ty with (env,ty) then
      match printExpr env rhs with (env,rhs) then
        (env, _par (join ["(",ty,") ", rhs]))
      else never
    else never

  | ESizeOfType { ty = ty } ->
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
  | OXor    {} -> join [lhs, " ^ ", rhs]

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
  -- C INITIALIERS --
  -------------------

  -- Helper function for printing declarations and definitions
  sem printDef (env: PprintEnv) (ty: Type) (id: Name) =
  | init ->
    match printType env ty with (env,ty) then
      match printId env id with (env,id) then
        let decl = join [ty, " ", id] in
        match init with Some init then
          match printInit env init with (env,init) then
            (env, join [decl, " = ", init])
          else never
        else (env, decl)
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

  -- Print a line-separated list of statements at the given indentation level.
  sem printStmts (indent: Int) (env: PprintEnv) =
  | stmts ->
    match mapAccumL (printStmt indent) env stmts with (env,stmts) then
      (env, strJoin (pprintNewline indent) stmts)
    else never

  sem printStmt (indent: Int) (env: PprintEnv) =
  | SDef { ty = ty, id = id, init = init } ->
    match printDef env ty id init with (env,str) then
      (env, join [str, ";"])
    else never

  | SIf { cond = cond, thn = thn, els = els } ->
    let i = indent in
    let ii = pprintIncr i in
    match printExpr env cond with (env,cond) then
      match printStmts ii env thn with (env,thn) then
        match printStmts ii env els with (env,els) then
          (env, join ["if (", cond, ") {", pprintNewline ii,
                      thn, pprintNewline i,
                      "} else {", pprintNewline ii,
                      els, pprintNewline i,
                      "}"])
        else never
      else never
    else never

  | SSwitch { cond = cond, body = body, default = default } ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    match printExpr env cond with (env,cond) then
      let f = lam env. lam t.
        match printStmts iii env t.1 with (env,t1) then (t.0,t1) else never in
      match mapAccumL f env body with (env,body) then
        let f = lam t.
          join ["case ", int2string t.0, ":", pprintNewline iii, t.1] in
        let body = strJoin (pprintNewline ii) (map f body) in
        let str = join ["switch (", cond, ") {", pprintNewline ii, body] in
        match default with Some default then
          match printStmts iii default with (env,default) then
            (env join [str, pprintNewline ii,
                       "default:", pprintNewline iii,
                       default, pprintNewline i,
                       "}"])
          else never
        else (env, join [str, pprintNewline ii, "}"])
      else never
    else never

  | SWhile { cond = cond, body = body } ->
    let i = indent in
    let ii = pprintIncr i in
    match printExpr env cond with (env,cond) then
      match printStmts ii env body with (env,body) then
        (env, join ["while (", cond, ") {", pprintNewline ii,
                    body, pprintNewline i,
                    "}"])
      else never
    else never

  | SExpr { expr = expr } ->
    match printExpr env expr with (env,expr) then
      (env, join [expr, ";"])
    else never

  | SComp { stmts = stmts } ->
    let i = indent in
    let ii = pprintIncr i in
    match printStmts ii env stmts with (env,stmts) then
      (env, join ["{", pprintNewline ii, stmts, pprintNewline i, "}"])
    else never

  | SRet { val = val } ->
    match val with Some val then
      match printExpr env val with (env,val) then
        (env, join ["return", val, ";"])
      else never
    else (env, "return;")

  | SCont { } -> (env, "cont;")
  | SBreak { } -> (env, "break;")


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem printTop (indent : Int) (env: PprintEnv) =
  | TDef { ty = ty, id = id, init = init } ->
    match printDef env ty id init with (env,str) then
      (env, join [str, ";"])
    else never

  | TFun { ret = ret, id = id, params = params, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match printType env ret with (env,ret) then
      match printId env id with (env,id) then
        let f = lam env. lam t. printDef env t.0 t.1 (None ()) in
        match mapAccumL f env params with (env,params) then
          let params = strJoin ", " params in
          match printStmts ii env body with (env,body) then
            (env, join [ret, " ", id, "(", params, ") {", pprintNewline ii,
                        body, pprintNewline i,
                        "}"])
          else never
        else never
      else never
    else never

  | TPtrTy { ty = ty, id = id } ->
    match printType env ty with (env,ty) then
      match printId env id with (env,id) then
        (env, join ["typedef ", ty, " *", id, ";"])
      else never
    else never

  | TFunTy { ret = ret, id = id, params = params } ->
    match printType env ret with (env,ret) then
      match printId env id with (env,id) then
        match mapAccumL printType env params with (env,params) then
          let params = strJoin ", " params in
          (env, join ["typedef ", ret, " ", id, "(", params, ");"])
        else never
      else never
    else never

  | TArrTy { ty = ty, id = id, size = size } ->
    match printType env ty with (env,ty) then
      let subscr = match size with Some size then int2string size else "" in
      (env, join ["typedef ", ty, " ", id, "[", subscr, "];"])
    else never

  | TStructTy { id = id, mem = mem } ->
    let i = indent in
    let ii = pprintIncr i in
    match printId env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printDef env t.0 t.1 (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = strJoin (pprintNewline ii) mem in
          (env, join ["typedef struct ", id, " {", pprintNewline ii,
                      mem, pprintNewline i,
                      "};"])
        else never
      else (env, join ["typedef struct ", id, " ", id, ";"])
    else never

  | TUnionTy { id = id, mem = mem } ->
    let i = indent in
    let ii = pprintIncr i in
    match printId env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printDef env t.0 t.1 (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = strJoin (pprintNewline ii) mem in
          (env, join ["typedef union ", id, " {", pprintNewline ii,
                      mem, pprintNewline i,
                      "};"])
        else never
      else (env, join ["typedef union ", id, " ", id, ";"])
    else never

  | TEnumTy { id = id, mem = mem } ->
    let i = indent in
    let ii = pprintIncr i in
    match printId env id with (env,id) then
      match mem with Some mem then
        match mapAccumL printId env mem with (env,mem) then
          let mem = strJoin (pprintNewline ii) mem in
          (env, join ["typedef enum ", id, " {", pprintNewline ii,
                      mem, pprintNewline i,
                      "};"])
        else never
      else (env, join ["typedef enum ", id, " ", id, ";"])
    else never

  sem printProg =
  | PProg { tops = tops } ->
    -- If main is found, we must make sure it is printed as "main"
    recursive let findMain = lam tops.
      match tops with [h] ++ tl then
        match h with TDef { id = id } | TFun { id = id } then
          if eqString (nameGetStr id) "main" then Some id
          else findMain tl
        else findMain tl
      else match tops with [] then None ()
      else never
    in
    let indent = 0 in
    let env =
      match findMain tops with Some name then
        pprintAddStr pprintEnvEmpty name
      else pprintEnvEmpty
    in
    match mapAccumL (printTop indent) env tops with (env,tops) then
      strJoin (pprintNewline indent) tops
    else never

end

mexpr
use CPrettyPrint in

let def = TDef { ty = TyInt {}, id = nameSym "x", init = None () } in

let definit = TDef {
  ty = TyChar {}, id = nameSym "y",
  init = Some (IExpr { expr = EChar { c = 'c'}})
}
in

let main = TFun {
  ret = TyInt {}, id = nameSym "main",
  params = [], body = [SRet { val = None () }] }
in

let tops = [
  def,
  definit,
  main
] in

let prog = PProg { tops = tops } in

let _ = printLn (printProg prog) in

()
