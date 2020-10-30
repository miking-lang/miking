-- Pretty printer for C.

include "ast.mc"

include "mexpr/pprint.mc"

-------------
-- HELPERS --
-------------

-- Surrounds a string with parentheses
let _par = lam str. join ["(",str,")"]

-- Combines two strings with space in between (if the second string is non-empty)
let _joinSpace = lam fst. lam snd.
  if eqString "" snd then fst else join [fst, " ", snd]

lang CPrettyPrint = CAst + PrettyPrint

  -------------------
  -- C EXPRESSIONS --
  -------------------

  sem printExpr (env: PprintEnv) =

  | EVar { id = id } -> pprintEnvGetStr env id

  | EApp { fun = fun, args = args } ->
    match pprintEnvGetStr env fun with (env,fun) then
      match mapAccumL printExpr env args with (env,args) then
        (env, _par (join [fun, "(", (strJoin ", " args), ")"]))
      else never
    else never

  | EInt   { i = i } -> (env, int2string i)
  | EFloat { f = f } -> (env, float2string f)
  | EChar  { c = c } -> (env, ['\'', c, '\''])

  -- TODO(dlunde,2020-10-29): Escape characters
  | EString { s = s } -> (env, join ["\"", s, "\""])

  | EBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match printExpr env lhs with (env,lhs) then
      match printExpr env rhs with (env,rhs) then
        (env, _par (printBinOp lhs rhs op))
      else never
    else never

  | EUnOp { op = op, arg = arg } ->
    match printExpr env arg with (env,arg) then
      (env, _par (printUnOp arg op))
    else never

  | EMember { lhs = lhs, id = id } ->
    match printExpr env lhs with (env,lhs) then
      match pprintEnvGetStr env id with (env,id) then
        (env, _par (join [lhs, ".", id]))
      else never
    else never

  | ECast { ty = ty, rhs = rhs } ->
    match printType "" env ty with (env,ty) then
      match printExpr env rhs with (env,rhs) then
        (env, _par (join ["( ", ty, " ) ", rhs]))
      else never
    else never

  | ESizeOfType { ty = ty } ->
    match printType "" env ty with (env,ty) then
      (env, _par (join ["sizeof(", ty, ")"]))
    else never

  sem printBinOp (lhs: String) (rhs: String) =
  | OAssign    {} -> join [lhs, " = ", rhs]
  | OSubScript {} -> join [lhs, "[", rhs, "]"]
  | OOr        {} -> join [lhs, " || ", rhs]
  | OAnd       {} -> join [lhs, " && ", rhs]
  | OEq        {} -> join [lhs, " == ", rhs]
  | ONeq       {} -> join [lhs, " != ", rhs]
  | OLt        {} -> join [lhs, " < ", rhs]
  | OGt        {} -> join [lhs, " > ", rhs]
  | OLe        {} -> join [lhs, " <= ", rhs]
  | OGe        {} -> join [lhs, " >= ", rhs]
  | OShiftL    {} -> join [lhs, " << ", rhs]
  | OShiftR    {} -> join [lhs, " >> ", rhs]
  | OAdd       {} -> join [lhs, " + ", rhs]
  | OSub       {} -> join [lhs, " - ", rhs]
  | OMul       {} -> join [lhs, " * ", rhs]
  | ODiv       {} -> join [lhs, " / ", rhs]
  | OMod       {} -> join [lhs, " % ", rhs]
  | OBOr       {} -> join [lhs, " | ", rhs]
  | OBAnd      {} -> join [lhs, " & ", rhs]
  | OXor       {} -> join [lhs, " ^ ", rhs]

  sem printUnOp (arg: String) =
  | OSizeOf {} -> join ["sizeof(", arg, ")"]
  | ODeref  {} -> join ["*", arg]
  | OAddrOf {} -> join ["&", arg]
  | ONeg    {} -> join ["-", arg]
  | ONot    {} -> join ["~", arg]


  -------------
  -- C TYPES --
  -------------

  -- Helper function for printing declarations and definitions
  sem printDef (env: PprintEnv) (ty: Type) (id: Option Name) =
  | init ->
    let tmp = match id with Some id then pprintEnvGetStr env id else (env, "") in
    match tmp with (env,id) then
      match printType id env ty with (env,decl) then
        match init with Some init then
          match printInit env init with (env,init) then
            (env, join [decl, " = ", init])
          else never
        else (env, decl)
      else never
    else never

  sem printType (decl: String) (env: PprintEnv) =

  -- TyIdent not really needed unless we add typedef
  --| TyIdent  { id = id } -> pprintEnvGetStr env id

  | TyChar {} -> (env, _joinSpace "char" decl)
  | TyInt {}  -> (env, _joinSpace "int" decl)
  | TyDouble {} -> (env, _joinSpace "double" decl)
  | TyVoid {} -> (env, _joinSpace "void" decl)
  | TyPtr { ty = ty } -> printType (join ["(*", decl, ")"]) env ty

  | TyFun { ret = ret, params = params } ->
    match mapAccumL (printType "") env params with (env,params) then
      let params = join ["(", strJoin ", " params, ")"] in
      printType (join [decl, params]) env ret
    else never

  | TyArray { ty = ty, size = size } ->
    let subscr = match size with Some size then int2string size else "" in
    printType (join [decl, "[", subscr, "]"]) env ty

  | TyStruct { id = id, mem = mem } ->
    match pprintEnvGetStr env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printDef env t.0 (Some t.1) (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join ["struct ", id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (join ["struct ", id]) decl)
    else never

  | TyUnion { id = id, mem = mem } ->
    match pprintEnvGetStr env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printDef env t.0 (Some t.1) (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join ["union ", id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (join ["union ", id]) decl)
    else never

  | TyEnum { id = id, mem = mem } ->
    match pprintEnvGetStr env id with (env,id) then
      match mem with Some mem then
        match mapAccumL pprintEnvGetStr env mem with (env,mem) then
          let mem = strJoin ", " mem in
          (env, _joinSpace (join ["enum ", id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (join ["enum ", id]) decl)
    else never


  --------------------
  -- C INITIALIZERS --
  --------------------

  sem printInit (env: PprintEnv) =
  | IExpr { expr = expr } -> printExpr env expr

  | IList { inits = inits } ->
    match mapAccumL printInit env inits with (env,inits) then
      (env, join ["{", strJoin ", " inits, "}"])
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
        match printStmts iii env t.1 with (env,t1) then
          (env,(t.0,t1))
        else never in
      match mapAccumL f env body with (env,body) then
        let f = lam t.
          join ["case ", int2string t.0, ":", pprintNewline iii, t.1] in
        let body = strJoin (pprintNewline ii) (map f body) in
        let str = join ["switch (", cond, ") {", pprintNewline ii, body] in
        match default with Some default then
          match printStmts iii env default with (env,default) then
            (env, join [str, pprintNewline ii,
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
        (env, join ["return ", val, ";"])
      else never
    else (env, "return;")

  | SCont { } -> (env, "continue;")
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
    match pprintEnvGetStr env id with (env,id) then
      let f = lam env. lam t. printDef env t.0 (Some t.1) (None ()) in
      match mapAccumL f env params with (env,params) then
        let params = join ["(", strJoin ", " params, ")"] in
        match printType (join [id, params]) env ret with (env,ty) then
          match printStmts ii env body with (env,body) then
            (env, join [ty, " {", pprintNewline ii, body, pprintNewline i, "}"])
          else never
        else never
      else never
    else never

  sem printProg =
  | PProg { tops = tops } ->
    recursive let findMain = lam tops.
      match tops with [h] ++ tl then
        match h with TDef { id = Some id } | TFun { id = id } then
          if eqString (nameGetStr id) "main" then Some id
          else findMain tl
        else findMain tl
      else match tops with [] then None ()
      else never
    in
    let indent = 0 in
    -- If a main function exists, we must make sure it is printed as "main". We
    -- do this by adding that name first to the environment.
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

-- TODO(dlunde,2020-10-30): We should add proper utests here. For now, we just
-- print a C program containing all the features above.

let xname = nameSym "x" in
let funname = nameSym "fun" in

let var = SExpr { expr = EVar { id = xname } } in
let app = SExpr {
  expr = EApp { fun = funname, args = [EInt { i = 1 }, EChar { c = 'a' }] }
} in

let deftop = TDef { ty = TyInt {}, id = Some xname, init = None () } in
let definittop = TDef {
  ty = TyChar {}, id = Some (nameSym "y"),
  init = Some (IExpr { expr = EChar { c = 'c'}})
} in

let structtyname = nameSym "structty" in
let structmemname = nameSym "x" in

let structtop = TDef {
  ty = TyStruct {
    id = structtyname,
    mem = Some (
      [(TyInt {}, structmemname),
       (TyDouble {}, nameSym "y")]
    )
  },
  id = None (),
  init = None ()
} in

let defstmt = SDef {
  ty = TyDouble {}, id = Some (nameSym "x"),
  init = Some (IExpr { expr = EFloat { f = 0.1 }} )
} in

let ifstmt = SIf {
  cond = EInt { i = 2 },
  thn = [
    var,
    app
  ],
  els = [
  ]
} in

let strinit = SDef {
  ty = TyArray { ty = TyChar {}, size = None () }, id = Some (nameSym "strinit"),
  init = Some (IExpr { expr = EString { s = "strinit" } })
} in

let op = SExpr {
  expr = EBinOp {
    op = OAssign {},
    lhs = EVar { id = xname },
    rhs = EBinOp {
      op = OMul {},
      lhs = EUnOp { op = ONeg {}, arg = EInt { i = 1 } },
      rhs = EInt { i = 3 }
    }
  }
} in

let structname = nameSym "s" in

let struct = SDef {
  ty = TyStruct { id = structtyname, mem = None () },
  id = Some structname,
  init = None ()
} in

let memb = SExpr {
  expr = EMember { lhs = EVar { id = structname }, id = structmemname }
} in

let advty =
TyPtr {
  ty = TyFun {
    ret = TyPtr {
      ty = TyFun {
        ret = TyPtr {
          ty = TyStruct { id = structtyname, mem = None ()}
        },
        params = [TyFun { ret = TyInt {}, params = [TyDouble {}] }]
      }
    },
    params = [TyChar {}]
  }
} in

let cast = SExpr {
  expr = ECast { ty = advty, rhs = EInt { i = 1 } }
} in

let sizety = SExpr {
  expr = ESizeOfType { ty = advty }
} in

let union = SDef {
  ty = TyUnion {
    id = nameSym "unionty",
    mem = Some (
      [(TyInt {}, nameSym "x"),
       (TyDouble {}, nameSym "y")]
    )
  },
  id = None (),
  init = None ()
} in

let enum = SDef {
  ty = TyEnum {
    id = nameSym "enumty",
    mem = Some (
      [(nameSym "CONST"),
       (nameSym "CONST")]
    )
  },
  id = None (),
  init = None ()
} in


let switch = SSwitch {
  cond = EInt { i = 1 },
  body = [
    (2,[
      op,
      SBreak {}
    ]),
    (5,[
      var
    ]),
    (7,[
      app,
      SBreak {}
    ])
  ],
  default = Some ([
    memb
  ])
} in

let while = SWhile {
  cond = EInt { i = 42 },
  body = [
    app,
    SComp { stmts = [
      var,
      memb
    ] },
    SCont {},
    memb
  ]
} in

let funbody = [
  defstmt,
  strinit,
  struct,
  union,
  enum,
  memb,
  cast,
  sizety,
  op,
  app,
  ifstmt,
  switch,
  while
] in

let mainname = nameSym "main" in
let arg2name = nameSym "arg2" in

let arrinit = TDef {
  ty = TyArray {
    ty = TyArray { ty = TyInt {}, size = Some 3 }, size = None ()
  },
  id = Some (nameSym "arrinit"),
  init = Some ( IList {
    inits = [
      IList {
        inits = [
          IExpr { expr = EInt { i = 1 } },
          IExpr { expr = EInt { i = 2 } },
          IExpr { expr = EInt { i = 3 } }
        ]
      },
      IList {
        inits = [
          IExpr { expr = EInt { i = 4 } },
          IExpr { expr = EInt { i = 5 } },
          IExpr { expr = EInt { i = 6 } }
        ]
      }
    ]
  } )
} in

let fun = TFun {
  ret =
    TyPtr { ty = TyFun { ret = TyChar {}, params = [TyInt {}, TyDouble {}] } },
  id = funname,
  params = [(TyInt {}, nameSym "main"), (TyChar {}, arg2name)],
  body = funbody
} in

let main = TFun {
  ret = TyInt {}, id = nameSym "main",
  params = [
    (TyInt {}, nameSym "argc"),
    (TyArray { ty = TyPtr { ty = TyChar {}}, size = None ()}, nameSym "argv")
  ],
  body = [ SRet { val = Some (EInt { i = 1 }) }] }
in

let noreturn = TFun {
  ret = TyVoid {}, id = nameSym "noreturn",
  params = [],
  body = [ SRet { val = None () }] } in

let tops = [
  deftop,
  definittop,
  structtop,
  arrinit,
  fun,
  noreturn,
  main
] in

let prog = PProg { tops = tops } in

-- let _ = printLn (printProg prog) in

-- Test making sure printProg does not crash
utest geqi (length (printProg prog)) 0 with true in

()
