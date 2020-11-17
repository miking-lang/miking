-- Pretty printer for C.

include "ast.mc"

include "mexpr/pprint.mc"

-------------
-- HELPERS --
-------------

-- Surrounds a string with parentheses
let _par = lam str. join ["(",str,")"]

-- Combines two strings with space in between (if the second string is
-- non-empty)
let _joinSpace = lam fst. lam snd.
  if eqString "" snd then fst else join [fst, " ", snd]

-- Similar to pprintEnvGetStr in mexpr/pprint.mc, but takes an Option Name as
-- argument. If it is None (), the returned string is "".
let pprintEnvGetOptStr = lam env. lam id.
  match id with Some id then pprintEnvGetStr env id else (env,"")

lang CPrettyPrint = CAst

  -------------------
  -- C EXPRESSIONS --
  -------------------

  sem printCExpr (env: PprintEnv) =

  | CEVar { id = id } -> pprintEnvGetStr env id

  | CEApp { fun = fun, args = args } ->
    match pprintEnvGetStr env fun with (env,fun) then
      match mapAccumL printCExpr env args with (env,args) then
        (env, _par (join [fun, "(", (strJoin ", " args), ")"]))
      else never
    else never

  | CEInt   { i = i } -> (env, int2string i)
  | CEFloat { f = f } -> (env, float2string f)
  | CEChar  { c = c } -> (env, ['\'', c, '\''])

  | CEString { s = s } -> (env, join ["\"", escapeString s, "\""])

  | CEBinOp { op = op, lhs = lhs, rhs = rhs } ->
    match printCExpr env lhs with (env,lhs) then
      match printCExpr env rhs with (env,rhs) then
        (env, _par (printCBinOp lhs rhs op))
      else never
    else never

  | CEUnOp { op = op, arg = arg } ->
    match printCExpr env arg with (env,arg) then
      (env, _par (printCUnOp arg op))
    else never

  | CEMember { lhs = lhs, id = id } ->
    match printCExpr env lhs with (env,lhs) then
      (env, _par (join [lhs, ".", id]))
    else never

  | CECast { ty = ty, rhs = rhs } ->
    match printCType "" env ty with (env,ty) then
      match printCExpr env rhs with (env,rhs) then
        (env, _par (join ["( ", ty, " ) ", rhs]))
      else never
    else never

  | CESizeOfType { ty = ty } ->
    match printCType "" env ty with (env,ty) then
      (env, _par (join ["sizeof(", ty, ")"]))
    else never

  sem printCBinOp (lhs: String) (rhs: String) =
  | COAssign    {} -> join [lhs, " = ", rhs]
  | COSubScript {} -> join [lhs, "[", rhs, "]"]
  | COOr        {} -> join [lhs, " || ", rhs]
  | COAnd       {} -> join [lhs, " && ", rhs]
  | COEq        {} -> join [lhs, " == ", rhs]
  | CONeq       {} -> join [lhs, " != ", rhs]
  | COLt        {} -> join [lhs, " < ", rhs]
  | COGt        {} -> join [lhs, " > ", rhs]
  | COLe        {} -> join [lhs, " <= ", rhs]
  | COGe        {} -> join [lhs, " >= ", rhs]
  | COShiftL    {} -> join [lhs, " << ", rhs]
  | COShiftR    {} -> join [lhs, " >> ", rhs]
  | COAdd       {} -> join [lhs, " + ", rhs]
  | COSub       {} -> join [lhs, " - ", rhs]
  | COMul       {} -> join [lhs, " * ", rhs]
  | CODiv       {} -> join [lhs, " / ", rhs]
  | COMod       {} -> join [lhs, " % ", rhs]
  | COBOr       {} -> join [lhs, " | ", rhs]
  | COBAnd      {} -> join [lhs, " & ", rhs]
  | COXor       {} -> join [lhs, " ^ ", rhs]

  sem printCUnOp (arg: String) =
  | COSizeOf {} -> join ["sizeof(", arg, ")"]
  | CODeref  {} -> join ["*", arg]
  | COAddrOf {} -> join ["&", arg]
  | CONeg    {} -> join ["-", arg]
  | CONot    {} -> join ["~", arg]


  -------------
  -- C TYPES --
  -------------

  -- Helper function for printing declarations and definitions
  sem printCDef (env: PprintEnv) (ty: CType) (id: String) =
  | init ->
    match printCType id env ty with (env,decl) then
      match init with Some init then
        match printCInit env init with (env,init) then
          (env, join [decl, " = ", init])
        else never
      else (env, decl)
    else never

  sem printCType (decl: String) (env: PprintEnv) =

  -- CTyIdent not really needed unless we add typedef
  --| CTyIdent  { id = id } -> pprintEnvGetStr env id

  | CTyChar {} -> (env, _joinSpace "char" decl)
  | CTyInt {}  -> (env, _joinSpace "int" decl)
  | CTyDouble {} -> (env, _joinSpace "double" decl)
  | CTyVoid {} -> (env, _joinSpace "void" decl)
  | CTyPtr { ty = ty } -> printCType (join ["(*", decl, ")"]) env ty

  | CTyFun { ret = ret, params = params } ->
    match mapAccumL (printCType "") env params with (env,params) then
      let params = join ["(", strJoin ", " params, ")"] in
      printCType (join [decl, params]) env ret
    else never

  | CTyArray { ty = ty, size = size } ->
    let subscr = match size with Some size then int2string size else "" in
    printCType (join [decl, "[", subscr, "]"]) env ty

  | CTyStruct { id = id, mem = mem } ->
    match pprintEnvGetStr env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printCDef env t.0 t.1 (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join ["struct ", id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (join ["struct ", id]) decl)
    else never

  | CTyUnion { id = id, mem = mem } ->
    match pprintEnvGetStr env id with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t. printCDef env t.0 t.1 (None ()) in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join ["union ", id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (join ["union ", id]) decl)
    else never

  | CTyEnum { id = id, mem = mem } ->
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

  sem printCInit (env: PprintEnv) =
  | CIExpr { expr = expr } -> printCExpr env expr

  | CIList { inits = inits } ->
    match mapAccumL printCInit env inits with (env,inits) then
      (env, join ["{", strJoin ", " inits, "}"])
    else never


  ------------------
  -- C STATEMENTS --
  ------------------

  -- Print a line-separated list of statements at the given indentation level.
  sem printCStmts (indent: Int) (env: PprintEnv) =
  | stmts ->
    match mapAccumL (printCStmt indent) env stmts with (env,stmts) then
      (env, strJoin (pprintNewline indent) stmts)
    else never

  sem printCStmt (indent: Int) (env: PprintEnv) =

  | CSDef { ty = ty, id = id, init = init } ->
    match pprintEnvGetOptStr env id with (env,id) then
      match printCDef env ty id init with (env,str) then
        (env, join [str, ";"])
      else never
    else never

  | CSIf { cond = cond, thn = thn, els = els } ->
    let i = indent in
    let ii = pprintIncr i in
    match printCExpr env cond with (env,cond) then
      match printCStmts ii env thn with (env,thn) then
        match printCStmts ii env els with (env,els) then
          (env, join ["if (", cond, ") {", pprintNewline ii,
                      thn, pprintNewline i,
                      "} else {", pprintNewline ii,
                      els, pprintNewline i,
                      "}"])
        else never
      else never
    else never

  | CSSwitch { cond = cond, body = body, default = default } ->
    let i = indent in
    let ii = pprintIncr i in
    let iii = pprintIncr ii in
    match printCExpr env cond with (env,cond) then
      let f = lam env. lam t.
        match printCStmts iii env t.1 with (env,t1) then
          (env,(t.0,t1))
        else never in
      match mapAccumL f env body with (env,body) then
        let f = lam t.
          join ["case ", int2string t.0, ":", pprintNewline iii, t.1] in
        let body = strJoin (pprintNewline ii) (map f body) in
        let str = join ["switch (", cond, ") {", pprintNewline ii, body] in
        match default with Some default then
          match printCStmts iii env default with (env,default) then
            (env, join [str, pprintNewline ii,
                       "default:", pprintNewline iii,
                       default, pprintNewline i,
                       "}"])
          else never
        else (env, join [str, pprintNewline ii, "}"])
      else never
    else never

  | CSWhile { cond = cond, body = body } ->
    let i = indent in
    let ii = pprintIncr i in
    match printCExpr env cond with (env,cond) then
      match printCStmts ii env body with (env,body) then
        (env, join ["while (", cond, ") {", pprintNewline ii,
                    body, pprintNewline i,
                    "}"])
      else never
    else never

  | CSExpr { expr = expr } ->
    match printCExpr env expr with (env,expr) then
      (env, join [expr, ";"])
    else never

  | CSComp { stmts = stmts } ->
    let i = indent in
    let ii = pprintIncr i in
    match printCStmts ii env stmts with (env,stmts) then
      (env, join ["{", pprintNewline ii, stmts, pprintNewline i, "}"])
    else never

  | CSRet { val = val } ->
    match val with Some val then
      match printCExpr env val with (env,val) then
        (env, join ["return ", val, ";"])
      else never
    else (env, "return;")

  | CSCont { } -> (env, "continue;")
  | CSBreak { } -> (env, "break;")


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem printCTop (indent : Int) (env: PprintEnv) =
  | CTDef { ty = ty, id = id, init = init } ->
    match pprintEnvGetOptStr env id with (env,id) then
      match printCDef env ty id init with (env,str) then
        (env, join [str, ";"])
      else never
    else never

  | CTFun { ret = ret, id = id, params = params, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match pprintEnvGetStr env id with (env,id) then
      let f = lam env. lam t.
        match pprintEnvGetStr env t.1 with (env,t1) then
          printCDef env t.0 t1 (None ())
        else never in
      match mapAccumL f env params with (env,params) then
        let params = join ["(", strJoin ", " params, ")"] in
        match printCType (join [id, params]) env ret with (env,ty) then
          match printCStmts ii env body with (env,body) then
            (env, join [ty, " {", pprintNewline ii, body, pprintNewline i, "}"])
          else never
        else never
      else never
    else never

  sem printCProg (nameInit: [Name]) =
  | CPProg { includes = includes, tops = tops } ->
    -- TODO(dlunde,2020-11-13): The following functionality was here
    -- previously, but is probably more suitable in a future C parser or
    -- similar.
    -- If a main function exists, we must make sure it is printed as "main". We
    -- do this by adding that name first to the environment.
    --     recursive let findMain = lam tops.
    --       match tops with [h] ++ tl then
    --         match h with CTDef { id = Some id } | CTFun { id = id } then
    --           if eqString (nameGetStr id) "main" then Some id
    --           else findMain tl
    --         else findMain tl
    --       else match tops with [] then None ()
    --       else never
    --     in
    let indent = 0 in
    let includes = map (lam inc. join ["#include ", inc]) includes in
    let addName = lam env. lam name.
      match pprintAddStr env name with Some env then env
      else error (join ["Duplicate name in printCProg: ", nameGetStr name])
    in
    let env = foldl addName pprintEnvEmpty nameInit in
    match mapAccumL (printCTop indent) env tops with (env,tops) then
      strJoin (pprintNewline indent) (join [includes, tops])
    else never

end

mexpr
use CPrettyPrint in

-- TODO(dlunde,2020-10-30): We should add proper utests here. For now, we just
-- print a C program containing all the features above.

let xname = nameSym "x" in
let funname = nameSym "fun" in

let var = CSExpr { expr = CEVar { id = xname } } in
let app = CSExpr {
  expr = CEApp { fun = funname, args = [CEInt { i = 1 }, CEChar { c = 'a' }] }
} in

let deftop = CTDef { ty = CTyInt {}, id = Some xname, init = None () } in
let definittop = CTDef {
  ty = CTyChar {}, id = Some (nameSym "y"),
  init = Some (CIExpr { expr = CEChar { c = 'c'}})
} in

let structtyname = nameSym "structty" in

let structtop = CTDef {
  ty = CTyStruct {
    id = structtyname,
    mem = Some (
      [(CTyInt {}, "x"),
       (CTyDouble {}, "y")]
    )
  },
  id = None (),
  init = None ()
} in

let defstmt = CSDef {
  ty = CTyDouble {}, id = Some (nameSym "x"),
  init = Some (CIExpr { expr = CEFloat { f = 0.1 }} )
} in

let ifstmt = CSIf {
  cond = CEInt { i = 2 },
  thn = [
    var,
    app
  ],
  els = [
  ]
} in

let strinit = CSDef {
  ty = CTyArray { ty = CTyChar {}, size = None () }, id = Some (nameSym "strinit"),
  init = Some (CIExpr { expr = CEString { s = "strinit" } })
} in

let op = CSExpr {
  expr = CEBinOp {
    op = COAssign {},
    lhs = CEVar { id = xname },
    rhs = CEBinOp {
      op = COMul {},
      lhs = CEUnOp { op = CONeg {}, arg = CEInt { i = 1 } },
      rhs = CEInt { i = 3 }
    }
  }
} in

let structname = nameSym "s" in

let struct = CSDef {
  ty = CTyStruct { id = structtyname, mem = None () },
  id = Some structname,
  init = None ()
} in

let memb = CSExpr {
  expr = CEMember { lhs = CEVar { id = structname }, id = "x" }
} in

let advty =
CTyPtr {
  ty = CTyFun {
    ret = CTyPtr {
      ty = CTyFun {
        ret = CTyPtr {
          ty = CTyStruct { id = structtyname, mem = None ()}
        },
        params = [CTyFun { ret = CTyInt {}, params = [CTyDouble {}] }]
      }
    },
    params = [CTyChar {}]
  }
} in

let cast = CSExpr {
  expr = CECast { ty = advty, rhs = CEInt { i = 1 } }
} in

let sizety = CSExpr {
  expr = CESizeOfType { ty = advty }
} in

let union = CSDef {
  ty = CTyUnion {
    id = nameSym "unionty",
    mem = Some (
      [(CTyInt {}, "x"),
       (CTyDouble {}, "y")]
    )
  },
  id = None (),
  init = None ()
} in

let enum = CSDef {
  ty = CTyEnum {
    id = nameSym "enumty",
    mem = Some (
      [(nameSym "CONST"),
       (nameSym "CONST")]
    )
  },
  id = None (),
  init = None ()
} in


let switch = CSSwitch {
  cond = CEInt { i = 1 },
  body = [
    (2,[
      op,
      CSBreak {}
    ]),
    (5,[
      var
    ]),
    (7,[
      app,
      CSBreak {}
    ])
  ],
  default = Some ([
    memb
  ])
} in

let while = CSWhile {
  cond = CEInt { i = 42 },
  body = [
    app,
    CSComp { stmts = [
      var,
      memb
    ] },
    CSCont {},
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

let arrinit = CTDef {
  ty = CTyArray {
    ty = CTyArray { ty = CTyInt {}, size = Some 3 }, size = None ()
  },
  id = Some (nameSym "arrinit"),
  init = Some ( CIList {
    inits = [
      CIList {
        inits = [
          CIExpr { expr = CEInt { i = 1 } },
          CIExpr { expr = CEInt { i = 2 } },
          CIExpr { expr = CEInt { i = 3 } }
        ]
      },
      CIList {
        inits = [
          CIExpr { expr = CEInt { i = 4 } },
          CIExpr { expr = CEInt { i = 5 } },
          CIExpr { expr = CEInt { i = 6 } }
        ]
      }
    ]
  } )
} in

let fun = CTFun {
  ret =
    CTyPtr { ty = CTyFun { ret = CTyChar {}, params = [CTyInt {}, CTyDouble {}] } },
  id = funname,
  params = [(CTyInt {}, nameSym "main"), (CTyChar {}, arg2name)],
  body = funbody
} in

let main = CTFun {
  ret = CTyInt {}, id = mainname,
  params = [
    (CTyInt {}, nameSym "argc"),
    (CTyArray { ty = CTyPtr { ty = CTyChar {}}, size = None ()}, nameSym "argv")
  ],
  body = [ CSRet { val = Some (CEInt { i = 1 }) }] }
in

let noreturn = CTFun {
  ret = CTyVoid {}, id = nameSym "noreturn",
  params = [],
  body = [ CSRet { val = None () }] } in

let tops = [
  deftop,
  definittop,
  structtop,
  arrinit,
  fun,
  noreturn,
  main
] in

let prog = CPProg { includes = ["<stdio.h>"], tops = tops } in

-- let _ = printLn (printCProg [mainname] prog) in

-- Test making sure printCProg does not crash
utest geqi (length (printCProg [mainname] prog)) 0 with true in

()
