-- Pretty printing for C fragments.
-- TODO(dlunde,2021-02-25): Add handling for arbitrary variable names.

include "ast.mc"
include "string.mc"
include "char.mc"

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

-- Replace invalid characters with underscore
let replaceInvalidChar = lam c.
  if isAlphaOrUnderscore c then c
  else if isDigit c then c
  else '_'

-- Ensure string is a valid C identifier
let escapeIdentifier = lam str: String.
  match str with [h] ++ t then
    let h =
      if isAlphaOrUnderscore h then [h]
      else if isDigit h then cons '_' [h]
      else "_"
    in
    concat h (map replaceInvalidChar t)
  else "_"

let cPprintEnvGetStr = lam env. lam id: Name.
  use IdentifierPrettyPrint in
  -- Set this to true to print names with their symbols (for debugging)
  if false then
    (env,join [
      nameGetStr id,
      match nameGetSym id with Some sym then int2string (sym2hash sym) else ""
    ])
  else
    let id = nameSetStr id (escapeIdentifier (nameGetStr id)) in
    pprintEnvGetStr env id

-- Similar to cPprintEnvGetStr above, but takes an Option Name as
-- argument. If it is None (), the returned string is "".
let cPprintEnvGetOptStr = lam env. lam id.
  match id with Some id then cPprintEnvGetStr env id else (env,"")

--------------
-- KEYWORDs --
--------------

-- From https://en.cppreference.com/w/c/keyword and
-- https://en.cppreference.com/w/cpp/keyword
let cKeywords = [
  "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex", "_Decimal128",
  "_Decimal32", "_Decimal64", "_Generic", "_Imaginary", "_Noreturn",
  "_Static_assert", "_Thread_local", "alignas", "alignof", "and", "and_eq",
  "asm", "atomic_cancel", "atomic_commit", "atomic_noexcept", "auto", "bitand",
  "bitor", "bool", "break", "case", "catch", "char", "char16_t", "char32_t",
  "char8_t", "class", "co_await", "co_return", "co_yield", "compl", "concept",
  "const", "const_cast", "consteval", "constexpr", "constinit", "continue",
  "decltype", "default", "delete", "do", "double", "dynamic_cast", "else",
  "enum", "explicit", "export", "extern", "false", "float", "for", "friend",
  "goto", "if", "inline", "int", "long", "mutable", "namespace", "new",
  "noexcept", "not", "not_eq", "nullptr", "operator", "or", "or_eq", "private",
  "protected", "public", "reflexpr", "register", "reinterpret_cast", "requires",
  "restrict", "return", "short", "signed", "sizeof", "static", "static_assert",
  "static_cast", "struct", "switch", "synchronized", "template", "this",
  "thread_local", "throw", "true", "try", "typedef", "typeid", "typename",
  "union", "unsigned", "using", "virtual", "void", "volatile", "wchar_t",
  "while", "xor", "xor_eq"
]

-----------------------------
-- C TYPES AND EXPRESSIONS --
-----------------------------
lang CExprTypePrettyPrint = CExprTypeAst

  sem printCType (decl: String) (env: PprintEnv) =

  | CTyVar { id = id } ->
    match cPprintEnvGetStr env id with (env,id) then
      (env, _joinSpace id decl)
    else never

  | CTyChar {} -> (env, _joinSpace "char" decl)
  | CTyInt {}  -> (env, _joinSpace "int" decl)
  | CTyInt32 {} -> (env, _joinSpace "int32_t" decl)
  | CTyInt64 {} -> (env, _joinSpace "int64_t" decl)
  | CTyFloat {} -> (env, _joinSpace "float" decl)
  | CTyDouble {} -> (env, _joinSpace "double" decl)
  | CTyVoid {} -> (env, _joinSpace "void" decl)
  | CTyPtr { ty = ty } -> printCType (join ["(*", decl, ")"]) env ty

  | CTyFun { ret = ret, params = params } ->
    match mapAccumL (printCType "") env params with (env,params) then
      let params = join ["(", strJoin ", " params, ")"] in
      printCType (join [decl, params]) env ret
    else never

  | CTyArray { ty = ty, size = size } ->
    let subscr =
      match size with Some size then printCExpr env size else (env,"") in
    match subscr with (env,subscr) then
      printCType (join [decl, "[", subscr, "]"]) env ty
    else never

  | CTyStruct { id = id, mem = mem } ->
    let idtup =
      match id with Some id then cPprintEnvGetStr env id else (env, "") in
    match idtup with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t: (CType, Option Name).
          match t.1 with Some n then
            match cPprintEnvGetStr env n with (env,n) then
              printCType n env t.0
            else never
          else match t.1 with None _ then
            printCType "" env t.0
          else never
        in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join [_joinSpace "struct" id, " {", mem, "}"]) decl)
        else never
      else match mem with None _ then
        (env, _joinSpace (_joinSpace "struct" id) decl)
      else never
    else never

  | CTyUnion { id = id, mem = mem } ->
    let idtup =
      match id with Some id then cPprintEnvGetStr env id else (env, "") in
    match idtup with (env,id) then
      match mem with Some mem then
        let f = lam env. lam t: (CType, Option Name).
          match t.1 with Some n then
            match cPprintEnvGetStr env n with (env,n) then
              printCType n env t.0
            else never
          else printCType "" env t.0
        in
        match mapAccumL f env mem with (env,mem) then
          let mem = map (lam s. join [s,";"]) mem in
          let mem = strJoin " " mem in
          (env, _joinSpace (join [_joinSpace "union" id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (_joinSpace "union " id) decl)
    else never

  | CTyEnum { id = id, mem = mem } ->
    let idtup =
      match id with Some id then cPprintEnvGetStr env id else (env, "") in
    match idtup with (env,id) then
      match mem with Some mem then
        match mapAccumL cPprintEnvGetStr env mem with (env,mem) then
          let mem = strJoin ", " mem in
          (env, _joinSpace (join [_joinSpace "enum" id, " {", mem, "}"]) decl)
        else never
      else (env, _joinSpace (_joinSpace "enum" id) decl)
    else never


  sem printCExpr (env: PprintEnv) =

  | CEVar { id = id } -> cPprintEnvGetStr env id

  -- NOTE(larshum, 2021-09-03): We might need to add parentheses around
  -- applications in the future, if we add support for scope resolution
  -- (see https://en.cppreference.com/w/cpp/language/operator_precedence).
  | CEApp { fun = fun, args = args } ->
    match cPprintEnvGetStr env fun with (env,fun) then
      match mapAccumL printCExpr env args with (env,args) then
        (env, join [fun, "(", (strJoin ", " args), ")"])
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
    match cPprintEnvGetStr env id with (env,id) then
      match printCExpr env lhs with (env,lhs) then
        (env, _par (join [lhs, ".", escapeIdentifier id]))
      else never
    else never

  | CEArrow { lhs = lhs, id = id } ->
    match cPprintEnvGetStr env id with (env,id) then
      match printCExpr env lhs with (env,lhs) then
        (env, _par (join [lhs, "->", escapeIdentifier id]))
      else never
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

end


--------------------
-- C INITIALIZERS --
--------------------
lang CInitPrettyPrint = CInitAst + CExprTypePrettyPrint

  sem printCInit (env: PprintEnv) =
  | CIExpr { expr = expr } -> printCExpr env expr

  | CIList { inits = inits } ->
    match mapAccumL printCInit env inits with (env,inits) then
      (env, join ["{", strJoin ", " inits, "}"])
    else never

end

-------------------------------------
-- HELPER FRAGMENT FOR DEFINITIONS --
-------------------------------------
lang CDefPrettyPrint = CExprTypePrettyPrint + CInitPrettyPrint

  -- Helper function for printing declarations and definitions
  sem printCDef (env: PprintEnv) (ty: CType) (id: String) =
  | init ->
    match printCType id env ty with (env,decl) then
      match init with Some init then
        match printCInit env init with (env,init) then
          (env, join [decl, " = ", init])
        else never
      else match init with None _ then
        (env, decl)
      else never
    else never

end

------------------
-- C STATEMENTS --
------------------
lang CStmtPrettyPrint =
  CStmtAst + CInitPrettyPrint + CExprTypePrettyPrint + CDefPrettyPrint

  -- Print a line-separated list of statements at the given indentation level.
  sem printCStmts (indent: Int) (env: PprintEnv) =
  | stmts ->
    match mapAccumL (printCStmt indent) env stmts with (env,stmts) then
      (env, strJoin (pprintNewline indent) stmts)
    else never

  sem printCStmt (indent: Int) (env: PprintEnv) =

  | CSDef { ty = ty, id = id, init = init } ->
    match cPprintEnvGetOptStr env id with (env,id) then
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
      let f = lam env. lam t: (Int, [CStmt]).
        match printCStmts iii env t.1 with (env,t1) then
          (env,(t.0,t1))
        else never in
      match mapAccumL f env body with (env,body) then
        let f = lam t: (Int, String).
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

  | CSNop {} -> (env, ";")

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

end


-----------------
-- C TOP-LEVEL --
-----------------
lang CTopPrettyPrint =
  CTopAst + CExprTypePrettyPrint + CInitPrettyPrint + CStmtPrettyPrint
  + CDefPrettyPrint

  sem printCTop (indent : Int) (env: PprintEnv) =
  | CTTyDef { ty = ty, id = id } ->
    match cPprintEnvGetStr env id with (env,id) then
      match printCDef env ty id (None ()) with (env,str) then
        (env, join ["typedef ", str, ";"])
      else never
    else never

  | CTDef { ty = ty, id = id, init = init } ->
    match cPprintEnvGetOptStr env id with (env,id) then
      match printCDef env ty id init with (env,str) then
        (env, join [str, ";"])
      else never
    else never

  | CTFun { ret = ret, id = id, params = params, body = body } ->
    let i = indent in
    let ii = pprintIncr indent in
    match cPprintEnvGetStr env id with (env,id) then
      let f = lam env. lam t: (CType,Name).
        match cPprintEnvGetStr env t.1 with (env,t1) then
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

end


-----------------------
-- COMBINED FRAGMENT --
-----------------------
lang CPrettyPrint =
  CExprTypePrettyPrint + CInitPrettyPrint + CStmtPrettyPrint + CTopPrettyPrint
end

---------------
-- C PROGRAM --
---------------
lang CProgPrettyPrint = CProgAst + CTopPrettyPrint

  sem printCProg (nameInit: [Name]) =
  | CPProg { includes = includes, tops = tops } ->
    let indent = 0 in
    let includes = map (lam inc. join ["#include ", inc]) includes in
    let addName = lam env. lam name.
      match pprintAddStr env name with Some env then env
      else error (join ["Duplicate name in printCProg: ", nameGetStr name])
    in
    let env = foldl addName pprintEnvEmpty (map nameNoSym cKeywords) in
    let env = foldl addName env nameInit in
    match mapAccumL (printCTop indent) env tops with (env,tops) then
      strJoin (pprintNewline indent) (join [includes, tops])
    else never

end

----------------
-- UNIT TESTS --
----------------

lang Test = CPrettyPrint + CProgPrettyPrint
end

mexpr
use Test in

let funname = nameSym "fun" in
let mainname = nameSym "main" in
let xname = nameSym "x" in
let tyname = nameSym "Ty" in

let printTest = printCProg [mainname] in

let strIndent = lam indent. lam str.
  strJoin "\n" (map (lam str. join [make indent ' ', str]) (strSplit "\n" str))
in

let wrapTop = lam top. CPProg { includes = [], tops = [top] } in

let wrapStmt = lam stmt. wrapTop (CTFun {
  ret = CTyVoid {}, id = funname, params = [], body = [stmt]
}) in
let wrapStmtString = lam str. join [
  "void fun() {\n",
   strIndent 2 str, "\n",
  "}"
] in

let deftop = CTDef { ty = CTyInt {}, id = Some xname, init = None () } in
utest printTest (wrapTop deftop) with
  "int x;"
in

let escapedName = CTDef {
  ty = CTyInt {}, id = Some (nameSym "0@a[A"), init = None ()
} in
utest printTest (wrapTop escapedName) with
  "int _0_a_A;"
in

let tydeftop = CTTyDef { ty = CTyInt {}, id = tyname } in
utest printTest (wrapTop tydeftop) with
  "typedef int Ty;"
in

let deftoptyvar =
  CTDef { ty = CTyVar { id = tyname }, id = Some xname, init = None () } in
utest printTest (wrapTop deftoptyvar) with
  "Ty x;"
in

let definittop = CTDef {
  ty = CTyChar {}, id = Some (nameSym "y"),
  init = Some (CIExpr { expr = CEChar { c = 'c'}})
} in
utest printTest (wrapTop definittop) with
  "char y = 'c';"
in

let structtyname = nameSym "structty" in
let structtop = CTDef {
  ty = CTyStruct {
    id = Some structtyname,
    mem = Some [
      (CTyInt {}, Some (nameNoSym "0x")),
      (CTyDouble {}, Some (nameNoSym "y"))
    ]
  },
  id = None (),
  init = None ()
} in
utest printTest (wrapTop structtop) with
  "struct structty {int _0x; double y;};"
in

let nestedstructtop = CTDef {
  ty = CTyStruct {
    id = Some structtyname,
    mem = Some [
      (CTyInt {}, Some (nameNoSym "x")),
      (CTyStruct {
         id = None (), mem = Some [(CTyChar {}, Some (nameNoSym "z"))]
       }, None ()),
      (CTyDouble {}, Some (nameNoSym "y"))
    ]
  },
  id = None (),
  init = None ()
} in
utest printTest (wrapTop nestedstructtop) with
  "struct structty {int x; struct {char z;}; double y;};"
in

let anonenum = CTDef {
  ty = CTyEnum {
    id = None (),
    mem = Some (
      [(nameSym "CONST"),
       (nameSym "CONST")]
    )
  },
  id = None (),
  init = None ()
} in
utest printTest (wrapTop anonenum) with
  "enum {CONST, CONST1};"
in


let arrinit = CTDef {
  ty = CTyArray {
    ty = CTyArray { ty = CTyInt {}, size = Some (CEInt { i = 3 }) },
    size = None ()
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
utest printTest (wrapTop arrinit) with
  "int arrinit[][3] = {{1, 2, 3}, {4, 5, 6}};"
in

let defstmt = CSDef {
  ty = CTyDouble {}, id = Some xname,
  init = Some (CIExpr { expr = CEFloat { f = 0.1 }} )
} in
utest printTest (wrapStmt defstmt) with
  wrapStmtString "double x = 0.1;"
using eqString in

let var = CSExpr { expr = CEVar { id = xname } } in
let app = CSExpr {
  expr = CEApp { fun = funname, args = [CEInt { i = 1 }, CEChar { c = 'a' }] }
} in

let ifstmt = CSIf {
  cond = CEInt { i = 2 },
  thn = [
    var,
    app
  ],
  els = []
} in
utest printTest (wrapStmt ifstmt) with
  wrapStmtString (strJoin "\n" [
    "if (2) {",
    "  x;",
    "  fun(1, 'a');",
    "} else {",
    "  ",
    "}"
  ])
using eqString in

let strinit = CSDef {
  ty = CTyArray { ty = CTyChar {}, size = None () }, id = Some (nameSym "strinit"),
  init = Some (CIExpr { expr = CEString { s = "strinit" } })
} in
utest printTest (wrapStmt strinit) with
  wrapStmtString "char strinit[] = \"strinit\";"
using eqString in

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
utest printTest (wrapStmt op) with
  wrapStmtString "(x = ((-1) * 3));"
using eqString in

let structname = nameSym "s" in
let struct = CSDef {
  ty = CTyStruct { id = Some structtyname, mem = None () },
  id = Some structname,
  init = None ()
} in
utest printTest (wrapStmt struct) with
  wrapStmtString "struct structty s;"
using eqString in

let memb = CSExpr {
  expr = CEMember { lhs = CEVar { id = structname }, id = (nameNoSym "0x") }
} in
utest printTest (wrapStmt memb) with
  wrapStmtString "(s._0x);"
using eqString in

let arrow = CSExpr {
  expr = CEArrow { lhs = CEVar { id = structname }, id = (nameNoSym "0x") }
} in
utest printTest (wrapStmt arrow) with
  wrapStmtString "(s->_0x);"
using eqString in

let nop = CSNop {} in
utest printTest (wrapStmt nop) with
  wrapStmtString ";"
using eqString in

let advty =
CTyPtr {
  ty = CTyFun {
    ret = CTyPtr {
      ty = CTyFun {
        ret = CTyPtr {
          ty = CTyStruct { id = Some structtyname, mem = None ()}
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
utest printTest (wrapStmt cast) with
  wrapStmtString "(( struct structty (*(*(*)(char))(int (double))) ) 1);"
using eqString in

let advtydeftop = CTTyDef { ty = advty, id = xname } in
utest printTest (wrapTop advtydeftop) with
  "typedef struct structty (*(*(*x)(char))(int (double)));"
in


let sizety = CSExpr {
  expr = CESizeOfType { ty = advty }
} in
utest printTest (wrapStmt sizety) with
  wrapStmtString "(sizeof(struct structty (*(*(*)(char))(int (double)))));"
using eqString in

let union = CSDef {
  ty = CTyUnion {
    id = Some (nameSym "unionty"),
    mem = Some (
      [(CTyInt {}, Some (nameNoSym "0x")),
       (CTyDouble {}, Some (nameNoSym "y"))]
    )
  },
  id = None (),
  init = None ()
} in
utest printTest (wrapStmt union) with
  wrapStmtString "union unionty {int _0x; double y;};"
using eqString in

let enum = CSDef {
  ty = CTyEnum {
    id = Some (nameSym "enumty"),
    mem = Some (
      [(nameSym "CONST"),
       (nameSym "CONST")]
    )
  },
  id = None (),
  init = None ()
} in
utest printTest (wrapStmt enum) with
  wrapStmtString "enum enumty {CONST, CONST1};"
using eqString in

let sw = CSSwitch {
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
utest printTest (wrapStmt sw) with
  wrapStmtString (strJoin "\n" [
    "switch (1) {",
    "  case 2:",
    "    (x = ((-1) * 3));",
    "    break;",
    "  case 5:",
    "    x;",
    "  case 7:",
    "    fun(1, 'a');",
    "    break;",
    "  default:",
    "    (s._0x);",
    "}"
  ])
using eqString in

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
utest printTest (wrapStmt while) with
  wrapStmtString (strJoin "\n" [
    "while (42) {",
    "  fun(1, 'a');",
    "  {",
    "    x;",
    "    (s._0x);",
    "  }",
    "  continue;",
    "  (s._0x);",
    "}"
  ])
using eqString in

let arg2name = nameSym "arg2" in
let fun = lam body. CTFun {
  ret =
    CTyPtr { ty = CTyFun { ret = CTyChar {}, params = [CTyInt {}, CTyDouble {}] } },
  id = funname,
  params = [(CTyInt {}, nameSym "main"), (CTyChar {}, arg2name)],
  body = body
} in
utest printTest (wrapTop (fun [CSRet { val = Some (CEChar { c = 'a' }) }])) with
  strJoin "\n" [
    "char (*fun(int main1, char arg2))(int, double) {",
    "  return 'a';",
    "}"
  ]
using eqString in

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
  sw,
  while
] in

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
  fun funbody,
  noreturn,
  main
] in

let prog = CPProg { includes = ["<stdio.h>"], tops = tops } in
utest printCProg [mainname] prog with strJoin "\n" [
  "#include <stdio.h>",
  "int x;",
  "char y = 'c';",
  "struct structty {int _0x; double y1;};",
  "int arrinit[][3] = {{1, 2, 3}, {4, 5, 6}};",
  "char (*fun(int main1, char arg2))(int, double) {",
  "  double x = 0.1;",
  "  char strinit[] = \"strinit\";",
  "  struct structty s;",
  "  union unionty {int _0x; double y1;};",
  "  enum enumty {CONST, CONST1};",
  "  (s._0x);",
  "  (( struct structty (*(*(*)(char))(int (double))) ) 1);",
  "  (sizeof(struct structty (*(*(*)(char))(int (double)))));",
  "  (x = ((-1) * 3));",
  "  fun(1, 'a');",
  "  if (2) {",
  "    x;",
  "    fun(1, 'a');",
  "  } else {",
  "    ",
  "  }",
  "  switch (1) {",
  "    case 2:",
  "      (x = ((-1) * 3));",
  "      break;",
  "    case 5:",
  "      x;",
  "    case 7:",
  "      fun(1, 'a');",
  "      break;",
  "    default:",
  "      (s._0x);",
  "  }",
  "  while (42) {",
  "    fun(1, 'a');",
  "    {",
  "      x;",
  "      (s._0x);",
  "    }",
  "    continue;",
  "    (s._0x);",
  "  }",
  "}",
  "void noreturn() {",
  "  return;",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 1;",
  "}"
]
using eqString in

-- let _ = printLn (printCProg [mainname] prog) in

()
