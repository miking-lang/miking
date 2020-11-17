-- Prototype compiler from MExpr to C. Only supports a small subset of MExpr
-- programs. We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--

include "ast.mc"
include "ast-builder.mc"
include "anf.mc"
include "symbolize.mc"

include "c/ast.mc"
include "c/pprint.mc"

include "assoc.mc"

----------------
-- INTRINSICS --
----------------

-- Convenience function for constructing a function given a C type
let _funWithType = use CAst in
  lam ty. lam id. lam params. lam body.
    match ty with CTyFun {ret = ret, params = tyParams} then
      CTFun {
        ret = ret,
        id = id,
        params =
          if eqi (length tyParams) (length params) then
            zipWith (lam ty. lam p. (ty,p)) tyParams params
          else
            error "Incorrect number of parameters in funWithType",
        body = body
      }
    else error "Non-function type given to _funWithType"

-- Customizable set of includes
let _includes = [
  "<stdio.h>",
  "<stdlib.h>"
]

-- Names used in the compiler
let _argc = nameSym "argc"
let _argv = nameSym "argv"
let _main = nameSym "main"
let _malloc = nameSym "malloc"
let _free = nameSym "free"

-- A list of names/intrinsics available in the source code (MExpr)
let _names : [Name] =
  join [
    -- Fixed set of intrinsics
    [_argc, _argv],

    -- Customizable set of intrinsics
    map (lam str. nameSym str) [
      "printf"
    ]
  ]

-- Adds additional names/intrinsics needed by the compiler
let _namesExt : [Name] =
  join [
    _names,
    [
      _main,
      _malloc,
      _free
    ]
  ]

----------------------------------
-- MEXPR -> C COMPILER FRAGMENT --
----------------------------------

lang MExprCCompile = MExprAst + MExprANF + MExprSym + CAst + CPrettyPrint

  sem output =
  | cprog ->
    printCProg _namesExt cprog

  sem compile =
  | prog ->

    -- Debugging function
    let debug = lam file. lam str.
      if false then writeFile file str
      else ()
    in

    let _ = debug "_1-init.mc" (use MExprPrettyPrint in expr2str prog) in

    -- Identify compound types and define them at top-level (structs, tagged
    -- unions).

    -- Symbolize program
    let varEnv =
      assocConstruct {eq=eqString} (map (lam n. (nameGetStr n, n)) _names) in
    let prog = symbolizeExpr {varEnv = varEnv, conEnv = assocEmpty} prog in
    let _ = debug "_2-sym.mc" (use MExprPrettyPrint in expr2str prog) in

    -- Do a (TODO(dlunde,2020-11-16): partial?) ANF transformation, including
    -- lifting out construction of compound data types from expressions (i.e.,
    -- we avoid anonymous record/sequence/variant construction in the middle of
    -- expressions). By doing this, construction of complex data types is
    -- explicit and always bound to variables, which makes translation to C
    -- straightforward.
    let prog = normalizeTerm prog in
    let _ = debug "_3-anf.mc" (use MExprPrettyPrint in expr2str prog) in

    -- Translate to C program. Call `compileTops` and build final program
    -- from result.
    let cprog = CPProg {includes = _includes, tops = compileTops [] [] prog} in
    let _ = debug "_4-final.c" (output cprog) in
    prog

  -------------
  -- C TYPES --
  -------------

  sem compileType =
  | TyUnit _           -> CTyVoid {}
  | TyInt _ | TyBool _ -> CTyInt {}
  | TyFloat _          -> CTyDouble {}
  | TyChar _           -> CTyChar {}
  | TyString _         -> CTyPtr { ty = CTyChar {}}

  | TyArrow _ & ty ->
    recursive let params = lam acc. lam ty.
      match ty with TyArrow {from = from, to = to} then
        params (snoc acc from) to
      else (acc, ty)
    in
    match params [] ty with (params, ret) then
      CTyFun {ret = ret, params = map compileType params}
    else never

  --| TyUnknown _ -> CTyVoid {}
  | TyUnknown _ -> error "Unknown type in compileType"

  | TySeq _ | TyTuple _ | TyRecord _
  | TyCon _ | TyApp _ | TyVar _ -> error "Type not currently supported"

  -------------
  -- HELPERS --
  -------------

  -- Translate sequence of lambdas to C function. Takes an explicit type as
  -- parameter, because the lambdas do not explicitly give the return type,
  -- which is required in C.
  sem compileFun (id: Name) (ty: Type) =
  | TmLam _ & fun ->
    recursive let detachParams: [Name] -> Expr -> ([Name], Expr) =
      lam acc. lam rest.
        match rest with TmLam {ident = ident, body = rest} then
          detachParams (snoc acc (ident)) rest
        else (acc, rest)
    in
    recursive let funTypes: [Type] -> Type -> ([Type], Type) =
      lam acc. lam rest.
        match rest with TyArrow {from = from, to = rest} then
          funTypes (snoc acc from) rest
        else (acc, rest)
    in
    match detachParams [] fun with (params, body) then
      match funTypes [] ty with (paramTypes, retType) then
        if neqi (length params) (length paramTypes) then
          error "Number of parameters in compileFun does not match."
        else
          let params =
            zipWith (lam t. lam id. ((compileType t), id)) paramTypes params in
          let ret = compileType retType in
          let body = compileStmts {ty = ret, name = None ()} [] body in
          CTFun {ret = ret, id = id, params = params, body = body}
      else never
    else never
  | other -> error "Non-function supplied to compileFun"

  -- Compile various let-bound forms. Note that, due to ANF, certain terms can
  -- only appear here (e.g., TmMatch).
  sem compileLet (ident: Name) (ty: Type) =

  -- TmMatch with true as pattern: translate to if statement.
  | TmMatch {target = target, pat = PBool {val = true}, thn = thn, els = els} ->
    let ty = compileType ty in
    let def = match ty with CTyVoid _ then None () else
      Some {ty = ty, id = Some ident, init = None ()}
    in
    let cond = compileExpr target in
    let innerFinal = {ty = ty, name = Some ident} in
    let thn = compileStmts innerFinal [] thn in
    let els = compileStmts innerFinal [] els in
    let stmt = Some (CSIf {cond = cond, thn = thn, els = els}) in
    (def, stmt)

  | TmMatch _ ->
      error "Unsupported TmMatch pattern in compileStmts"

  -- TmSeq: allocate and create a new struct/array.
--   | TmSeq _ ->
--       error "TODO" -- Commented out for now to allow string literals (handled as expression)

  -- TmConApp: allocate and create a new struct.
  | TmConApp _ ->
      error "TODO"

  -- TmRecord: allocate and create new struct.
  | TmRecord _ ->
      error "TODO"

  -- TmRecordUpdate: allocate and create new struct.
  | TmRecordUpdate _ ->
      error "TODO"

  -- Declare variable and call `compileExpr` on body.
  | expr ->
    let ty = compileType ty in
    match ty with CTyVoid _ then
      (None (), Some (CSExpr {expr = compileExpr expr}))
    else
      (Some {ty = ty, id = Some ident,
             init = Some (CIExpr {expr = compileExpr expr})},
       None ())


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem compileTops (accTop: [CTop]) (accMain: [CStmt]) =

  | TmLet {ident = ident, ty = ty, body = body, inexpr = inexpr} ->
    match body with TmLam _ then
      let fun = compileFun ident ty body in
      compileTops (snoc accTop fun) accMain inexpr
    else
      let t = compileLet ident ty body in

      -- We need to specially handle direct initialization, since most things
      -- are not allowed at top-level.
      match t with (Some ({init = Some init} & def), None ()) then
        match init with CIExpr {expr = expr} then
          let def = CTDef {def with init = None ()} in
          let init = CSExpr {expr = CEBinOp {
            op = COAssign {}, lhs = CEVar {id = ident}, rhs = expr}}
          in
          compileTops (snoc accTop def) (snoc accMain init) inexpr
        else match init with _ then
          error "TODO"
        else never

      else match t with (def, init) then
        let accTop =
          match def with Some def then snoc accTop (CTDef def) else accTop in
        let accMain =
          match init with Some init then snoc accMain init else accMain in
        compileTops accTop accMain inexpr

      else error "TODO"

  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let f = lam binding.
      match binding with {ident = ident, ty = ty, body = body} then
        compileFun ident ty body
      else never
    in
    let g = lam fun.
      match fun with CTFun {ret = ret, id = id, params = params, body = body}
      then
        let params = map (lam t. t.0) params in
        CTDef {ty = CTyFun {ret = ret, params = params}, id = Some id,
               init = None ()}
      else never
    in
    let funs = map f bindings in
    let decls = map g funs in
    compileTops (join [accTop, decls, funs]) accMain inexpr

  -- Skip for now. Should be handled by a prior compiler phase.
  | TmConDef {inexpr = inexpr} -> compileTops accTop accMain inexpr

  -- Skip
  | TmUtest {next = next} -> compileTops accTop accMain next

  -- Set up main function
  | rest ->
    let mainTy = CTyFun {
      ret = CTyInt {},
      params = [
        CTyInt {},
        CTyArray {ty = CTyPtr {ty = CTyChar {}}, size = None ()}]}
    in
    let body = compileStmts {ty = CTyInt {}, name = None ()} accMain rest in
    let main = _funWithType mainTy _main [_argc, _argv] body in

    snoc accTop main


  ------------------
  -- C STATEMENTS --
  ------------------

  sem compileStmts (final: {ty: CType, name: Option Name}) (acc: [CStmt]) =

  | TmLet {ident = ident, ty = ty, body = body, inexpr = inexpr} ->
    match compileLet ident ty body with (def, init) then
      let acc =
        match def with Some def then snoc acc (CSDef def) else acc in
      let acc =
        match init with Some init then snoc acc init else acc in
      compileStmts final acc inexpr
    else never

  -- Not allowed here.
  | TmRecLets _ -> error "Recursion not allowed in statements."

  -- Skip for now. Should be handled by a prior compiler phase.
  | TmConDef {inexpr = inexpr} -> compileStmts final acc inexpr

  -- Skip
  | TmUtest {next = next} -> compileStmts final acc next

  -- Return result of `compileExpr` (use `final` to decide between return and
  -- assign)
  | rest ->
    match final with {ty = ty, name = name} then
      match ty with CTyVoid _ then
        snoc acc (CSExpr {expr = compileExpr rest})
      else match name with Some ident then
        snoc acc
          (CSExpr {expr = CEBinOp {
            op = COAssign {}, lhs = CEVar {id = ident}, rhs = compileExpr rest
          }})
      else match name with None () then
        snoc acc (CSRet {val = Some (compileExpr rest)})
      else never
    else never

  -------------------
  -- C EXPRESSIONS --
  -------------------

  sem compileOp =
  | CAddi _ | CAddf _ -> COAdd {}
  | CSubi _ | CSubf _ -> COSub {}
  | CMuli _ | CMulf _ -> COMul {}
  | CDivf _           -> CODiv {}
  | CNegf _           -> CONeg {}
  | CEqi _  | CEqf _  -> COEq {}
  | CLti _  | CLtf _  -> COLt {}

  | CGet _ -> error "TODO: Array indexing"

  | CCons _   | CSnoc _
  | CConcat _ | CLength _ | CHead _
  | CTail _   | CNull _   | CReverse _ -> error "List functions not supported"

  | CEqsym _ -> error "CEqsym not supported"

  | CInt _   | CSymb _
  | CFloat _ | CBool _ | CChar _ -> error "Should not happen"

  sem compileExpr =

  | TmVar {ident = ident} -> CEVar {id = ident}

  | TmApp _ & app ->
    recursive let rec: [Expr] -> Expr -> (Expr, [Expr]) = lam acc. lam t.
      match t with TmApp {lhs = lhs, rhs = rhs} then rec (cons rhs acc) lhs
      else (t, acc)
    in
    match rec [] app with (fun, args) then

      -- Function calls
      match fun with TmVar {ident = ident} then
        CEApp {fun = ident, args = map compileExpr args}

      else match fun with TmConst {val = val} then
        let op = compileOp val in

        -- Unary operators
        if eqi 1 (length args) then
          CEUnOp {op = op, arg = compileExpr (head args)}

        -- Binary operators
        else if eqi 2 (length args) then
          CEBinOp {op = op, lhs = compileExpr (head args),
                   rhs = compileExpr (last args)}

        else error "Encountered operator with more than two operands in compileExpr."
      else error "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam _ -> error "Anonymous function not allowed in compileExpr."

  -- C strings
  | TmSeq {tms = tms} ->
    let toChar = lam expr.
      match expr with TmConst {val = CChar {val = val}} then Some val
      else None ()
    in
    match optionMapM toChar tms with Some str then CEString {s = str}
    else error "Should not happen (due to ANF)"

  -- Should not occur due to ANF.
  | TmRecord _ | TmRecordUpdate _ | TmLet _
  | TmRecLets _ | TmConDef _ | TmConApp _
  | TmMatch _ | TmUtest _ | TmSeq _ -> error "Should not happen (due to ANF)"

  -- Unit literal (encoded as 0 in C) is encoded as empty TmRecord in MExpr.
  | TmRecord {bindings = []} -> CEInt {i = 0}

  -- Literals
  | TmConst {val = val} ->
    match val      with CInt   {val = val} then CEInt   {i = val}
    else match val with CFloat {val = val} then CEFloat {f = val}
    else match val with CChar  {val = val} then CEChar  {c = val}
    else match val with CBool  {val = val} then
      let val = match val with true then 1 else 0 in
      CEInt {i = val}
    else error "Unsupported literal"

  -- Should not occur?
  | TmNever _ -> error "Never term found in compileExpr"

end

lang TestLang = MExprCCompile + MExprPrettyPrint

mexpr
use TestLang in

-- Heavily type-annotated version of factorial function
let factorial =
  reclet_ "factorial" (tyarrow_ tyint_ tyint_)
    (lam_ "n" tyint_
      (asc_ tyint_
        (if_ (asc_ tybool_ (eqi_ (var_ "n") (int_ 0)))
          (int_ 1)
          (asc_ tyint_
            (muli_ (var_ "n")
              (asc_ tyint_
                (app_ (var_ "factorial")
                  (asc_ tyint_ (subi_ (var_ "n") (int_ 1))))))))))
in

-- Heavily type-annotated versions of mutually recursive odd and even functions
let oddEven = reclets_ [

    ("odd", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (asc_ tybool_
         (if_ (asc_ tybool_ (eqi_ (var_ "x") (int_ 1)))
           true_
           (asc_ tybool_
             (if_ (asc_ tybool_ (lti_ (var_ "x") (int_ 1)))
                false_
                (asc_ tybool_
                  (app_ (var_ "even")
                    (asc_ tyint_ (subi_ (var_ "x") (int_ 1)))))))))),

    ("even", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (asc_ tybool_
         (if_ (asc_ tybool_ (eqi_ (var_ "x") (int_ 0)))
            true_
            (asc_ tybool_
              (if_ (asc_ tybool_ (lti_ (var_ "x") (int_ 0)))
                 false_
                 (asc_ tybool_
                   (app_ (var_ "odd")
                     (asc_ tyint_ (subi_ (var_ "x") (int_ 1))))))))))

] in

let printf = lam str. lam ls.
  asc_ tyunit_
    (appSeq_ (var_ "printf")
       (cons (asc_ tystr_ (str_ str))
          ls))
in

let mprog = bindall_ [
  factorial,
  oddEven,
  printf "factorial(5) is: %d\n" [
    asc_ tyint_ (app_ (var_ "factorial") (int_ 5))
  ],
  let_ "boolres" tystr_
    (if_ (asc_ tybool_ (app_ (var_ "odd") (int_ 7)))
       (asc_ tystr_ (str_ "true")) (asc_ tystr_ (str_ "false"))),
  printf "7 odd? %s.\n" [(var_ "boolres")],
  int_ 0 -- Main must return an integer
] in

let _ = compile mprog in

()
