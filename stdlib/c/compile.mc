-- Prototype compiler from MExpr to C. Only supports a small subset of MExpr
-- programs. We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--
-- TODO
-- * Types need to be revised after changes in MExpr

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"
include "mexpr/symbolize.mc"

include "ast.mc"
include "pprint.mc"

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

-----------------
-- ENVIRONMENT --
-----------------

-- NOTE
-- * Recursive record/variant types?

type CompileCEnv = {

  -- Maps encountered compound types to c struct types
  typeMap: AssocMap Type CType

}

let compileCEnvEmpty = {typeMap = assocEmpty}

----------------------------------
-- MEXPR -> C COMPILER FRAGMENT --
----------------------------------

lang MExprCCompile = MExprAst + MExprANF + MExprSym + CAst + CPrettyPrint

  sem output =
  | cprog -> printCProg _namesExt cprog

  sem compile =
  | prog ->

    -- Debugging function
    let debug = lam file. lam str.
      if true then writeFile file str
      else ()
    in

    let _ = debug "_1-init.mc" (use MExprPrettyPrint in expr2str prog) in

    -- TODO Identify compound types and define them at top-level (structs, tagged
    -- unions).

    -- Symbolize program
    let varEnv =
      seq2assoc {eq=eqString} (map (lam n. (nameGetStr n, n)) _names) in
    let prog = symbolizeExpr {varEnv = varEnv, conEnv = assocEmpty} prog in
    let _ = debug "_2-sym.mc" (use MExprPrettyPrint in expr2str prog) in

    -- Perform (TODO(dlunde,2020-11-16): partial?) ANF transformation, including
    -- lifting out construction of compound data types from expressions (i.e.,
    -- we avoid anonymous record/sequence/variant construction in the middle of
    -- expressions). By doing this, construction of complex data types is
    -- explicit and always bound to variables, which makes translation to C
    -- straightforward.
    let prog = normalizeTerm prog in
    let _ = debug "_3-anf.mc" (use MExprPrettyPrint in expr2str prog) in

    -- Translate to C program. Call `compileTops` and build final program
    -- from result.
    match compileTops compileCEnvEmpty [] [] prog with (env, tops) then
      -- TODO Build type definitions from env
      let cprog = CPProg {includes = _includes, tops = tops} in
      let _ = debug "_4-final.c" (output cprog) in
      cprog
    else never

  -------------
  -- C TYPES --
  -------------

  sem compileType (env: CompileCEnv) =
  | TyInt _ | TyBool _      -> (env, CTyInt {})
  | TyFloat _               -> (env, CTyDouble {})
  | TyChar _                -> (env, CTyChar {})
  | TySeq { ty = TyChar _ } -> (env, CTyPtr { ty = CTyChar {}})

  | TyArrow _ & ty ->
    recursive let params = lam acc. lam ty.
      match ty with TyArrow {from = from, to = to} then
        params (snoc acc from) to
      else (acc, ty)
    in
    match params [] ty with (params, ret) then
      match mapAccumL compileType env params with (env, params) then
        match compileType env ret with (env, ret) then
          (env, CTyFun {ret = ret, params = params})
        else never
      else never
    else never

  | TyRecord { fields = fields } ->
    -- Check for unit type
    if eqi (assocLength fields) 0 then (env, CTyVoid {}) else
      error "TODO" -- TODO: This is where we modify the environment
  | TyVar _ -> error "TODO" -- TODO: This is where we modify the environment

  --| TyUnknown _ -> CTyVoid {}
  | TyUnknown _ -> error "Unknown type in compileType"

  | TySeq _
  | TyApp _ -> error "Type not currently supported"


  -------------
  -- HELPERS --
  -------------

  -- Translate sequence of lambdas to C function. Takes an explicit type as
  -- parameter, because the lambdas do not explicitly give the return type,
  -- which is required in C.
  sem compileFun (env: CompileCEnv) (id: Name) (ty: Type) =
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
          match mapAccumL compileType env paramTypes with (env, paramTypes) then
            let params = zipWith (lam t. lam id. (t, id)) paramTypes params in
            match compileType env retType with (env, ret) then
              match compileStmts env {ty = ret, name = None ()} [] body
              with (env, body) then
                (env, CTFun {ret = ret, id = id, params = params, body = body})
              else never
            else never
          else never
      else never
    else never
  | other -> error "Non-function supplied to compileFun"

  -- Compile various let-bound forms. Note that, due to ANF, certain terms can
  -- only appear here (e.g., TmMatch).
  sem compileLet (env: CompileCEnv) (ident: Name) (ty: Type) =

  -- TmMatch with true as pattern: translate to if statement.
  | TmMatch {target = target, pat = PatBool {val = true}, thn = thn, els = els} ->
    match compileType env ty with (env, ty) then
      let def = match ty with CTyVoid _ then None () else
        Some {ty = ty, id = Some ident, init = None ()}
      in
      let cond = compileExpr target in
      let innerFinal = {ty = ty, name = Some ident} in
      match compileStmts env innerFinal [] thn with (env, thn) then
        match compileStmts env innerFinal [] els with (env, els) then
          let stmt = Some (CSIf {cond = cond, thn = thn, els = els}) in
          (env, def, stmt)
        else never
      else never
    else never

  | TmMatch _ -> error "Unsupported TmMatch pattern in compileStmts"

  -- TmSeq: allocate and create a new struct/array.
--   | TmSeq _ ->
--       error "TODO" -- Commented out for now to allow string literals (handled as expression)

  -- TmConApp: allocate and create a new struct.
  | TmConApp _ -> error "TODO"

  -- TmRecord: allocate and create new struct.
  | TmRecord _ -> error "TODO"

  -- TmRecordUpdate: allocate and create new struct.
  | TmRecordUpdate _ -> error "TODO"

  -- Declare variable and call `compileExpr` on body.
  | expr ->
    match compileType env ty with (env, ty) then
      match ty with CTyVoid _ then
        (env, None (), Some (CSExpr {expr = compileExpr expr}))
      else
        (env,
         Some {ty = ty, id = Some ident,
               init = Some (CIExpr {expr = compileExpr expr})},
         None ())
    else never


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem compileTops (env: CompileCEnv) (accTop: [CTop]) (accMain: [CStmt]) =

  | TmLet {ident = ident, tyBody = tyBody, body = body, inexpr = inexpr} ->
    match body with TmLam _ then
      match compileFun env ident tyBody body with (env, fun) then
        compileTops env (snoc accTop fun) accMain inexpr
      else never
    else
      match compileLet env ident tyBody body with (env, def, init) then
        -- We need to specially handle direct initialization, since most things
        -- are not allowed at top-level.
        let t = (def, init) in
        match t with (Some ({init = Some init} & def), None ()) then
          match init with CIExpr {expr = expr} then
            let def = CTDef {def with init = None ()} in
            let init = CSExpr {expr = CEBinOp {
              op = COAssign {}, lhs = CEVar {id = ident}, rhs = expr}}
            in
            compileTops env (snoc accTop def) (snoc accMain init) inexpr
          else match init with _ then
            error "TODO"
          else never

        else match t with (def, init) then
          let accTop =
            match def with Some def then snoc accTop (CTDef def) else accTop in
          let accMain =
            match init with Some init then snoc accMain init else accMain in
          compileTops env accTop accMain inexpr

        else error "TODO"
      else never


  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let f = lam env. lam binding.
      match binding with {ident = ident, ty = ty, body = body} then
        compileFun env ident ty body
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
    match mapAccumL f env bindings with (env, funs) then
      let decls = map g funs in
      compileTops env (join [accTop, decls, funs]) accMain inexpr
    else never

  -- Skip for now. Should be handled by a prior compiler phase.
  | TmConDef {inexpr = inexpr} -> compileTops env accTop accMain inexpr

  -- Skip
  | TmUtest {next = next} -> compileTops env accTop accMain next

  -- Set up main function
  | rest ->
    let mainTy = CTyFun {
      ret = CTyInt {},
      params = [
        CTyInt {},
        CTyArray {ty = CTyPtr {ty = CTyChar {}}, size = None ()}]}
    in
    match compileStmts env {ty = CTyInt {}, name = None ()} accMain rest
    with (env, body) then
      let main = _funWithType mainTy _main [_argc, _argv] body in
      (env,snoc accTop main)
    else never


  ------------------
  -- C STATEMENTS --
  ------------------

  sem compileStmts
    (env: CompileCEnv) (final: {ty: CType, name: Option Name}) (acc: [CStmt]) =

  | TmLet {ident = ident, tyBody = tyBody, body = body, inexpr = inexpr} ->
    match compileLet env ident tyBody body with (env, def, init) then
      let acc =
        match def with Some def then snoc acc (CSDef def) else acc in
      let acc =
        match init with Some init then snoc acc init else acc in
      compileStmts env final acc inexpr
    else never

  -- Not allowed here.
  | TmRecLets _ -> error "Recursion not allowed in statements."

  -- Skip for now. Should be handled by a prior compiler phase.
  | TmConDef {inexpr = inexpr} -> compileStmts env final acc inexpr

  -- Skip
  | TmUtest {next = next} -> compileStmts env final acc next

  -- Return result of `compileExpr` (use `final` to decide between return and
  -- assign)
  | rest ->
    match final with {ty = ty, name = name} then
      match ty with CTyVoid _ then
        (env, snoc acc (CSExpr {expr = compileExpr rest}))
      else match name with Some ident then
        (env,
         snoc acc
          (CSExpr {expr = CEBinOp {
            op = COAssign {}, lhs = CEVar {id = ident}, rhs = compileExpr rest
          }}))
      else match name with None () then
        (env, snoc acc (CSRet {val = Some (compileExpr rest)}))
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
  | CConcat _ | CLength _
  | CReverse _ -> error "List functions not supported"

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
      (withType tyint_
        (if_ (withType tybool_ (eqi_ (var_ "n") (int_ 0)))
          (int_ 1)
          (withType tyint_
            (muli_ (var_ "n")
              (withType tyint_
                (app_ (var_ "factorial")
                  (withType tyint_ (subi_ (var_ "n") (int_ 1))))))))))
in

-- Heavily type-annotated versions of mutually recursive odd and even functions
let oddEven = reclets_ [

    ("odd", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (withType tybool_
         (if_ (withType tybool_ (eqi_ (var_ "x") (int_ 1)))
           true_
           (withType tybool_
             (if_ (withType tybool_ (lti_ (var_ "x") (int_ 1)))
                false_
                (withType tybool_
                  (app_ (var_ "even")
                    (withType tyint_ (subi_ (var_ "x") (int_ 1)))))))))),

    ("even", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (withType tybool_
         (if_ (withType tybool_ (eqi_ (var_ "x") (int_ 0)))
            true_
            (withType tybool_
              (if_ (withType tybool_ (lti_ (var_ "x") (int_ 0)))
                 false_
                 (withType tybool_
                   (app_ (var_ "odd")
                     (withType tyint_ (subi_ (var_ "x") (int_ 1))))))))))

] in

let printf = lam str. lam ls.
  appSeq_ (var_ "printf") (cons (withType tystr_ (str_ str)) ls)
in

let mprog = bindall_ [
  factorial,
  oddEven,
  let_ "_" tyunit_ (printf "factorial(5) is: %d\n" [
    withType tyint_ (app_ (var_ "factorial") (int_ 5))
  ]),
  let_ "boolres" tystr_
    (if_ (withType tybool_ (app_ (var_ "odd") (int_ 7)))
       (withType tystr_ (str_ "true")) (withType tystr_ (str_ "false"))),
  let_ "_" tyunit_ (printf "7 odd? %s.\n" [(var_ "boolres")]),
  int_ 0 -- Main must return an integer
] in

let _ = compile mprog in

()
