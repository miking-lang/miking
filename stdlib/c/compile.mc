-- Compilation from MExpr to C. Only supports a small subset of MExpr
-- programs. We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--
-- Assumptions:
-- * All identifiers are unique (i.e., are symbolized)
-- * All lets and lambdas have proper type annotations
-- (TODO(dlunde,2020-10-03): Add type annotations to all lets). This requirement
-- can be weakened when we have a type system.

include "mexpr/ast.mc"
include "mexpr/anf.mc"
include "mexpr/programs.mc"

include "ast.mc"
include "pprint.mc"

lang MExprCCompile = MExprAst + CAst + MExprANF

  sem compile =
  | prog ->
    -- 1. Identify compound types and define them at top-level (structs, tagged
    -- unions).

    -- 2. Do a (TODO(dlunde,2020-11-10): partial) ANF transformation, lifting
    -- out construction of compound data types from expressions (i.e., we avoid
    -- anonymous record/sequence/variant construction in the middle of
    -- expressions). By doing this, construction of complex data types is
    -- explicit and always bound to variables, which makes translation to C
    -- straightforward.
    let prog = normalizeTerm prog in

    -- 3. Translate to C program. Call `compileTops` and build final program
    -- from result.
    CPProg {tops = compileTops [] [] prog}


  -------------
  -- C TYPES --
  -------------

  sem compileType =
  | TyUnit _ | TyBool _ | TyInt _ -> CTyInt {}
  | TyFloat _ -> CTyDouble {}
  | TyChar _ -> CTyChar {}
  | TyArrow _ & ty ->
    recursive let params = lam acc. lam ty.
      match ty with TyArrow {from = from, to = to} then
        params (snoc acc from) to
      else (acc, ty)
    in
    match params [] ty with (params, ret) then
      CTyFun {ret = ret, params = map compileType params}
    else never

  -- How do we handle this properly?
  | TyUnknown _ -> CTyVoid {}

  | TySeq _ | TyTuple _ | TyRecord _
  | TyCon _ | TyApp _ | TyString _
  | TyVar _ -> error "Type not currently supported"

  -----------------
  -- C TOP-LEVEL --
  -----------------

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
          let body = compileStmts (None ()) [] body in
          CTFun {ret = ret, id = id, params = params, body = body}
      else never
    else never
  | other -> error "Non-function supplied to compileFun"

  sem compileTops (accTop: [CTop]) (accMain: [CStmt]) =

  | TmLet {ident = ident, ty = ty, body = body, inexpr = inexpr} ->
    match body with TmLam _ then
      let fun = compileFun ident ty body in
      compileTops (snoc accTop fun) accMain inexpr
    else
      let decl = CTDef {ty = compileType ty, id = Some ident, init = None ()} in
      let init = CSExpr {expr = CEBinOp {
        op = COAssign {}, lhs = CEVar {id = ident}, rhs = compileExpr body
      }} in
      compileTops (snoc accTop decl) (snoc accMain init) inexpr

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
    let main = CTFun {
      ret = CTyInt {}, id = nameSym "main",
      params = [
        (CTyInt {}, nameSym "argc"),
        (CTyArray {ty = CTyPtr {ty = CTyChar {}}, size = None ()},
         nameSym "argv")
      ],
      body = compileStmts (None ()) accMain rest
    }
    in
    snoc accTop main


  ------------------
  -- C STATEMENTS --
  ------------------

  sem compileStmts (final: Some Name) (acc: [CStmt]) =

  -- Compile various let-bound forms. Note that, due to ANF, certain terms can
  -- only appear here (e.g., TmMatch, TmSeq)
  | TmLet {ident = ident, ty = ty, body = body, inexpr = inexpr} ->

    -- * TmMatch with true as pattern: translate to if statement.
    match body with TmMatch {target = target, pat = PBool {val = true},
                             thn = thn, els = els} then
      let decl = CSDef {ty = compileType ty, id = Some ident, init = None ()} in
      let cond = compileExpr target in
      let thn = compileStmts (Some ident) [] thn in
      let els = compileStmts (Some ident) [] els in
      let stmt = CSIf {cond = cond, thn = thn, els = els} in
      compileStmts final (snoc (snoc acc decl) stmt) inexpr

    else match body with TmMatch _ then
      error "Unsupported TmMatch pattern in compileStmts"

    -- * TmSeq: allocate and create a new struct/array.
    else match body with TmSeq _ then
      error "TODO"

    -- * TmConApp: allocate and create a new struct.
    else match body with TmConApp _ then
      error "TODO"

    -- * TmRecord: allocate and create new struct.
    else match body with TmRecord _ then
      error "TODO"

    -- * TmRecordUpdate: allocate and create new struct.
    else match body with TmRecordUpdate _ then
      error "TODO"

    -- Declare variable and call `compileExpr` on body.
    else
      let def = CSDef {
        ty = compileType ty, id = Some ident,
        init = Some (CIExpr {expr = (compileExpr body)})
      } in
      compileStmts final (snoc acc def) inexpr

  -- Not allowed here.
  | TmRecLets _ -> error "Recursion not allowed in statements."

  -- Skip for now. Should be handled by a prior compiler phase.
  | TmConDef {inexpr = inexpr} -> compileStmts final acc inexpr

  -- Skip
  | TmUtest {next = next} -> compileStmts final acc next

  -- Return result of `compileExpr` (use "final")
  | rest ->
    let final = match final with Some ident then
      CSExpr {expr = CEBinOp {
        op = COAssign {}, lhs = CEVar {id = ident}, rhs = compileExpr rest
      }}
    else CSRet {val = Some (compileExpr rest)} in
    snoc acc final


  -------------------
  -- C EXPRESSIONS --
  -------------------

  sem compileOp =
  | CAddi _ | CAddf _ -> COAdd {}
  | CSubi _ | CSubf _ -> COSub {}
  | CMuli _ | CMulf _ -> COMul {}
  | CDivf _ -> CODiv {}
  | CNegf _ -> CONeg {}
  | CEqi _ | CEqf _ -> COEq {}
  | CLti _ | CLtf _ -> COLt {}

  | CGet _ -> error "TODO: Array indexing"

  | CCons _ | CSnoc _ | CConcat _
  | CLength _ | CHead _ | CTail _
  | CNull _ | CReverse _ -> error "List functions not supported"

  | CEqsym _ -> error "CEqsym not supported"

  | CInt _ | CSymb _ | CFloat _
  | CBool _ | CChar _ -> error "Should not happen"


  sem compileExpr =

  -- Direct translation.
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

        else error "Should not happen (ternary operator)"
      else error "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam _ -> error "Anonymous function not allowed in compileExpr."

  -- Should not occur due to ANF.
  | TmRecord _ | TmRecordUpdate _ | TmLet _
  | TmRecLets _ | TmConDef _ | TmConApp _
  | TmMatch _ | TmUtest _ | TmSeq _ -> error "Should not happen (due to ANF)"

  -- Unit literal is encoded as TmRecord
  | TmRecord {bindings = []} -> CEInt {i = 0}

  -- Literals
  | TmConst {val = val} ->
    match val with CInt {val = val} then CEInt {i = val}
    else match val with CFloat {val = val} then CEFloat {f = val}
    else match val with CChar {val = val} then CEChar {c = val}
    else match val with CBool {val = val} then
      let val = match val with true then 1 else 0 in
      CEInt {i = val}
    else error "Unsupported literal"

  -- Should not occur?
  | TmNever _ -> error "Never term found in compileExpr"

end

lang TestLang = MExprCCompile + MExprPrettyPrint + CPrettyPrint

mexpr
use TestLang in

-- Things to test:
-- * global data
-- * function creating and returning record

let mprog = bindall_ [
  programsFactorial,
  programsOddEven
]
in

let _ = print (printCProg (compile mprog)) in

()
