-- Compiles a subset of MExpr programs to C.
-- * Anonymous functions are not supported, except when bound to variables at
-- top-level.
-- * Top-level MExpr variables (including functions) are compiled to global C
-- data.
-- * Non-primitive data types are always stored in the heap, and handled
-- through pointers.
-- * There is no garbage collection. Currently, memory is never freed.
-- * Any top-level code besides functions and data declarations are returned as
-- a list of C statements. Usually, these statements should be
-- put in a C `main` function or similar.
--
-- TODO
-- * Compile sequences to structs containing length and an array (requires
-- changes to type lift)

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"
include "mexpr/builtin.mc"
include "mexpr/boot-parser.mc"

include "ast.mc"
include "pprint.mc"

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Convenience function for constructing a function given a C type
let _funWithType = use CAst in
  lam ty. lam id. lam params. lam body.
    match ty with CTyFun { ret = ret, params = tyParams } then
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

-- Check for unit type
let _isUnitTy = use RecordTypeAst in lam ty.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields
  else false

--------------------------
-- COMPILER DEFINITIONS --
--------------------------

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
let _printf = nameSym "printf"

-- C names that must be pretty printed using their exact string
let _compilerNames : [Name] = [
  _argc,
  _argv,
  _main,
  _malloc,
  _free,
  _printf
]

let _constrKey = "constr"

--------------------------
-- COMPILER ENVIRONMENT --
--------------------------

type ConstrDataEnv = [(Name,String)]

type CompileCEnv = {

  -- Map from constructor names to data field names
  constrData: ConstrDataEnv,

  -- The initial type environment produced by type lifting
  typeEnv: [(Name,Type)]

}

recursive
  let _unwrapType = use VarTypeAst in
    lam tyEnv: AssocSeq Name Type. lam ty: Type.
    match ty with TyVar { ident = ident } then
      match assocSeqLookup { eq = nameEq } ident tyEnv with Some ty then
        _unwrapType tyEnv ty
      else error "TyVar not defined in environment"
    else ty
end

let compileCEnvEmpty = { typeEnv = [], constrData = [] }

----------------------------------
-- MEXPR -> C COMPILER FRAGMENT --
----------------------------------

lang MExprCCompile = MExprAst + CAst

  sem allocStruct (ty: Type) =
  -- Intentionally left blank

  sem free =
  -- Intentionally left blank

  -- Entry point
  sem compile (typeEnv: [(Name,Type)]) =
  | prog ->

    let decls: [CTop] =
      foldl (lam acc. lam t. genTyDecls acc t.0 t.1) [] typeEnv in
    let defs: [CTop] =
      foldl (lam acc. lam t. genTyDefs acc t.0 t.1) [] typeEnv in
    let postDefs: (ConstrDataEnv, [CTop]) =
      foldl (lam acc. lam t. genTyPostDefs acc t.0 t.1) ([],[]) typeEnv in

    match postDefs with (constrData, postDefs) then
      let env = {{ compileCEnvEmpty with constrData = constrData }
                                    with typeEnv = typeEnv } in
      match compileTops env [] [] prog with (tops, inits) then
        (join [decls, defs, postDefs], tops, inits)
      else never
    else never


  sem genTyDecls (acc: [CTop]) (name: Name) =

  | TyVariant _ ->
    let decl = CTTyDef {
      ty = CTyPtr { ty = CTyStruct { id = Some name, mem = None () } },
      id = name
    } in
    cons decl acc

  | _ -> acc


  sem genTyDefs (acc: [CTop]) (name: Name) =

  | TyVariant _ -> acc

  | TyRecord { fields = fields } ->
    let fieldsLs: [(CType,String)] =
      mapFoldWithKey (lam acc. lam k. lam ty.
        let ty = compileType ty in
        snoc acc (ty, Some (sidToString k))) [] fields in
    let def = CTTyDef {
      ty = CTyPtr { ty = CTyStruct { id = Some name, mem = Some fieldsLs } },
      id = name
    } in
    cons def acc

  | ty ->
    let def = CTTyDef { ty = compileType ty, id = name } in
    cons def acc


  sem genTyPostDefs (acc: (ConstrDataEnv, [CTop])) (name: Name) =

  | TyVariant { constrs = constrs } ->
    match acc with (constrData, postDefs) then
      let constrLs: [(Name, CType)] =
        mapFoldWithKey (lam acc. lam name. lam ty.
          let ty = compileType ty in
            snoc acc (name, ty)) [] constrs in
      let constrLs: [(Name, String, CType)] =
        mapi (lam i. lam t: (Name,CType).
          (t.0, cons 'd' (int2string i), t.1)) constrLs in
      let constrData = foldl (lam acc. lam t: (Name,String,CType).
        assocSeqInsert t.0 t.1 acc) constrData constrLs in
      let def = CTDef {
        ty = CTyStruct {
          id = Some name,
          mem = Some [
            (CTyEnum {
               id = None (),
               mem = Some (map (lam t. t.0) constrLs)
             }, Some _constrKey),
            (CTyUnion {
               id = None (),
               mem = Some (map
                 (lam t: (Name,String,CType). (t.2, Some t.1)) constrLs)
             }, None ())
          ] },
        id = None (), init = None ()
      }
      in
      (constrData, cons def postDefs)
    else never

  | _ -> acc



  -------------
  -- C TYPES --
  -------------

  sem compileType =

  | TyInt _   -> CTyInt {}
  | TyFloat _ -> CTyDouble {}
  | TyBool _
  | TyChar _  -> CTyChar {}

  | TyArrow _ & ty ->
    error "Type not currently supported"
    -- recursive let params = lam acc. lam ty.
    --   match ty with TyArrow { from = from, to = to } then
    --     params (snoc acc from) to
    --   else (acc, ty)
    -- in
    -- match params [] ty with (params, ret) then
    --   match mapAccumL compileType params with (env, params) then
    --     match compileType ret with (env, ret) then
    --       (env, CTyFun { ret = ret, params = params })
    --     else never
    --   else never
    -- else never

  | TyRecord { fields = fields } ->
    if mapIsEmpty fields then CTyVoid {}
    else
      error "ERROR: TyRecord should not occur in compileType. Did you run type lift?"

  | TyVar { ident = ident } -> CTyVar { id = ident }

  -- | TyUnknown _ -> (env, CTyChar {})
  | TyUnknown _ -> error "Unknown type in compileType"

  | TySeq { ty = TyChar _ } -> CTyPtr { ty = CTyChar {} }

  | TyVariant _ ->
    error "TyVariant should not occur in compileType. Did you run type lift?"

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
        match rest with
        TmLam { ty = ty, ident = ident, body = rest } then
          match ty with TyArrow { from = fromTy } then
            if _isUnitTy fromTy then detachParams acc rest
            else detachParams (snoc acc ident) rest
          else error "Incorrect type in compileFun"
        else (acc, rest)
    in
    recursive let funTypes: [Type] -> Type -> ([Type], Type) =
      lam acc. lam rest.
        match rest with TyArrow { from = from, to = rest } then
          if _isUnitTy from then funTypes acc rest
          else funTypes (snoc acc from) rest
        else (acc, rest)
    in
    match detachParams [] fun with (params, body) then
      match funTypes [] ty with (paramTypes, retType) then
        if neqi (length params) (length paramTypes) then
          error "Number of parameters in compileFun does not match."
        else
          match map compileType paramTypes with paramTypes then
            let params = zipWith (lam t. lam id. (t, id)) paramTypes params in
            match compileType retType with ret then
              match compileStmts env { name = None () } [] body
              with (env, body) then
                (env, CTFun { ret = ret, id = id, params = params, body = body })
              else never
            else never
          else never
      else never
    else never

  | _ -> error "Non-function supplied to compileFun"


  -- Compile patterns
  sem compilePat (env: CompileCEnv)
    (conds: [CExpr]) (defs: [(Name,CExpr)]) (target: CExpr) (ty: Type) =

  | PatNamed { ident = PName ident } ->
    let def = CSDef {
      ty = compileType ty,
      id = Some ident,
      init = Some (CIExpr { expr = target })
    } in
    ( conds, snoc defs def )

  | PatNamed { ident = PWildcard _ } -> (conds, defs)

  | PatBool { val = val } ->
    ( snoc conds (CEBinOp {
        op = COEq {},
        lhs = target,
        rhs = let val = match val with true then 1 else 0 in CEInt { i = val }
      }),
      defs )

  | PatRecord { bindings = bindings } ->
    match env with { typeEnv = typeEnv } then
      let f = lam acc. lam sid. lam subpat.
        match acc with (conds, defs) then
          match _unwrapType typeEnv ty with TyRecord { fields = fields } then
            match mapLookup sid fields with Some ty then
              let label = sidToString sid in
              compilePat env conds defs
                (CEArrow { lhs = target, id = label }) ty subpat

            else error "Label does not match between PatRecord and TyRecord"
          else error "Type not TyVar for PatRecord in compilePat"
        else never
      in
      mapFoldWithKey f (conds, defs) bindings
    else never

  | PatCon { ident = ident, subpat = subpat } ->
    match env with { typeEnv = typeEnv, constrData = constrData } then
      let dataKey =
        match assocSeqLookup { eq = nameEq } ident constrData
        with Some dataKey then dataKey
        else error "Data key not found for PatCon in compilePat"
      in
      match _unwrapType typeEnv ty with TyVariant { constrs = constrs } then
        match mapLookup ident constrs with Some ty then
          compilePat env (snoc conds (CEBinOp {
              op = COEq {},
              lhs = CEArrow { lhs = target, id = _constrKey },
              rhs = CEVar { id = ident }
            }))
            defs (CEArrow { lhs = target, id = dataKey }) ty subpat
        else error "Invalid constructor in compilePat"
      else error "Not a TyVariant for PatCon in compilePat"
    else never
  | _ -> error "Pattern not supported"


  -- Compile various let-bound forms. Note that, if the program is in ANF,
  -- most terms can only appear here (e.g., TmMatch).
  sem compileLet (env: CompileCEnv) (ident: Name) =

  | TmMatch { ty = tyMatch, target = target, pat = pat,
              thn = thn, els = els } ->

    -- Allocate memory for return value of match expression
    let def = match ty with CTyVoid _ then None () else
      Some { ty = compileType tyMatch, id = Some ident, init = None () }
    in

    let ctarget = compileExpr target in

    -- Compile branches
    let innerFinal = { name = Some ident } in
    match compileStmts env innerFinal [] thn with (env, thn) then
      match compileStmts env innerFinal [] els with (env, els) then

        -- Generate conditions corresponding to pat, and add pattern bindings
        -- to start of thn
        match compilePat env [] [] ctarget (ty target) pat
        with (conds, defs) then

          -- Compute joint condition
          let cond = foldr1 (lam cond. lam acc.
              CEBinOp { op = COAnd {}, lhs = cond, rhs = acc }
            ) conds in

          -- TODO Empty cond => no if needed

          -- Produce final statement
          let stmt = CSIf { cond = cond, thn = concat defs thn, els = els } in
          (env, def, [stmt])

        else never
      else never
    else never

  -- TmSeq: allocate and create a new array. Special handling of strings for now.
  | TmSeq { ty = ty, tms = tms } ->
    let ty = compileType ty in
    let toChar = lam expr.
      match expr with TmConst { val = CChar { val = val } } then Some val
      else None ()
    in
    match optionMapM toChar tms with Some str then (
      env,
      Some { ty = ty, id = Some ident,
             init = Some (CIExpr { expr = CEString { s = str } }) },
      []
    )
    else error "TODO: TmSeq"

  -- TmConApp: allocate and create a new struct.
  | TmConApp { ident = constrIdent, body = body, ty = ty } ->
    let ty = compileType ty in
    match env with { constrData = constrData } then
      let def = allocStruct ty ident in
      let dataKey =
        match assocSeqLookup { eq = nameEq } constrIdent constrData
        with Some dataKey then dataKey
        else error "Data key not found for TmConApp in compileLet"
      in
      let init = [
        -- Set constructor tag
        CSExpr {
          expr = CEBinOp {
            op = COAssign {},
            lhs = CEArrow {
              lhs = CEVar { id = ident }, id = _constrKey
            },
            rhs = CEVar { id = constrIdent }
          }
        },
        -- Set data
        CSExpr {
          expr = CEBinOp {
            op = COAssign {},
            lhs = CEArrow {
              lhs = CEVar { id = ident }, id = dataKey
            },
            rhs = compileExpr body
          }
        }
      ] in
      (env, Some def, init)

    else never

  -- TmRecord: allocate and create new struct, unless it is an empty record (in
  -- which case it is compiled to the integer 0)
  | TmRecord { ty = ty, bindings = bindings } ->
    let ty = compileType ty in
    if mapIsEmpty bindings then (
      env,
      Some { ty = ty, id = Some ident,
             init = Some (CIExpr { expr = CEInt { i = 0 } }) },
      []
    )
    else
      let def = allocStruct ty ident in
      let init = mapMapWithKey (lam sid. lam expr.
        CSExpr {
          expr = CEBinOp {
            op = COAssign {},
            lhs = CEArrow {
              lhs = CEVar { id = ident }, id = sidToString sid
            },
            rhs = compileExpr expr
          }
        }
      ) bindings in
      (env, Some def, mapValues init)

  -- TmRecordUpdate: allocate and create new struct.
  | TmRecordUpdate _ -> error "TODO: TmRecordUpdate"

  -- Declare variable and call `compileExpr` on body.
  | ( TmVar { ty = ty } | TmApp { ty = ty } | TmLet { ty = ty }
    | TmRecLets { ty = ty } | TmConst { ty = ty } | TmSeq { ty = ty }
    | TmType { ty = ty } | TmConDef { ty = ty } | TmUtest { ty = ty }
    | TmNever { ty = ty }) & expr ->
    if _isUnitTy ty then
      match expr with TmVar _ then (env, None (), None())
      else (env, None (), [CSExpr { expr = compileExpr expr }])

    else
      let ty = compileType ty in
      (env,
       Some { ty = ty, id = Some ident,
              init = Some (CIExpr { expr = compileExpr expr }) },
       [])


  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem compileTops (env: CompileCEnv) (accTop: [CTop]) (accInit: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->
    match body with TmLam _ then
      match compileFun env ident tyBody body with (env, fun) then
        compileTops env (snoc accTop fun) accInit inexpr
      else never
    else
      match compileLet env ident body with (env, def, init) then
        -- We need to specially handle direct initialization, since most things
        -- are not allowed at top-level.
        let t = (def, init) in
        match t with (Some ({ init = Some definit } & def), _) then
          match definit with CIExpr { expr = expr } then
            let def = CTDef { def with init = None () } in
            let definit = CSExpr { expr = CEBinOp {
              op = COAssign {}, lhs = CEVar { id = ident }, rhs = expr } }
            in
            let accInit = join [accInit, [definit], init] in
            compileTops env (snoc accTop def) accInit inexpr
          else match definit with _ then
            error "CIList initializer, TODO?"
          else never

        else
          let accTop =
            match def with Some def then snoc accTop (CTDef def) else accTop in
          let accInit = concat accInit init in
          compileTops env accTop accInit inexpr

      else never

  | TmRecLets { bindings = bindings, inexpr = inexpr } ->
    let f = lam env. lam binding.
      match binding with { ident = ident, tyBody = tyBody, body = body } then
        compileFun env ident tyBody body
      else never
    in
    let g = lam fun.
      match fun with CTFun { ret = ret, id = id, params = params, body = body }
      then
        let params = map (lam t. t.0) params in
        CTDef { ty = CTyFun { ret = ret, params = params }, id = Some id,
               init = None () }
      else never
    in
    match mapAccumL f env bindings with (env, funs) then
      let decls = map g funs in
      compileTops env (join [accTop, decls, funs]) accInit inexpr
    else never

  -- Set up initialization code (for use, e.g., in a main function)
  | ( TmVar _ | TmLam _ | TmApp _ | TmConst _
    | TmSeq _ | TmRecord _ | TmRecordUpdate _
    | TmType _ | TmConDef _ | TmConApp _
    | TmMatch _ | TmUtest _ | TmNever _) & rest ->
    match compileStmts env { name = None () } accInit rest
    with (env, accInit) then
      (accTop, accInit)
    else never


  ------------------
  -- C STATEMENTS --
  ------------------

  sem compileStmts
    (env: CompileCEnv) (final: { name: Option Name }) (acc: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->
    match compileLet env ident body with (env, def, init) then
      let acc = match def with Some def then snoc acc (CSDef def) else acc in
      let acc = concat acc init in
      compileStmts env final acc inexpr
    else never

  | TmNever _ -> (env, snoc acc (CSNop {}))

  -- Return result of `compileExpr` (use `final` to decide between return and
  -- assign)
  | ( TmVar { ty = ty } | TmApp { ty = ty } | TmLam { ty = ty }
    | TmRecLets { ty = ty } | TmConst { ty = ty } | TmSeq { ty = ty }
    | TmRecord { ty = ty } | TmRecordUpdate { ty = ty } | TmType { ty = ty }
    | TmConDef { ty = ty } | TmConApp { ty = ty } | TmMatch { ty = ty }
    | TmUtest { ty = ty } ) & stmt ->
    match final with { name = name } then
      if _isUnitTy ty then
        match stmt with TmVar _ then (env, acc)
        else (env, snoc acc (CSExpr { expr = compileExpr stmt }))
      else match name with Some ident then
        (env,
         snoc acc
          (CSExpr {
            expr = CEBinOp { op = COAssign {},
                             lhs = CEVar { id = ident },
                             rhs = compileExpr stmt } }))
      else match name with None () then
        (env, snoc acc (CSRet { val = Some (compileExpr stmt) }))
      else never
    else never

  -------------------
  -- C EXPRESSIONS --
  -------------------

  -- Only a subset of constants can be compiled
  sem compileOp (args: [CExpr]) =

  -- Binary operators
  | CAddi _
  | CAddf _ -> CEBinOp { op = COAdd {}, lhs = head args, rhs = last args }
  | CSubi _
  | CSubf _ -> CEBinOp { op = COSub {}, lhs = head args, rhs = last args }
  | CMuli _
  | CMulf _ -> CEBinOp { op = COMul {}, lhs = head args, rhs = last args }
  | CDivf _ -> CEBinOp { op = CODiv {}, lhs = head args, rhs = last args }
  | CEqi _
  | CEqf _ -> CEBinOp { op = COEq {}, lhs = head args, rhs = last args }
  | CLti _
  | CLtf _ -> CEBinOp { op = COLt {}, lhs = head args, rhs = last args }

  -- Unary operators
  | CNegf _ -> CEUnOp { op = CONeg {}, arg = head args }

  -- Custom intrinsics
  | CPrint _ ->
    CEApp { fun = _printf, args = [CEString { s = "%s" }, head args] }


  sem compileExpr =

  | TmVar { ty = ty, ident = ident } ->
    if _isUnitTy ty then error "Unit type var in compileExpr"
    else CEVar { id = ident }

  | TmApp _ & app ->
    recursive let rec: [Expr] -> Expr -> (Expr, [Expr]) = lam acc. lam t.
      match t with TmApp { lhs = lhs, rhs = rhs } then
        if _isUnitTy (ty rhs) then rec acc lhs
        else rec (cons rhs acc) lhs
      else (t, acc)
    in
    match rec [] app with (fun, args) then
      -- Function calls
      match fun with TmVar { ident = ident } then
        CEApp { fun = ident, args = map compileExpr args }

      -- Intrinsics
      else match fun with TmConst { val = val } then
        let args = map compileExpr args in
        compileOp args val

      else error "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam _ -> error "Anonymous function in compileExpr."

  | TmRecord { bindings = bindings } ->
    if mapIsEmpty bindings then CEInt { i = 0 }
    else error "ERROR: Records cannot be handled in compileExpr."

  -- Should not occur after ANF.
  | TmRecordUpdate _ | TmLet _
  | TmRecLets _ | TmType _ | TmConDef _
  | TmConApp _ | TmMatch _ | TmUtest _
  | TmSeq _ ->
    error "ERROR: Term cannot be handled in compileExpr."

  -- Literals
  | TmConst { val = val } ->
    match val      with CInt   { val = val } then CEInt   { i = val }
    else match val with CFloat { val = val } then CEFloat { f = val }
    else match val with CChar  { val = val } then CEChar  { c = val }
    else match val with CBool  { val = val } then
      let val = match val with true then 1 else 0 in
      CEInt { i = val }
    else error "Unsupported literal"

  -- Should not occur?
  | TmNever _ -> error "Never term found in compileExpr"

end

lang MExprCCompileGCC = MExprCCompile + CPrettyPrint

  sem allocStruct (ty: Type) =
  | name ->
    match ty with CTyVar { id = tyName } then {
      ty = ty,
      id = Some name,
      init = Some (
        CIExpr {
          expr = CEApp {
            fun = _malloc,
            args = [
              CESizeOfType { ty = CTyStruct { id = Some tyName, mem = None ()}}
            ]
          }
        }
      )
    }
    else error "Not a CTyVar in allocStruct"

  sem free =
  | name -> error "TODO"

  sem printCompiledCProg =
  | cprog -> printCProg _compilerNames cprog

  sem compileWithMain (typeEnv: [(Name,Type)]) =
  | prog ->
    match compile typeEnv prog with (types, tops, inits) then
      let mainTy = CTyFun {
        ret = CTyInt {},
        params = [
          CTyInt {},
          CTyArray { ty = CTyPtr { ty = CTyChar {} }, size = None () }] }
      in
      let main = _funWithType mainTy _main [_argc, _argv] inits in
      CPProg { includes = _includes, tops = join [types, tops, [main]] }
    else never

end

-----------
-- TESTS --
-----------

lang Test =
  MExprCCompileGCC + MExprPrettyPrint + MExprTypeAnnot + MExprANF +
  MExprSym + BootParser + MExprTypeLift

mexpr
use Test in

let compile: Expr -> CProg = lam prog.

  -- Symbolize with empty environment
  let prog = symbolizeExpr symEnvEmpty prog in

  -- Type annotate
  let prog = typeAnnot prog in

  -- ANF transformation
  let prog = normalizeTerm prog in

  -- Type lift
  match typeLift prog with (env, prog) then

    -- Run C compiler
    let cprog = compileWithMain env prog in

    cprog

  else never
in

let testCompile: Expr -> String = lam expr. printCompiledCProg (compile expr) in

let simpleLet = bindall_ [
  ulet_ "x" (int_ 1),
  int_ 0
] in
utest testCompile simpleLet with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "int x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = 1);",
  "  return 0;",
  "}"
] in

let simpleFun = bindall_ [
  let_ "foo" (tyarrows_ [tyint_, tyint_, tyint_])
    (ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b")))),
  ulet_ "x" (appf2_ (var_ "foo") (int_ 1) (int_ 2)),
  int_ 0
] in
utest testCompile simpleFun with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "int foo(int a, int b) {",
  "  int t = (a + b);",
  "  return t;",
  "}",
  "int x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = (foo(1, 2)));",
  "  return 0;",
  "}"
] in

let constants = bindall_ [
  let_ "foo" (tyarrows_ [tyunit_, tyunit_])
    (ulam_ "a" (bindall_ [
      ulet_ "t" (addi_ (int_ 1) (int_ 2)),
      ulet_ "t" (addf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (muli_ (int_ 1) (int_ 2)),
      ulet_ "t" (mulf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (divf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (eqi_ (int_ 1) (int_ 2)),
      ulet_ "t" (eqf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (lti_ (int_ 1) (int_ 2)),
      ulet_ "t" (ltf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (negf_ (float_ 1.)),
      (print_ (str_ "Hello, world!"))
    ])),
  int_ 0
] in
utest testCompile constants with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "void foo() {",
  "  int t = (1 + 2);",
  "  double t1 = (1.0e-0 + 2.0e+0);",
  "  int t2 = (1 * 2);",
  "  double t3 = (1.0e-0 * 2.0e+0);",
  "  double t4 = (1.0e-0 / 2.0e+0);",
  "  char t5 = (1 == 2);",
  "  char t6 = (1.0e-0 == 2.0e+0);",
  "  char t7 = (1 < 2);",
  "  char t8 = (1.0e-0 < 2.0e+0);",
  "  double t9 = (-1.0e-0);",
  "  char (*t10) = \"Hello, world!\";",
  "  (printf(\"%s\", t10));",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] in

let factorial = bindall_ [
  reclet_ "factorial" (tyarrow_ tyint_ tyint_)
    (lam_ "n" tyint_
      (if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n")
          (app_ (var_ "factorial")
            (subi_ (var_ "n") (int_ 1)))))),
   int_ 0
] in
utest testCompile factorial with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "int factorial(int);",
  "int factorial(int n) {",
  "  char t = (n == 0);",
  "  int t1;",
  "  if ((t == 1)) {",
  "    (t1 = 1);",
  "  } else {",
  "    int t2 = (n - 1);",
  "    int t3 = (factorial(t2));",
  "    int t4 = (n * t3);",
  "    (t1 = t4);",
  "  }",
  "  return t1;",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

-- Mutually recursive odd and even functions
let oddEven = bindall_ [
  reclets_ [
    ("odd", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (if_ (eqi_ (var_ "x") (int_ 1))
         true_
         (if_ (lti_ (var_ "x") (int_ 1))
           false_
           (app_ (var_ "even")
             (subi_ (var_ "x") (int_ 1)))))),

    ("even", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (if_ (eqi_ (var_ "x") (int_ 0))
          true_
          (if_ (lti_ (var_ "x") (int_ 0))
            false_
            (app_ (var_ "odd")
              (subi_ (var_ "x") (int_ 1))))))
  ],
  int_ 0
] in
utest testCompile oddEven with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "char odd(int);",
  "char even(int);",
  "char odd(int x) {",
  "  char t = (x == 1);",
  "  char t1;",
  "  if ((t == 1)) {",
  "    (t1 = 1);",
  "  } else {",
  "    char t2 = (x < 1);",
  "    char t3;",
  "    if ((t2 == 1)) {",
  "      (t3 = 0);",
  "    } else {",
  "      int t4 = (x - 1);",
  "      char t5 = (even(t4));",
  "      (t3 = t5);",
  "    }",
  "    (t1 = t3);",
  "  }",
  "  return t1;",
  "}",
  "char even(int x1) {",
  "  char t6 = (x1 == 0);",
  "  char t7;",
  "  if ((t6 == 1)) {",
  "    (t7 = 1);",
  "  } else {",
  "    char t8 = (x1 < 0);",
  "    char t9;",
  "    if ((t8 == 1)) {",
  "      (t9 = 0);",
  "    } else {",
  "      int t10 = (x1 - 1);",
  "      char t11 = (odd(t10));",
  "      (t9 = t11);",
  "    }",
  "    (t7 = t9);",
  "  }",
  "  return t7;",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

let typedefs = bindall_ [

  type_ "Tree" (tyvariant_ []),
  type_ "Integer" tyint_,
  type_ "MyRec" (tyrecord_ [("k", (tyvar_ "Integer"))]),
  type_ "MyRec2" (tyrecord_ [("k", (tyvar_ "MyRec")), ("t", (tyvar_ "Tree"))]),
  type_ "Integer2" (tyvar_ "Integer"),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", (tyvar_ "Integer2"))]) (tyvar_ "Tree")),
  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tyvar_ "Tree")), ("r", (tyvar_ "Tree"))])
    (tyvar_ "Tree")),

  int_ 0
] in
utest testCompile typedefs with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "typedef struct Tree (*Tree);",
  "typedef int Integer;",
  "typedef struct Rec {Integer k;} (*Rec);",
  "typedef Rec MyRec;",
  "typedef struct Rec1 {MyRec k; Tree t;} (*Rec1);",
  "typedef Rec1 MyRec2;",
  "typedef Integer Integer2;",
  "typedef struct Rec2 {Integer2 v;} (*Rec2);",
  "typedef struct Rec3 {int v; Tree l; Tree r;} (*Rec3);",
  "struct Tree {enum {Leaf, Node} constr; union {Rec2 d0; Rec3 d1;};};",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

let leaf_ = lam v.
  conapp_ "Leaf" (record_ [("v", int_ v)]) in

let node_ = lam v. lam left. lam right.
  conapp_ "Node" (record_ [("v", int_ v), ("l", left), ("r", right)]) in

let trees = bindall_ [

  type_ "Tree" (tyvariant_ []),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", tyint_)]) (tyvar_ "Tree")),

  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tyvar_ "Tree")), ("r", (tyvar_ "Tree"))])
    (tyvar_ "Tree")),

  ulet_ "tree"
    (node_ 1 (node_ 2 (leaf_ 3) (leaf_ 4)) (node_ 5 (leaf_ 6) (leaf_ 7))),

  reclet_
    "treeRec" (tyarrow_ (tyvar_ "Tree") tyint_)
    (lam_ "t" (tyvar_ "Tree")
       (match_ (var_ "t") (pcon_ "Node" (prec_ [
           ("v", pvar_ "v"),
           ("l", pvar_ "l"),
           ("r", pvar_ "r")
         ]))
         (addi_ (addi_ (var_ "v") (app_ (var_ "treeRec") (var_ "l")))
            (app_ (var_ "treeRec") (var_ "r")))
         (match_ (var_ "t") (pcon_ "Leaf" (prec_ [("v", pvar_ "v")]))
            (var_ "v") never_))
      ),

  ulet_ "sum" (app_ (var_ "treeRec") (var_ "tree")),

  int_ 0
] in

utest testCompile trees with strJoin "\n" [
  "#include <stdio.h>",
  "#include <stdlib.h>",
  "typedef struct Tree (*Tree);",
  "typedef struct Rec {int v;} (*Rec);",
  "typedef struct Rec1 {int v; Tree l; Tree r;} (*Rec1);",
  "struct Tree {enum {Leaf, Node} constr; union {Rec d0; Rec1 d1;};};",
  "Rec t;",
  "Tree t1;",
  "Rec t2;",
  "Tree t3;",
  "Rec1 t4;",
  "Tree t5;",
  "Rec t6;",
  "Tree t7;",
  "Rec t8;",
  "Tree t9;",
  "Rec1 t10;",
  "Tree t11;",
  "Rec1 t12;",
  "Tree tree;",
  "int treeRec(Tree);",
  "int treeRec(Tree t13) {",
  "  int t14;",
  "  if (((t13->constr) == Node)) {",
  "    int v = ((t13->d1)->v);",
  "    Tree l = ((t13->d1)->l);",
  "    Tree r = ((t13->d1)->r);",
  "    int t15 = (treeRec(l));",
  "    int t16 = (v + t15);",
  "    int t17 = (treeRec(r));",
  "    int t18 = (t16 + t17);",
  "    (t14 = t18);",
  "  } else {",
  "    int t19;",
  "    if (((t13->constr) == Leaf)) {",
  "      int v1 = ((t13->d0)->v);",
  "      (t19 = v1);",
  "    } else {",
  "      ;",
  "    }",
  "    (t14 = t19);",
  "  }",
  "  return t14;",
  "}",
  "int sum;",
  "int main(int argc, char (*argv[])) {",
  "  (t = (malloc((sizeof(struct Rec)))));",
  "  ((t->v) = 7);",
  "  (t1 = (malloc((sizeof(struct Tree)))));",
  "  ((t1->constr) = Leaf);",
  "  ((t1->d0) = t);",
  "  (t2 = (malloc((sizeof(struct Rec)))));",
  "  ((t2->v) = 6);",
  "  (t3 = (malloc((sizeof(struct Tree)))));",
  "  ((t3->constr) = Leaf);",
  "  ((t3->d0) = t2);",
  "  (t4 = (malloc((sizeof(struct Rec1)))));",
  "  ((t4->v) = 5);",
  "  ((t4->l) = t3);",
  "  ((t4->r) = t1);",
  "  (t5 = (malloc((sizeof(struct Tree)))));",
  "  ((t5->constr) = Node);",
  "  ((t5->d1) = t4);",
  "  (t6 = (malloc((sizeof(struct Rec)))));",
  "  ((t6->v) = 4);",
  "  (t7 = (malloc((sizeof(struct Tree)))));",
  "  ((t7->constr) = Leaf);",
  "  ((t7->d0) = t6);",
  "  (t8 = (malloc((sizeof(struct Rec)))));",
  "  ((t8->v) = 3);",
  "  (t9 = (malloc((sizeof(struct Tree)))));",
  "  ((t9->constr) = Leaf);",
  "  ((t9->d0) = t8);",
  "  (t10 = (malloc((sizeof(struct Rec1)))));",
  "  ((t10->v) = 2);",
  "  ((t10->l) = t9);",
  "  ((t10->r) = t7);",
  "  (t11 = (malloc((sizeof(struct Tree)))));",
  "  ((t11->constr) = Node);",
  "  ((t11->d1) = t10);",
  "  (t12 = (malloc((sizeof(struct Rec1)))));",
  "  ((t12->v) = 1);",
  "  ((t12->l) = t11);",
  "  ((t12->r) = t5);",
  "  (tree = (malloc((sizeof(struct Tree)))));",
  "  ((tree->constr) = Node);",
  "  ((tree->d1) = t12);",
  "  (sum = (treeRec(tree)));",
  "  return 0;",
  "}"
] using eqString in

()
