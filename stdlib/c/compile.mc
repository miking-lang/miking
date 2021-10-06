-- Compiles a subset of MExpr programs to C.
-- * Anonymous functions are not supported, except when bound to variables at
-- top-level.
-- * Top-level MExpr variables (including functions) are compiled to global C
-- data.
-- * There is no garbage collection.
-- * Any top-level code besides functions and data declarations are returned as
-- a list of C statements. Usually, these statements should be
-- put in a C `main` function or similar.
--
-- TODO Add an explicit TmString to Expr (transform in separate pass) to make pattern matching easier in this compilation


include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/type-lift.mc"
include "mexpr/builtin.mc"
include "mexpr/boot-parser.mc"

include "name.mc"
include "map.mc"
include "set.mc"

include "ast.mc"
include "pprint.mc"

-- Externals (these should be automatically parsed eventually)
include "ext/math-ext.ext-c.mc"

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Check for unit type
let _isUnitTy = use RecordTypeAst in lam ty.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields
  else false

-- Unwrap type until something useful falls out
recursive let _unwrapType = use ConTypeAst in
    lam tyEnv: AssocSeq Name Type. lam ty: Type.
    match ty with TyCon { ident = ident } then
      match assocSeqLookup { eq = nameEq } ident tyEnv with Some ty then
        _unwrapType tyEnv ty
      else infoErrorExit (infoTy ty) "TyCon not defined in environment"
    else ty
end

-- Unwrap type aliases
recursive let _unwrapTypeAlias = use ConTypeAst in
    lam tyEnv: AssocSeq Name Type. lam ty: Type.
    match ty with TyCon { ident = ident } then
      let res = assocSeqLookup { eq = nameEq } ident tyEnv in
      match res with Some ((TyCon _) & ty) then _unwrapTypeAlias tyEnv ty
      else match res with Some _ then ty
      else infoErrorExit (infoTy ty) "TyCon not defined in environment"
    else infoErrorExit (infoTy ty) "Not a tyVar in _unwrapTypeAlias"
end

-- C assignment shorthand
let _assign: CExpr -> CExpr -> CExpr = use CAst in
  lam lhs. lam rhs.
    CEBinOp { op = COAssign {}, lhs = lhs, rhs = rhs }


----------------------------------------
-- COMPILER DEFINITIONS AND EXTERNALS --
----------------------------------------

type ExtInfo = { ident: String, header: String }

let externalsMap: Map String ExtInfo = foldl1 mapUnion [
  mathExtMap
]

let externalNames =
  map nameNoSym
    (mapFoldWithKey (lam acc. lam. lam v. cons v.ident acc) [] externalsMap)

let externalIncludes =
  setToSeq
    (mapFoldWithKey (lam acc. lam. lam v. setInsert v.header acc)
       (setEmpty cmpString) externalsMap)

-- Customizable set of includes
let cIncludes = concat [
  "<stdio.h>"
] externalIncludes

-- Names used in the compiler for intrinsics
let _printf = nameSym "printf"

-- C names that must be pretty printed using their exact string
let cCompilerNames: [Name] = concat [
  _printf
] externalNames

-- Various names used when defining C structs
let _constrKey = nameNoSym "constr"
let _seqKey = nameNoSym "seq"
let _seqLenKey = nameNoSym "len"

-- Used in compileStmt and compileStmts
type Result
con Ident : Name -> Res
con Return : () -> Res
con None : () -> Res

--------------------------
-- COMPILER ENVIRONMENT --
--------------------------

type CompileCEnv = {

  -- Type names translating to C structs
  structTypes: [Name],

  -- The initial type environment produced by type lifting
  -- TODO(dlunde,2021-05-17): I want CompileCEnv to be visible across the whole
  -- MExprCCompile fragment, which is why it is defined here. A problem,
  -- however, is that Type is not bound outside the fragment. A solution to
  -- this would be to define CompileCEnv within the fragment MExprCCompile
  -- itself, with the requirement that it is visible across all semantic
  -- functions and types defined with syn. This is currently impossible.
  typeEnv: [(Name,Type)],

  externals: Map Name Name
}

let compileCEnvEmpty =
  { structTypes = [], typeEnv = [], externals = mapEmpty nameCmp }

----------------------------------
-- MEXPR -> C COMPILER FRAGMENT --
----------------------------------

lang MExprCCompile = MExprAst + CAst

  sem alloc (ty: Type) =
  -- Intentionally left blank

  sem free =
  -- Intentionally left blank

  -- Entry point
  sem compile (typeEnv: [(Name,Type)]) =
  | prog ->

    let structTypes: [Name] = foldl (lam acc. lam t: (Name,Type).
      if isStructType t.1 then snoc acc t.0 else acc
    ) [] typeEnv in

    let externals = collectExternals (mapEmpty nameCmp) prog in

    let env = {{{ compileCEnvEmpty
      with structTypes = structTypes }
      with typeEnv = typeEnv }
      with externals = externals }
    in

    let decls: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyDecls acc t.0 t.1
    ) [] typeEnv in

    let defs: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyDefs env acc t.0 t.1
    ) [] typeEnv in

    let postDefs: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyPostDefs env acc t.0 t.1
    ) [] typeEnv in

    match compileTops env [] [] prog with (tops, inits) then

    let retTy: CType = compileType env (tyTm prog) in

    (env, join [decls, defs, postDefs], tops, inits, retTy)

    else never

  sem collectExternals (acc: Map Name Name) =
  | TmExt t ->
    let str = nameGetStr t.ident in
    match mapLookup str externalsMap with Some e then
      mapInsert t.ident (nameNoSym e.ident) acc
    else infoErrorExit (t.info) "Unsupported external"
  | expr -> sfold_Expr_Expr collectExternals acc expr

  sem isStructType =
  | TyVariant _ -> true
  | TyRecord _ -> true
  | _ -> false

  -- Generate declarations for all variant types (required because of recursion).
  sem genTyDecls (acc: [CTop]) (name: Name) =
  | TyVariant _ ->
    let decl = CTDef {
      ty = CTyStruct { id = Some name, mem = None () },
      id = None (),
      init = None ()
    } in
    cons decl acc
  | _ -> acc

  -- Generate type definitions.
  sem genTyDefs (env: CompileCEnv) (acc: [CTop]) (name: Name) =
  | TyVariant _ -> acc -- These are handled by genTyPostDefs instead
  | TyRecord { fields = fields } ->
    let fieldsLs: [(CType,Name)] =
      mapFoldWithKey (lam acc. lam k. lam ty.
        let ty = compileType env ty in
        snoc acc (ty, Some (nameNoSym (sidToString k)))) [] fields in
    let def = CTDef {
      ty = CTyStruct { id = Some name, mem = Some fieldsLs },
      id = None (),
      init = None ()
    } in
    cons def acc
  | TySeq { ty = ty } ->
    let ty = compileType env ty in
    let fields = [
      (ty, _seqKey),
      (CTyInt {}, _seqLenKey)
    ] in
    let def = CTDef {
      ty = CTyStruct { id = Some name, mem = fields },
      id = None (),
      init = None ()
    } in
    cons def acc
  | ty ->
    let def = CTTyDef { ty = compileType env ty, id = name } in
    cons def acc

  -- Generate variant definitions.
  sem genTyPostDefs
    (env: CompileCEnv) (acc: [CTop]) (name: Name) =
  | TyVariant { constrs = constrs } ->
      let constrLs: [(Name, CType)] =
        mapFoldWithKey (lam acc. lam name. lam ty.
          let ty = compileType env ty in
            snoc acc (name, ty)) [] constrs in
      let nameEnum = nameSym "constrs" in
      let enum = CTDef {
        ty = CTyEnum {
          id = Some nameEnum,
          mem = Some (map (lam t. t.0) constrLs)
        },
        id = None (), init = None ()
      } in
      let def = CTDef {
        ty = CTyStruct {
          id = Some name,
          mem = Some [
            (CTyEnum { id = Some nameEnum, mem = None () }, Some _constrKey),
            (CTyUnion {
               id = None (),
               mem = Some (map
                 (lam t: (Name,CType). (t.1, Some t.0)) constrLs)
             }, None ())
          ] },
        id = None (), init = None ()
      }
      in
      concat [enum,def] acc
  | _ -> acc



  -------------
  -- C TYPES --
  -------------

  sem compileType (env: CompileCEnv) =

  | TyInt _ -> CTyInt {}
  | TyFloat _ -> CTyDouble {}
  | TyBool _
  | TyChar _ -> CTyChar {}

  | TyArrow _ & ty ->
    infoErrorExit (infoTy ty) "TyArrow currently not supported"
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

  | TyRecord { fields = fields } & ty ->
    if mapIsEmpty fields then CTyVoid {}
    else
      infoErrorExit (infoTy ty)
        "TyRecord should not occur in compileType. Did you run type lift?"

  | TyCon { ident = ident } & ty ->
    -- Safety precaution, it seems this may already be handled by type lifting
    let unwrapped =
      match _unwrapTypeAlias env.typeEnv ty with TyCon { ident = i } then i
      else infoErrorExit (infoTy ty) "Impossible in compileType"
    in
    match find (nameEq unwrapped) env.structTypes with Some _ then
      CTyPtr { ty = CTyStruct { id = Some ident, mem = None() } }
    else CTyVar { id = ident }

  | TyUnknown _ & ty -> infoErrorExit (infoTy ty) "Unknown type in compileType"

  | TySeq { ty = TyChar _ } -> CTyPtr { ty = CTyChar {} }

  | TyVariant _ & ty ->
    infoErrorExit (infoTy ty)
      "TyVariant should not occur in compileType. Did you run type lift?"

  | TySeq _ & ty ->
    infoErrorExit (infoTy ty)
      "TySeq should not occur in compileType. Did you run type lift?"

  | TyApp _ & ty -> infoErrorExit (infoTy ty) "Type not currently supported"


  -----------------------
  -- COMPILE FUNCTIONS --
  -----------------------

  -- Translate a sequence of lambdas to a C function. Takes an explicit type as
  -- argument, because the lambdas do not explicitly give the return type,
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
          else infoErrorExit (infoTy ty) "Incorrect type in compileFun"
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
          infoErrorExit (infoTy ty) "Number of parameters in compileFun does not match."
        else
          match map (compileType env) paramTypes with paramTypes then
            let params = zipWith (lam t. lam id. (t, id)) paramTypes params in
            match (compileType env) retType with ret then
              match compileStmts env (Return ()) [] body
              with (env, body) then
                (env, CTFun { ret = ret, id = id, params = params, body = body })
              else never
            else never
          else never
      else never
    else never

  | t -> infoErrorExit (infoTm t) "Non-lambda supplied to compileFun"


  ----------------------
  -- COMPILE PATTERNS --
  ----------------------

  sem compilePat (env: CompileCEnv)
    (pres: [CStmt]) (conds: [CExpr]) (defs: [CStmt])
    (target: CExpr) (ty: Type) =

  | PatNamed { ident = PName ident } ->
    let def = CSDef {
      ty = compileType env ty,
      id = Some ident,
      init = Some (CIExpr { expr = target })
    } in
    ( pres, conds, snoc defs def )

  | PatNamed { ident = PWildcard _ } -> (pres, conds, defs)

  | PatBool { val = val } ->
    ( pres,
      snoc conds (CEBinOp {
        op = COEq {},
        lhs = target,
        rhs = let val = match val with true then 1 else 0 in CEInt { i = val }
      }),
      defs )

  | PatRecord { bindings = bindings } ->
    match env with { typeEnv = typeEnv } then
      let f = lam acc. lam sid. lam subpat.
        match acc with (pres, conds, defs) then
          match _unwrapType typeEnv ty with TyRecord { fields = fields } then
            match mapLookup sid fields with Some ty then
              let label = sidToString sid in
              let namePre = nameSym "preMatch" in
              let pre = CSDef {
                ty = compileType env ty,
                id = Some namePre,
                init = Some (CIExpr {
                  expr = CEArrow { lhs = target, id = nameNoSym label }
                })
              } in
              compilePat env (snoc pres pre)
                conds defs (CEVar { id = namePre }) ty subpat
            else error "Label does not match between PatRecord and TyRecord"
          else error "Type not TyCon for PatRecord in compilePat"
        else never
      in
      mapFoldWithKey f (pres, conds, defs) bindings
    else never

  | PatCon { ident = ident, subpat = subpat } ->
    match env with { typeEnv = typeEnv } then
      match _unwrapType typeEnv ty with TyVariant { constrs = constrs } then
        match mapLookup ident constrs with Some ty then
          let namePre = nameSym "preMatch" in
          let pre = CSDef {
            ty = compileType env ty,
            id = Some namePre,
            init = Some (CIExpr {
              expr = CEArrow { lhs = target, id = ident }
            })
          } in
          compilePat env (snoc pres pre) (snoc conds (CEBinOp {
              op = COEq {},
              lhs = CEArrow { lhs = target, id = _constrKey },
              rhs = CEVar { id = ident }
            }))
            defs (CEVar { id = namePre }) ty subpat
        else error "Invalid constructor in compilePat"
      else error "Not a TyVariant for PatCon in compilePat"
    else never
  | pat -> infoErrorExit (infoPat pat) "Pattern not supported"

  -------------------
  -- C ALLOCATIONS --
  -------------------

  -- Compiles allocation/definition and initialization of composite data types
  sem compileAlloc (env: CompileCEnv) (name: Option Name) =

  | TmConApp { ident = constrIdent, body = body, ty = ty } & t ->
    let n = match name with Some name then name else nameSym "alloc" in
    let def = alloc n (compileType env ty) in
    let init = [
      -- Set constructor tag
      CSExpr {
        expr = _assign (CEArrow { lhs = CEVar { id = n }, id = _constrKey })
          (CEVar { id = constrIdent })
      },
      -- Set data
      CSExpr {
        expr = _assign (CEArrow { lhs = CEVar { id = n }, id = constrIdent })
          (compileExpr env body)
      }
    ] in
    (env, def, init, n)

  -- TmRecord: allocate and create new struct, unless it is an empty record (in
  -- which case it is compiled to the integer 0)
  | TmRecord { ty = ty, bindings = bindings } & t ->
    if mapIsEmpty bindings then
      infoErrorExit (infoTm t) "Empty bindings in TmRecord in compileAlloc"
    else
      let n = match name with Some name then name else nameSym "alloc" in
      let def = alloc n (compileType env ty) in
      let init = mapMapWithKey (lam sid. lam expr.
        CSExpr {
          expr = _assign
            (CEArrow {
              lhs = CEVar { id = n }, id = nameNoSym (sidToString sid)
            })
            (compileExpr env expr)
        }
      ) bindings in
      (env, def, mapValues init, n)

  -- | TmSeq {tms : [Expr], ty: Type, info: Info} ->
  | TmSeq {tms = tms, ty = ty} ->

  -----------------
  -- C TOP-LEVEL --
  -----------------

  sem compileTops (env: CompileCEnv) (accTop: [CTop]) (accInit: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->

    -- Functions
    match body with TmLam _ then
      match compileFun env ident tyBody body with (env, fun) then
        compileTops env (snoc accTop fun) accInit inexpr
      else never

    -- Optimize direct allocations
    else match body with TmConApp _ | TmRecord _ then
      match compileAlloc env (Some ident) body with (env, def, init, n) then
        let accTop = concat accTop (map (lam d. CTDef d) def) in
        let accInit = concat accInit init in
        compileTops env accTop accInit inexpr
      else never

    -- Other lets
    else
      let iu = _isUnitTy tyBody in
      let def =
        if iu then []
        else
          let ty = compileType env tyBody in
          [CTDef { ty = ty, id = Some ident, init = None () }]
      in
      let lres = if iu then None () else Ident ident in
      match compileStmt env lres body with (env, stmts) then
        let accTop = concat accTop def in
        let accInit = concat accInit stmts in
        compileTops env accTop accInit inexpr
      else never

  | TmRecLets { bindings = bindings, inexpr = inexpr } ->
    let f = lam env. lam binding: RecLetBinding.
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
      let decls = if leqi (length funs) 1 then [] else map g funs in
      compileTops env (join [accTop, decls, funs]) accInit inexpr
    else never

  -- Ignore externals (handled elsewhere)
  | TmExt { inexpr = inexpr } -> compileTops env accTop accInit inexpr

  -- Set up initialization code (for use, e.g., in a main function)
  | rest ->
    match compileStmts env (Return ()) accInit rest
    with (env, accInit) then (accTop, accInit)
    else never


  ------------------
  -- C STATEMENTS --
  ------------------

  -- Compile a single C statement, and take action according to res.
  sem compileStmt (env: CompileCEnv) (res: Result) =

  -- TmMatch: Compile to if-statement
  | TmMatch { target = target, pat = pat, thn = thn, els = els } & t ->

    let ctarget = compileExpr env target in

    -- Compile branches
    match compileStmts env res [] thn with (env, thn) then
      match compileStmts env res [] els with (env, els) then

        -- Generate conditions corresponding to pat, and add pattern bindings
        -- to start of thn
        match compilePat env [] [] [] ctarget (tyTm target) pat
        with (pres, conds, defs) then

          let thn = concat defs thn in

          let stmts =
            if null conds then thn
            else
              -- Compute joint condition
              let cond = foldr1 (lam cond. lam acc.
                  CEBinOp { op = COAnd {}, lhs = cond, rhs = acc }
                ) conds in
              [CSIf { cond = cond, thn = thn, els = els }]
          in

          let stmts = concat pres stmts in

          (env, stmts)

        else never
      else never
    else never

  | TmSeq { tms = tms } & t ->
    let toChar = lam expr.
      match expr with TmConst { val = CChar { val = val } } then Some val
      else None ()
    in

    -- Special case of TmSeq: String literals
    match optionMapM toChar tms with Some str then
      let str = CEString { s = str } in
      (
        env,
        [
          match res with Ident id then
            CSExpr { expr =_assign (CEVar { id = id }) str }
          else match res with Return _ then CSRet { val = str }
          else
            infoErrorExit (t.info) "Type error, should have been caught previously"
        ]
      )

    -- General TmSeqs
    else error "TODO: TmSeq"

  | TmConApp { ident = constrIdent, body = body, ty = ty } & t ->
    match res with Ident id then
      -- TODO: This is WRONG. We MUST collect all allocations and put them on top of it's function somehow (should be easy)
      -- We can optimize this case and ignore the alloc, since what we are
      -- returning to (Ident id) has already been allocated
      match compileAlloc env (Some id) t with (env, _, init, n) then
        (env, init)
      else never
    else match res with Return _ then
      infoErrorExit (t.info) "Returning TmConApp is not allowed"
    else
      infoErrorExit (t.info) "Type error, should have been caught previously"

  | TmRecord { ty = ty, bindings = bindings } & t ->
    if mapIsEmpty bindings then
      match res with None _ | Return _ then (env, [CSNop {}])
      else infoErrorExit (t.info) "Binding of unit type is not allowed"
    else
      match res with Ident id then
        -- TODO: This is WRONG
        -- We can optimize this case and ignore the alloc, since what we are
        -- returning to (Ident id) has already been allocated
        match compileAlloc env (Some id) t with (env, _, init, n) then
          (env, init)
        else never
      else match res with Return _ then
        infoErrorExit (t.info) "Returning TmRecord is not allowed"
      else
        infoErrorExit (t.info) "Type error, should have been caught previously"

  | TmRecordUpdate _ -> error "TODO: TmRecordUpdate"

  -- Declare variable and call `compileExpr` on body.
  | expr ->

    match res with Return _ then
      if _isUnitTy (tyTm expr) then
        match expr with TmVar _ then (env, [])
        else (env, [CSExpr { expr = compileExpr env expr }])
      else (env, [CSRet { val = Some (compileExpr env expr) }])

    else match res with None _ then
      if _isUnitTy (tyTm expr) then
        match expr with TmVar _ then (env, [])
        else (env, [CSExpr { expr = compileExpr env expr }])
      else infoErrorExit (infoTm expr)
        "Type error, should have been caught previously"

    else match res with Ident id then
      (env, [CSExpr {
        expr = _assign (CEVar { id = id }) (compileExpr env expr)
      }])

    else never


  sem compileStmts (env: CompileCEnv) (res: Result) (acc: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->

    -- Optimize direct allocations
    match body with TmConApp _ | TmRecord _ then
      match compileAlloc env (Some ident) body with (env, def, init, n) then
        let acc = join [ acc, map (lam d. CSDef d) def, init ] in
        compileStmts env res acc inexpr
      else never

    else
      let iu = _isUnitTy tyBody in
      let def =
        if iu then []
        else
          let ty = compileType env tyBody in
          [CSDef { ty = ty, id = Some ident, init = None () }]
      in
      let lres = if iu then None () else Ident ident in
      match compileStmt env lres body with (env, stmts) then
        let acc = join [acc, def, stmts] in
        compileStmts env res acc inexpr
      else never

  | stmt ->
    match compileStmt env res stmt with (env, stmts) then
      (env, join [acc, stmts])
    else never

  | TmNever _ -> (env, snoc acc (CSNop {}))

  -- Ignore externals (handled elsewhere)
  | TmExt { inexpr = inexpr } -> compileStmts env res acc inexpr


  -------------------
  -- C EXPRESSIONS --
  -------------------

  -- Only a subset of constants can be compiled
  sem compileOp (t: Expr) (args: [CExpr]) =

  -- Binary operators
  | CAddi _
  | CAddf _ -> CEBinOp { op = COAdd {}, lhs = head args, rhs = last args }
  | CSubi _
  | CSubf _ -> CEBinOp { op = COSub {}, lhs = head args, rhs = last args }
  | CMuli _
  | CMulf _ -> CEBinOp { op = COMul {}, lhs = head args, rhs = last args }
  | CDivf _ -> CEBinOp { op = CODiv {}, lhs = head args, rhs = last args }
  | CEqi _
  | CEqf _  -> CEBinOp { op = COEq {},  lhs = head args, rhs = last args }
  | CLti _
  | CLtf _  -> CEBinOp { op = COLt {},  lhs = head args, rhs = last args }
  | CGti _
  | CGtf _  -> CEBinOp { op = COGt {},  lhs = head args, rhs = last args }
  | CLeqi _
  | CLeqf _ -> CEBinOp { op = COLe {},  lhs = head args, rhs = last args }
  | CGeqi _
  | CGeqf _ -> CEBinOp { op = COGe {},  lhs = head args, rhs = last args }
  | CNeqi _
  | CNeqf _ -> CEBinOp { op = CONeq {}, lhs = head args, rhs = last args }

  -- Unary operators
  | CNegf _
  | CNegi _ -> CEUnOp { op = CONeg {}, arg = head args }

  -- Not directly mapped to C operators
  | CPrint _ ->
    CEApp { fun = _printf, args = [CEString { s = "%s" }, head args] }
  | CInt2float _ -> CECast { ty = CTyDouble {}, rhs = head args }
  | CFloorfi _ -> CECast { ty = CTyInt {}, rhs = head args }

  | c -> dprint c; infoErrorExit (infoTm t) "Unsupported intrinsic in compileOp"


  sem compileExpr (env: CompileCEnv) =

  | TmVar { ty = ty, ident = ident } & t->
    if _isUnitTy ty then
      error "Unit type var in compileExpr"
    else match mapLookup ident env.externals with Some ext then
      CEVar { id = ext }
    else CEVar { id = ident }

  | TmApp _ & app ->
    recursive let rec: [Expr] -> Expr -> (Expr, [Expr]) = lam acc. lam t.
      match t with TmApp { lhs = lhs, rhs = rhs } then
        if _isUnitTy (tyTm rhs) then rec acc lhs
        else rec (cons rhs acc) lhs
      else (t, acc)
    in
    match rec [] app with (fun, args) then
      -- Function calls
      match fun with TmVar { ident = ident } then
        let ident =
          match mapLookup ident env.externals with Some ext then ext
          else ident
        in
        CEApp { fun = ident, args = map (compileExpr env) args }

      -- Intrinsics
      else match fun with TmConst { val = val } then
        let args = map (compileExpr env) args in
        compileOp fun args val

      else error "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam _ -> error "Anonymous function in compileExpr."

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    if mapIsEmpty bindings then CEInt { i = 0 }
    else error "ERROR: Records cannot be handled in compileExpr."

  -- Should not occur after ANF and type lifting.
  | TmRecordUpdate _ | TmLet _
  | TmRecLets _ | TmType _ | TmConDef _
  | TmConApp _ | TmMatch _ | TmUtest _
  | TmSeq _ | TmExt _ ->
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

  -- Should not occur
  | TmNever _ -> error "Never term found in compileExpr"

end

-------------------------
-- COMPILATION FOR GCC --
-------------------------

lang MExprCCompileGCC = MExprCCompile + CProgAst

  -- Name -> CType -> [{ ty: CType, id: Option Name, init: Option CInit }]
  sem alloc (name: Name) =
  | CTyPtr { ty = CTyStruct { id = Some ident, mem = None() } & ty } & ptrTy ->
    [
      -- Define name as pointer to allocated struct
      { ty = CTyArray { ty = ty, size = Some (CEInt { i = 1 }) }
      , id = Some name
      , init = None ()
      }
    ]
  | _ -> error "Incorrect type in alloc"

  sem free =
  | name -> error "free currently unused"

end

let _argc = nameSym "argc"
let _argv = nameSym "argv"
let _main = nameSym "main"

let cGccCompilerNames = concat cCompilerNames [
  _argc,
  _argv,
  _main
]

let compileGCC = use MExprCCompileGCC in
  lam typeEnv: [(Name,Type)].
  lam prog: Expr.

    match compile typeEnv prog with (env, types, tops, inits, _) then

      let mainTy = CTyFun {
        ret = CTyInt {},
        params = [
          CTyInt {},
          CTyArray { ty = CTyPtr { ty = CTyChar {} }, size = None () }] }
      in
      let funWithType = use CAst in
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
          else error "Non-function type given to funWithType"
      in
      let main = funWithType mainTy _main [_argc, _argv] inits in
      CPProg {
        includes = cIncludes,
        tops = join [types, tops, [main]]
      }

    else never

let printCompiledCProg = use CProgPrettyPrint in
  lam cprog: CProg. printCProg cGccCompilerNames cprog

-----------
-- TESTS --
-----------

lang Test =
  MExprCCompileGCC + MExprPrettyPrint + MExprTypeAnnot + MExprANF +
  MExprSym + BootParser + MExprTypeLiftUnOrderedRecords
  + SeqTypeNoStringTypeLift

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

  -- Remove redundant lets
  let prog = removeTypeAscription prog in

  -- Run C compiler
  let cprog = compileGCC env prog in

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
  "#include <math.h>",
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
  "#include <math.h>",
  "int foo(int a, int b) {",
  "  return (a + b);",
  "}",
  "int x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = foo(1, 2));",
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
  "#include <math.h>",
  "void foo() {",
  "  int t;",
  "  (t = (1 + 2));",
  "  double t1;",
  "  (t1 = (1. + 2.));",
  "  int t2;",
  "  (t2 = (1 * 2));",
  "  double t3;",
  "  (t3 = (1. * 2.));",
  "  double t4;",
  "  (t4 = (1. / 2.));",
  "  char t5;",
  "  (t5 = (1 == 2));",
  "  char t6;",
  "  (t6 = (1. == 2.));",
  "  char t7;",
  "  (t7 = (1 < 2));",
  "  char t8;",
  "  (t8 = (1. < 2.));",
  "  double t9;",
  "  (t9 = (-1.));",
  "  char (*t10);",
  "  (t10 = \"Hello, world!\");",
  "  printf(\"%s\", t10);",
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
  "#include <math.h>",
  "int factorial(int n) {",
  "  char t;",
  "  (t = (n == 0));",
  "  if ((t == 1)) {",
  "    return 1;",
  "  } else {",
  "    int t1;",
  "    (t1 = (n - 1));",
  "    int t2;",
  "    (t2 = factorial(t1));",
  "    return (n * t2);",
  "  }",
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
  "#include <math.h>",
  "char odd(int);",
  "char even(int);",
  "char odd(int x) {",
  "  char t;",
  "  (t = (x == 1));",
  "  if ((t == 1)) {",
  "    return 1;",
  "  } else {",
  "    char t1;",
  "    (t1 = (x < 1));",
  "    if ((t1 == 1)) {",
  "      return 0;",
  "    } else {",
  "      int t2;",
  "      (t2 = (x - 1));",
  "      return even(t2);",
  "    }",
  "  }",
  "}",
  "char even(int x1) {",
  "  char t3;",
  "  (t3 = (x1 == 0));",
  "  if ((t3 == 1)) {",
  "    return 1;",
  "  } else {",
  "    char t4;",
  "    (t4 = (x1 < 0));",
  "    if ((t4 == 1)) {",
  "      return 0;",
  "    } else {",
  "      int t5;",
  "      (t5 = (x1 - 1));",
  "      return odd(t5);",
  "    }",
  "  }",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

let typedefs = bindall_ [

  type_ "Tree" (tyvariant_ []),
  type_ "Integer" tyint_,
  type_ "MyRec" (tyrecord_ [("k", (tycon_ "Integer"))]),
  type_ "MyRec2" (tyrecord_ [("k", (tycon_ "MyRec")), ("t", (tycon_ "Tree"))]),
  type_ "Integer2" (tycon_ "Integer"),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", (tycon_ "Integer2"))]) (tycon_ "Tree")),
  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tycon_ "Tree")), ("r", (tycon_ "Tree"))])
    (tycon_ "Tree")),

  int_ 0
] in
utest testCompile typedefs with strJoin "\n" [
  "#include <stdio.h>",
  "#include <math.h>",
  "struct Tree;",
  "typedef int Integer;",
  "struct Rec {Integer k;};",
  "typedef struct Rec (*MyRec);",
  "struct Rec1 {struct MyRec (*k); struct Tree (*t);};",
  "typedef struct Rec1 (*MyRec2);",
  "typedef Integer Integer2;",
  "struct Rec2 {Integer2 v;};",
  "struct Rec3 {int v; struct Tree (*l); struct Tree (*r);};",
  "enum constrs {Leaf, Node};",
  "struct Tree {enum constrs constr; union {struct Rec2 (*Leaf); struct Rec3 (*Node);};};",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

-- Potentially tricky case with type aliases
let alias = bindall_ [
  type_ "MyRec" (tyrecord_ [("k", tyint_)]),
  let_ "myRec" (tycon_ "MyRec") (urecord_ [("k", int_ 0)]),
  int_ 0
] in
utest testCompile alias with strJoin "\n" [
  "#include <stdio.h>",
  "#include <math.h>",
  "struct Rec {int k;};",
  "typedef struct Rec (*MyRec);",
  "struct Rec myRec[1];",
  "int main(int argc, char (*argv[])) {",
  "  ((myRec->k) = 0);",
  "  return 0;",
  "}"
] using eqString in

-- Externals test
let ext = bindall_ [
  ext_ "externalLog" false (tyarrow_ tyfloat_ tyfloat_),
  let_ "x" (tyfloat_) (app_ (var_ "externalLog") (float_ 2.)),
  int_ 0
] in
utest testCompile ext with strJoin "\n" [
  "#include <stdio.h>",
  "#include <math.h>",
  "double x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = log(2.));",
  "  return 0;",
  "}"
] using eqString in

let leaf_ = lam v.
  conapp_ "Leaf" (urecord_ [("v", int_ v)]) in

let node_ = lam v. lam left. lam right.
  conapp_ "Node" (urecord_ [("v", int_ v), ("l", left), ("r", right)]) in

let trees = bindall_ [

  type_ "Tree" (tyvariant_ []),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", tyint_)]) (tycon_ "Tree")),

  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tycon_ "Tree")), ("r", (tycon_ "Tree"))])
    (tycon_ "Tree")),

  ulet_ "tree"
    (node_ 1 (node_ 2 (leaf_ 3) (leaf_ 4)) (node_ 5 (leaf_ 6) (leaf_ 7))),

  reclet_
    "treeRec" (tyarrow_ (tycon_ "Tree") tyint_)
    (lam_ "t" (tycon_ "Tree")
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
  "#include <math.h>",
  "struct Tree;",
  "struct Rec {int v;};",
  "struct Rec1 {int v; struct Tree (*l); struct Tree (*r);};",
  "enum constrs {Leaf, Node};",
  "struct Tree {enum constrs constr; union {struct Rec (*Leaf); struct Rec1 (*Node);};};",
  "struct Rec t[1];",
  "struct Tree t1[1];",
  "struct Rec t2[1];",
  "struct Tree t3[1];",
  "struct Rec1 t4[1];",
  "struct Tree t5[1];",
  "struct Rec t6[1];",
  "struct Tree t7[1];",
  "struct Rec t8[1];",
  "struct Tree t9[1];",
  "struct Rec1 t10[1];",
  "struct Tree t11[1];",
  "struct Rec1 t12[1];",
  "struct Tree tree[1];",
  "int treeRec(struct Tree (*t13)) {",
  "  struct Rec1 (*preMatch) = (t13->Node);",
  "  int preMatch1 = (preMatch->v);",
  "  struct Tree (*preMatch2) = (preMatch->l);",
  "  struct Tree (*preMatch3) = (preMatch->r);",
  "  if (((t13->constr) == Node)) {",
  "    int v1 = preMatch1;",
  "    struct Tree (*l1) = preMatch2;",
  "    struct Tree (*r1) = preMatch3;",
  "    int t14;",
  "    (t14 = treeRec(l1));",
  "    int t15;",
  "    (t15 = (v1 + t14));",
  "    int t16;",
  "    (t16 = treeRec(r1));",
  "    return (t15 + t16);",
  "  } else {",
  "    struct Rec (*preMatch4) = (t13->Leaf);",
  "    int preMatch5 = (preMatch4->v);",
  "    if (((t13->constr) == Leaf)) {",
  "      int v2 = preMatch5;",
  "      return v2;",
  "    } else {",
  "      ;",
  "    }",
  "  }",
  "}",
  "int sum;",
  "int main(int argc, char (*argv[])) {",
  "  ((t->v) = 7);",
  "  ((t1->constr) = Leaf);",
  "  ((t1->Leaf) = t);",
  "  ((t2->v) = 6);",
  "  ((t3->constr) = Leaf);",
  "  ((t3->Leaf) = t2);",
  "  ((t4->v) = 5);",
  "  ((t4->l) = t3);",
  "  ((t4->r) = t1);",
  "  ((t5->constr) = Node);",
  "  ((t5->Node) = t4);",
  "  ((t6->v) = 4);",
  "  ((t7->constr) = Leaf);",
  "  ((t7->Leaf) = t6);",
  "  ((t8->v) = 3);",
  "  ((t9->constr) = Leaf);",
  "  ((t9->Leaf) = t8);",
  "  ((t10->v) = 2);",
  "  ((t10->l) = t9);",
  "  ((t10->r) = t7);",
  "  ((t11->constr) = Node);",
  "  ((t11->Node) = t10);",
  "  ((t12->v) = 1);",
  "  ((t12->l) = t11);",
  "  ((t12->r) = t5);",
  "  ((tree->constr) = Node);",
  "  ((tree->Node) = t12);",
  "  (sum = treeRec(tree));",
  "  return 0;",
  "}"
] using eqString in

-- let leaf = match tree with node then leftnode else
let indirectAlloc = bindall_ [

  ulet_ "rec" (match_ (bool_ true) (pbool_ true) (urecord_ [("a",int_ 1)]) (urecord_ [("a",int_ 2)])),

  int_ 0

] in

-- TODO: This is WRONG, rec is never allocated
utest testCompile indirectAlloc with strJoin "\n" [
  "#include <stdio.h>",
  "#include <math.h>",
  "struct Rec {int a;};",
  "struct Rec (*rec);",
  "int main(int argc, char (*argv[])) {",
  "  if ((1 == 1)) {",
  "    ((rec->a) = 1);",
  "  } else {",
  "    ((rec->a) = 2);",
  "  }",
  "  return 0;",
  "}"
] using eqString in

-- let leaf = match tree with node then leftnode else
let seqs = bindall_ [

  -- Define nested sequence, and see how it is handled
  ulet_ "seq" (seq_ [seq_ [int_ 1], seq_ [int_ 2]]),

  -- Use "length" and "get" functions

  int_ 0

] in

printLn (testCompile seqs);
-- utest testCompile indirectAlloc with strJoin "\n" [
-- ] using eqString in

()
