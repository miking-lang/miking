-- This file provides a rather aggressive partial evaluator.
--
-- In this file, a _non-strict expression_ refers to an expression
-- that does not examine its free variables. For example, `addi x y`
-- is strict, it needs values for both `x` and `y` to proceed, but
-- `(x, y)` is not.
--
-- Assumptions:
-- * Pattern matches are shallow.
-- * The target of a `match` is a variable.
-- * All functions are named.
-- * Functions are only allowed to close over global values.
-- * Functions are never residual, i.e., a function is never passed to
--   a constant (other than the higher-order sequence ones) or external
--   that doesn't compute, and the arms of a residualized `match` never
--   produce different functions in the same position.

-- TODO(vipa, 2026-09-23): Maybe make consts that return `()` return a
-- non-residualized value

-- TODO(vipa, 2026-09-30): The current implementation ends up being
-- entirely monomorphizing, which is technically overly restrictive,
-- we should be able to emit polymorphic things, either when the type
-- doesn't matter to the implementation, or when we use polymorphic
-- recursion. Leaving it as is for the moment though

-- TODO(vipa, 2026-10-05): There's a discrepancy between `pegGenPairs`
-- for `Char` vs `Int`, `Float`, and `Symbol`, the former needs exact
-- match, the latter three always match. It seems unlikely we'd write
-- a function that does recursion on, e.g., incrementing characters,
-- so this might be fine. There's a similar argument to be made for
-- `Symbol`, but then again it's easy to call `gensym` in a loop. Then
-- again again `gensym` has a side-effect, so we won't ever actually
-- produce `VSymb`, so it might not matter.

include "int.mc"
include "seq.mc"
include "info.mc"
include "basic-types.mc"
include "bool.mc"
include "map.mc"
include "name.mc"
include "list.mc"
include "set.mc"
include "either.mc"
include "option.mc"
include "stringid.mc"
include "string.mc"
include "lazy.mc"
include "thunk.mc"
include "error.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"
include "mexpr/cmp.mc"
include "mexpr/const-types.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type.mc"
include "mexpr/type-check.mc"
include "mexpr/free-vars.mc"
include "mexpr/resymbolize.mc"
include "mexpr/keyword-maker.mc"

lang PEvalGraph = Ast + NamedPat + VarAst + RecLetsDeclAst + MExprCmp + PrettyPrint + VarTypeSubstitute
  type SymInt = Int
  type VRef = Int

  syn PEGVal =
  | VRef {ty : Type, ref : VRef}

  sem smapAccumL_PEGVal_PEGVal : all acc. (acc -> PEGVal -> (acc, PEGVal)) -> acc -> PEGVal -> (acc, PEGVal)
  sem smapAccumL_PEGVal_PEGVal f acc = | v -> (acc, v)

  sem smap_PEGVal_PEGVal : (PEGVal -> PEGVal) -> PEGVal -> PEGVal
  sem smap_PEGVal_PEGVal f =
  | v -> (smapAccumL_PEGVal_PEGVal (lam. lam v. ((), f v)) () v).1

  sem sfold_PEGVal_PEGVal : all acc. (acc -> PEGVal -> acc) -> acc -> PEGVal -> acc
  sem sfold_PEGVal_PEGVal f acc =
  | v -> (smapAccumL_PEGVal_PEGVal (lam acc. lam v. (f acc v, v)) acc v).0

  syn PEGInstr =

  type PEGBlock =
    { name : Name
    , params : [Type]
    , instructions : [PEGInstr]
    -- These are the residual values being returned
    , toRet : [VRef]
    -- This is how to build the singular return value from the
    -- residual values above (i.e., `VRef`s index into `toRet`)
    , retValue : PEGVal
    }

  type PEGBlockKey =
    { function : SymInt
    , instantiation : Map Name Type
    , args : [PEGVal]
    }
  sem cmpPEGBlockKey : PEGBlockKey -> PEGBlockKey -> Int
  sem cmpPEGBlockKey a = | b ->
    let res = subi a.function b.function in
    if neqi res 0 then res else
    let res = mapCmp cmpType a.instantiation b.instantiation in
    if neqi res 0 then res else seqCmp cmpPEGVal a.args b.args

  sem cmpPEGVal : PEGVal -> PEGVal -> Int
  sem cmpPEGVal a = | b -> cmpPEGValH (a, b)

  sem cmpPEGValH : (PEGVal, PEGVal) -> Int
  sem cmpPEGValH =
  | (VRef a, VRef b) -> subi a.ref b.ref
  | (a, b) ->
    let res = subi (constructorTag a) (constructorTag b) in
    if eqi res 0
    then error "Missing case in cmpPEGValH for values with equal indices."
    else res

  type PEGEnv =
    { values : List (SymInt, PEGVal)
    , tyValues : Map Name Type
    , finalBlocks : Thunk (Map Name PEGBlock)
    , inline : (PEGVal, [PEGVal]) -> Bool
    }

  type PEGState =
    { computedBlocks : Map PEGBlockKey PEGBlock
    , requestedBlocks : Map PEGBlockKey BlockRequest
    , instructions : [PEGInstr]
    , nextVRef : VRef
    , callStack : [PEGBlockKey]
    }

  syn BlockRequest = | BlockRequest
    { name : Name
    , residualParamTypes : [Type]
    , compute : PEGState -> (PEGState, PEGVal)
    , callStack : [PEGBlockKey]
    }

  sem requestBlock : PEGState -> PEGBlockKey -> [Type] -> (PEGState -> Map Name Type -> [PEGVal] -> (PEGState, PEGVal)) -> (PEGState, Name)
  sem requestBlock st key residualParamTypes = | body ->
    match mapLookup key st.requestedBlocks with Some (BlockRequest x) then
      (st, x.name)
    else
      let name = nameSym "block" in
      let request = BlockRequest
        { name = name
        , residualParamTypes = residualParamTypes
        , compute = lam st. body st key.instantiation key.args
        , callStack = snoc st.callStack key
        } in
      ({st with requestedBlocks = mapInsert key request st.requestedBlocks}, name)

  sem forceBlock : PEGState -> PEGBlockKey -> (PEGState, PEGBlock)
  sem forceBlock st = | key ->
    match mapLookup key st.requestedBlocks with Some (BlockRequest x) then
      let localSt =
        { computedBlocks = st.computedBlocks
        , requestedBlocks = st.requestedBlocks
        , instructions = []
        , nextVRef = length x.residualParamTypes
        , callStack = x.callStack
        } in
      match x.compute localSt with (localSt, retValue) in

      recursive let renumber = lam acc. lam val.
        match val with VRef v then
          match acc with (toRet, nextVRef) in
          ( (snoc toRet v.ref, addi nextVRef 1)
          , VRef {v with ref = nextVRef}
          )
        else smapAccumL_PEGVal_PEGVal renumber acc val
      in

      match renumber ([], 0) retValue with ((toRet, _), retValue) in

      let block =
        { name = x.name
        , params = x.residualParamTypes
        , instructions = localSt.instructions
        , toRet = toRet
        , retValue = retValue
        } in
      ( { st with computedBlocks = mapInsert key block localSt.computedBlocks
        , requestedBlocks = mapRemove key localSt.requestedBlocks
        }
      , block
      )
    else error "Compiler error: Tried to force a non-existant block."

  sem forceAllBlocks : PEGState -> PEGState
  sem forceAllBlocks = | st ->
    match mapChoose st.requestedBlocks with Some (key, _)
    then forceAllBlocks (forceBlock st key).0
    else st

  type EvalF = PEGEnv -> PEGState -> (PEGState, PEGVal)

  sem mkEvalF : Expr -> EvalF
  sem mkPatF : Pat -> PEGEnv -> PEGVal -> Option PEGEnv
  sem mkEvalDeclF : Decl -> PEGEnv -> PEGState -> (PEGState, PEGEnv)

  -- The entry point, which expects a type checked expression
  sem mkTopEvalF : Expr -> EvalF
  sem mkTopEvalF = | tm ->
    mkEvalF (fixRecursiveInstantiate (mapEmpty nameCmp) tm)

  -- The `Type` is the type of the result of the application
  sem applyF : PEGEnv -> PEGState -> Type -> (PEGVal, [PEGVal]) -> (PEGState, PEGVal)

  sem pegGenPairs : (PEGVal, PEGVal) -> Bool
  sem pegGenPairs =
  | (l, r) ->
    if eqi (constructorTag l) (constructorTag r)
    then error "Missing case in pegGenPairs"
    else false
  | (VRef _, VRef _) -> true

  sem pegGenEmbeds : PEGVal -> PEGVal -> Bool
  sem pegGenEmbeds needle = | haystack ->
    if pegGenPairs (needle, haystack) then true else
    sfold_PEGVal_PEGVal
      (lam acc. lam c. if acc then true else pegGenEmbeds needle c)
      false
      haystack

  -- TODO(vipa, 2026-09-30): This is a work-around for the current
  -- handling of instantiation in the type-checker. Due to how
  -- inference for un-annotated recursive functions work, we never see
  -- the uninstantiated type _inside_ such a function, thus the
  -- `instantiated` field of a `TmVar` will be unpopulated. This fixes
  -- that, but should ideally eventually be removed when this is fixed
  -- in the type checker itself.
  sem fixRecursiveInstantiate : Map Name Type -> Expr -> Expr
  sem fixRecursiveInstantiate tyEnv =
  | tm -> smap_Expr_Expr (fixRecursiveInstantiate tyEnv) tm
  | TmDecl (x & {decl = DeclRecLets d}) ->
    let f = lam tyEnv. lam binding.
      mapInsert binding.ident binding.tyBody tyEnv in
    let localTyEnv = foldl f tyEnv d.bindings in
    let f = lam binding.
      {binding with body = fixRecursiveInstantiate localTyEnv binding.body} in
    TmDecl {x with decl = DeclRecLets {d with bindings = map f d.bindings}, inexpr = fixRecursiveInstantiate tyEnv x.inexpr}
  | TmVar (x & {frozen = false}) ->
    match mapLookup x.ident tyEnv with Some ty then
      match stripTyAll ty with (vars, stripped) in
      let vars = setOfSeq nameCmp (map (lam v. v.0) vars) in
      TmVar {x with instantiated = _matchTyVars vars (mapEmpty nameCmp) stripped x.ty}
    else TmVar x

  -- Finds what each of `vars` (as they appear in `pat`) corresponds
  -- to in `ty`
  sem _matchTyVars : Set Name -> Map Name Type -> Type -> Type -> Map Name Type
  sem _matchTyVars vars acc pat = | ty ->
    let pat = unwrapType pat in
    let ty = unwrapType ty in
    match pat with TyVar x then
      if setMem x.ident vars then mapInsert x.ident ty acc else acc
    else
      let children = lam ty. sfold_Type_Type snoc [] ty in
      let patChildren = children pat in
      let tyChildren = children ty in
      if and (eqi (constructorTag pat) (constructorTag ty))
          (eqi (length patChildren) (length tyChildren))
      then foldl2 (_matchTyVars vars) acc patChildren tyChildren
      else acc

  -- Errors with the given message if the name is unsymbolized
  sem nameToSymInt : [Info] -> String -> Name -> SymInt
  sem nameToSymInt infos msg = | n ->
    match nameGetSym n with Some s
    then sym2hash s
    else errorSingle infos msg

  -- This should produce a canonical order of all names bound in a
  -- shallow Pat
  sem collectPatNames : Pat -> [(Name, Type)]
  sem collectPatNames = | pat ->
    let f = lam acc. lam pat.
      match pat with PatNamed {ident = PName ident, ty = ty}
      then snoc acc (ident, ty)
      else acc in
    sfold_Pat_Pat f [] pat

  sem pegNewVRef : Type -> PEGState -> (PEGState, PEGVal)
  sem pegNewVRef ty = | st ->
    let idx = st.nextVRef in
    ({st with nextVRef = addi idx 1}, VRef {ty = ty, ref = idx})

  sem pegEmit : Type -> PEGState -> PEGInstr -> (PEGState, PEGVal)
  sem pegEmit ty st = | instr ->
    match pegNewVRef ty st with (st, val) in
    ({st with instructions = snoc st.instructions instr}, val)

  sem pegValTy : PEGVal -> Type
  sem pegValTy = | VRef x -> x.ty

  -- Every type read from the AST goes through this, since it may
  -- mention type variables of a polymorphic function we're currently
  -- evaluating an instantiation of
  sem pegSubstTy : PEGEnv -> Type -> Type
  sem pegSubstTy env = | ty ->
    if mapIsEmpty env.tyValues then ty
    else substituteVars (infoTy ty) env.tyValues ty

  sem pegSubstPat : PEGEnv -> Pat -> Pat
  sem pegSubstPat env = | pat ->
    let pat = withTypePat (pegSubstTy env (tyPat pat)) pat in
    smap_Pat_Pat (pegSubstPat env) pat

  sem pegInst : Map Name Type -> PEGVal -> PEGVal
  sem pegInst tyValues = | v -> v

  -- `replace` is given the values at each place where they differ
  -- structurally, one per input, and produces what goes there instead
  sem homogenizeValues : all st. (st -> [PEGVal] -> (st, PEGVal)) -> st -> [PEGVal] -> (st, PEGVal)
  sem homogenizeValues replace st = | vs -> replace st vs

  sem pegValToString : PEGVal -> String
  sem pegValToString =
  | VRef x -> concat "r" (int2string x.ref)

  sem pegValsToString : [PEGVal] -> String
  sem pegValsToString = | vals ->
    join ["[", strJoin ", " (map pegValToString vals), "]"]

  sem vrefToString : VRef -> String
  sem vrefToString = | r -> concat "r" (int2string r)

  -- `firstVRef` is the first `VRef` this instruction defines, which
  -- only a nested instruction list needs
  sem pegInstrToString : VRef -> PEGInstr -> (Int, String)

  -- `firstVRef` is the first `VRef` these instructions define, i.e. 0
  -- at the top level and the number of parameters inside a block
  sem pegInstrsToString : String -> VRef -> [PEGInstr] -> String
  sem pegInstrsToString indent firstVRef = | instrs ->
    let f = lam nextVRef. lam instr.
      match pegInstrToString nextVRef instr with (count, str) in
      let refs = create count (lam i. vrefToString (addi nextVRef i)) in
      ( addi nextVRef count
      , join [indent, "[", strJoin ", " refs, "] ", str, "\n"]
      ) in
    join (mapAccumL f firstVRef instrs).1

  sem pegBlockToString : PEGBlock -> String
  sem pegBlockToString = | block -> join
    [ "  ", nameGetStr block.name
    , "("
    , strJoin ", "
      (mapi
        (lam i. lam ty. join [vrefToString i, ": ", type2str ty])
        block.params)
    , "):\n"
    , pegInstrsToString "    " (length block.params) block.instructions
    , "    return ", pegValToString block.retValue
    , " of [", strJoin ", " (map vrefToString block.toRet), "]\n"
    ]
end

lang PEvalGraphDecl = PEvalGraph + DeclAst
  sem mkEvalF += | TmDecl x ->
    let decl = mkEvalDeclF x.decl in
    let inexpr = mkEvalF x.inexpr in
    lam env. lam st.
      match decl env st with (st, env) in
      inexpr env st
end

lang PEvalGraphConst = PEvalGraph + ConstAst + Cmp + ConstPrettyPrint + TyConst
  -- A function passed to a higher-order constant. It has a scope of
  -- `VRef`s of its own: `params` are the arguments it is applied to
  -- and `instr` is the single instruction its body compiled to, whose
  -- result `ret` is built from. The scope continues the numbering of
  -- the enclosing one, since `instr` may refer to anything emitted
  -- before the call, but its `VRef`s die with the call, which is why
  -- the call itself returns into the first of them.
  type PEGFunArg = {params : [PEGVal], instr : PEGInstr, ret : PEGVal}

  syn PEGInstr +=
  | IConstCall
    { const : Const
    , args : [PEGVal]
    }
  | IConstFCall
    { const : Const
    , args : [Either PEGFunArg PEGVal]
    }

  syn PEGVal +=
  | VConst {const : Const, f : [PEGVal] -> Option PEGVal}
  | VConstF (PEGEnv -> PEGState -> Type -> [PEGVal] -> (PEGState, PEGVal))

  sem mkDeltaF : Const -> PEGVal

  sem deltaF : Const -> ([PEGVal] -> Option PEGVal) -> PEGVal
  sem deltaF c = | f -> VConst {const = c, f = f}

  sem mkEvalF += | TmConst x ->
    let val = mkDeltaF x.val in
    lam. lam st. (st, val)

  sem applyF env st ty += | (VConst x, args) ->
    match x.f args with Some v
    then (st, v)
    else pegEmit ty st (IConstCall {const = x.const, args = args})

  sem applyF env st ty += | (VConstF f, args) -> f env st ty args

  -- Evaluates `f` applied to one fresh `VRef` per entry in
  -- `paramTys`, in a scope of its own, where `ty` is the type of the
  -- result of that application. Inlining is off in there, since the
  -- body is evaluated once but run many times.
  sem pegFunArg : PEGEnv -> PEGState -> Type -> [Type] -> PEGVal -> (PEGState, PEGFunArg)
  sem pegFunArg env st ty paramTys = | f ->
    let localSt = {st with instructions = []} in
    let localEnv = {env with inline = lam. false} in
    match mapAccumL (lam st. lam ty. pegNewVRef ty st) localSt paramTys
    with (localSt, params) in
    match applyF localEnv localSt ty (f, params) with (localSt, ret) in
    match localSt.instructions with [instr] then
      ( { st with
          computedBlocks = localSt.computedBlocks
        , requestedBlocks = localSt.requestedBlocks
        }
      , {params = params, instr = instr, ret = ret}
      )
    else error "Unexpected function given to a higher-order constant"

  sem pegValTy += | VConst _ -> tyunknown_
  sem pegValTy += | VConstF _ -> tyunknown_

  -- A delta function for a constant that never computes here
  sem residualDeltaF : Const -> PEGVal
  sem residualDeltaF = | c -> deltaF c (lam. None ())

  sem pegValToString += | VConst _ -> "<constant function>"
  sem pegValToString += | VConstF _ -> "<constant function (higher order)>"

  sem pegGenPairs += | (VConst a, VConst b) -> eqi (cmpConst a.const b.const) 0
  sem pegGenPairs += | (VConstF _, VConstF _) -> true

  sem pegInstrToString firstVRef += | IConstCall x ->
    ( 1
    , join
      [ getConstStringCode 0 x.const
      , " "
      , strJoin " " (map pegValToString x.args)
      ]
    )

  -- The function arguments are printed after the value ones, rather
  -- than in their original position, since each spans several lines
  sem pegInstrToString firstVRef += | IConstFCall x ->
    let fToString = lam fArg : PEGFunArg.
      join
        [ "\n      \\", strJoin " " (map pegValToString fArg.params), " ->\n"
        , pegInstrsToString "        "
          (addi firstVRef (length fArg.params)) [fArg.instr]
        , "        out ", pegValToString fArg.ret
        ] in
    ( 1
    , join
      [ getConstStringCode 0 x.const
      , join
        (map (eitherEither (lam. "") (lam v. cons ' ' (pegValToString v)))
          x.args)
      , join (map (eitherEither fToString (lam. "")) x.args)
      ]
    )

  -- The identity function, except that it always residualizes, which
  -- lets a test produce a residual value of any type.
  syn Const += | CResidualIdentity {}

  sem tyConstBase d += | CResidualIdentity _ ->
    tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))

  sem mkDeltaF += | c & CResidualIdentity _ -> deltaF c (lam args.
    match args with [v]
    then None ()
    else error "Wrong number of arguments to CResidualIdentity in mkDeltaF!")

  sem getConstStringCode indent += | CResidualIdentity _ -> "residualIdentity"
end

lang PEvalGraphLam = PEvalGraph + LamAst + PEvalGraphConst
  syn PEGVal +=
  | VLam {sym : SymInt, isRecursiveCall : Bool, arity : Int, applied : [PEGVal], instantiated : Map Name Type, body : PEGState -> Map Name Type -> [PEGVal] -> (PEGState, PEGVal)}

  syn PEGInstr +=
  | IBlockCall
    { block : Name
    , args : [VRef]
    -- `VRef`s here index into the return values of the called block,
    -- _not_ the current block
    , return : Either (Lazy PEGVal) [Type]
    }

  sem mkLam : Expr -> Option (Int, PEGEnv -> PEGState -> Map Name Type -> [PEGVal] -> (PEGState, PEGVal))
  sem mkLam =
  | _ -> None ()
  | tm & TmLam _ ->
    recursive let collect = lam params. lam tm.
      match tm with TmLam x then
        let s = nameToSymInt [x.info] "Unsymbolized TmLam in mkLam!" x.ident in
        collect (snoc params s) x.body
      else (params, tm) in
    match collect [] tm with (params, body) in
    let body = mkEvalF body in
    let f = lam env. lam st. lam tyValues. lam args.
      if eqi (length params) (length args) then
        let values = foldl2
          (lam values. lam p. lam a. Cons ((p, a), values))
          env.values
          params
          args in
        body {env with values = values, tyValues = mapUnion env.tyValues tyValues} st
      else error "Applied a function with the wrong number of arguments" in
    Some (length params, f)

  sem pegInst tyValues += | VLam x ->
    VLam {x with instantiated = mapUnion x.instantiated tyValues}

  sem _prepBlockKey : PEGState -> SymInt -> Map Name Type -> [PEGVal] -> (PEGState, PEGBlockKey, [(VRef, Type)])
  sem _prepBlockKey st function instantiation = | args ->
    let embedsHere = lam key.
      if neqi key.function function then false else
      if neqi (mapCmp cmpType key.instantiation instantiation) 0 then false else
      eqSeq pegGenEmbeds key.args args in
    let residualize = lam st. lam vs.
      match vs with [_, fill] in
      match fill with VRef _ then (st, fill) else
      let instr = IConstCall {const = CResidualIdentity (), args = [fill]} in
      pegEmit (pegValTy fill) st instr in
    let generalize = lam prev.
      mapAccumL
        (lam st. lam pair. homogenizeValues residualize st [pair.0, pair.1])
        st
        (zip prev.args args) in
    match
      match findLast embedsHere st.callStack with Some prev
      then generalize prev
      else (st, args)
    with (st, args) in
    recursive let abstract = lam acc. lam val.
      match val with VRef x then
        match acc with (params, nextVRef) in
        ((snoc params (x.ref, x.ty), addi nextVRef 1), VRef {x with ref = nextVRef})
      else smapAccumL_PEGVal_PEGVal abstract acc val
    in
    match mapAccumL abstract ([], 0) args with ((params, _), args) in
    (st, {function = function, instantiation = instantiation, args = args}, params)

  sem _blockCall : PEGState -> PEGBlock -> [VRef] -> (PEGState, PEGVal)
  sem _blockCall st block = | args ->
    recursive let work = lam return. lam v.
      match v with VRef x then
        ( snoc return x.ty
        , VRef {x with ref = addi x.ref st.nextVRef}
        )
      else smapAccumL_PEGVal_PEGVal work return v in
    match work [] block.retValue with (return, retValue) in
    let instr = IBlockCall
      { block = block.name
      , args = args
      , return = Right return
      } in
    let st =
      { st with
        instructions = snoc st.instructions instr
      , nextVRef = addi st.nextVRef (length return)
      } in
    (st, retValue)

  sem applyF env st ty += | app & (VLam x, args) ->
    let applied = concat x.applied args in
    if lti (length applied) x.arity then
      (st, VLam {x with applied = applied})
    else if env.inline app then
      x.body st x.instantiated applied
    else
      match _prepBlockKey st x.sym x.instantiated applied with (st, key, args) in
      match mapLookup key st.computedBlocks with Some block then
        _blockCall st block (map (lam x. x.0) args)
      else
        match requestBlock st key (map (lam x. x.1) args) x.body with (st, blockName) in
        if x.isRecursiveCall then
          let finalBlocks = env.finalBlocks in
          let mkRet = lam.
            match mapLookup blockName (finalBlocks.read ()) with Some x in
            x.retValue in
          let instr = IBlockCall
            { block = blockName
            , args = map (lam x. x.0) args
            , return = Left (lazy mkRet)
            } in
          pegEmit ty st instr
        else
          match forceBlock st key with (st, block) in
          _blockCall st block (map (lam x. x.0) args)

  sem pegInstrToString firstVRef += | IBlockCall x ->
    let call = join
      [ nameGetStr x.block
      , "(", strJoin ", " (map vrefToString x.args), ")"
      ] in
    switch x.return
    case Left val then
      (1, join [call, ", returning ", pegValToString (lazyForce val)])
    case Right tys then
      (length tys, join [call, " : ", strJoin ", " (map type2str tys)])
    end

  sem smapAccumL_PEGVal_PEGVal f acc += | VLam x ->
    match mapAccumL f acc x.applied with (acc, applied) in
    (acc, VLam {x with applied = applied})

  sem cmpPEGValH += | (VLam a, VLam b) ->
    let res = subi a.sym b.sym in
    if neqi res 0 then res else
    let res = subi (if a.isRecursiveCall then 1 else 0) (if b.isRecursiveCall then 1 else 0) in
    if neqi res 0 then res else
    let res = mapCmp cmpType a.instantiated b.instantiated in
    if neqi res 0 then res else
    seqCmp cmpPEGVal a.applied b.applied

  sem pegGenPairs += | (VLam a, VLam b) ->
    if neqi a.sym b.sym then false else
    if xor a.isRecursiveCall b.isRecursiveCall then false else
    if neqi (mapCmp cmpType a.instantiated b.instantiated) 0 then false else
    eqSeq pegGenEmbeds a.applied b.applied

  -- A function cannot be residual, thus every value must be the same
  -- function, but they may be applied to different arguments
  sem homogenizeValues replace st += | allVs & [VLam x] ++ _ ->
    let unapplied = VLam {x with applied = []} in
    let check = lam v.
      match v with VLam x2 then
        if eqi (cmpPEGValH (unapplied, VLam {x2 with applied = []})) 0
        then if eqi (length x.applied) (length x2.applied) then Some x2.applied else None ()
        else None ()
      else None () in
    match optionMapM check allVs with Some appliedss then
      match mapAccumL (homogenizeValues replace) st (transpose appliedss)
      with (st, applied) in
      (st, VLam {x with applied = applied})
    else error "Compiler error: different functions flow to the same place, which would require a residual function."

  sem pegValToString += | VLam x -> join
    [ "<lambda ", int2string x.sym
    , if null x.applied then ""
      else concat ", applied = " (pegValsToString x.applied)
    , if mapIsEmpty x.instantiated then ""
      else join
        [ ", instantiated = {"
        , strJoin ", "
          (map
            (lam b. join [nameGetStr b.0, " = ", type2str b.1])
            (mapBindings x.instantiated))
        , "}"
        ]
    , ", remaining = ", int2string (subi x.arity (length x.applied))
    , ">"
    ]
end

lang PEvalGraphLet = PEvalGraph + LetDeclAst + PEvalGraphLam
  sem mkEvalDeclF += | DeclLet x ->
    let s = nameToSymInt [x.info] "Unsymbolized DeclLet in mkEvalDeclF!" x.ident in
    match mkLam x.body with Some (arity, f) then
      lam env. lam st.
        let val = VLam {sym = s, isRecursiveCall = false, body = f env, arity = arity, applied = [], instantiated = mapEmpty nameCmp} in
        let env = {env with values = Cons ((s, val), env.values)} in
        (st, env)
    else
      let body = mkEvalF x.body in
      lam env. lam st.
        match body env st with (st, body) in
        let env = {env with values = Cons ((s, body), env.values)} in
        (st, env)
end

lang PEvalGraphRecLets = PEvalGraph + RecLetsDeclAst + PEvalGraphLam
  sem mkEvalDeclF += | DeclRecLets x ->
    let prepLam = lam binding.
      let s = nameToSymInt [binding.info]
        "Unsymbolized DeclRecLets binding in mkEvalDeclF!" binding.ident in
      match mkLam binding.body with Some f
      then (s, f)
      else errorSingle [binding.info] "Non-lambda in DeclRecLets rhs in mkEvalDeclF!" in
    let pairs = map prepLam x.bindings in
    lam env. lam st.
      let recEnv = mkThunk (lazy (lam. concat "recursive env in DeclRecLets at " (info2str x.info))) in
      let f = lam acc. lam pair.
        match (acc, pair) with ((rValues, nValues), (s, (arity, f))) in
        let body = lam st. lam tyValues. lam args.
          f (recEnv.read ()) st tyValues args in
        ( Cons ((s, VLam {sym = s, isRecursiveCall = true, arity = arity, applied = [], instantiated = mapEmpty nameCmp, body = body}), rValues)
        , Cons ((s, VLam {sym = s, isRecursiveCall = false, arity = arity, applied = [], instantiated = mapEmpty nameCmp, body = body}), nValues)
        ) in
      match foldl f (env.values, env.values) pairs with (rValues, nValues) in
      recEnv.write {env with values = rValues};
      (st, {env with values = nValues})
end

lang PEvalGraphType = PEvalGraph + TypeDeclAst
  sem mkEvalDeclF += | DeclType _ -> lam env. lam st. (st, env)
end

lang PEvalGraphVar = PEvalGraph + VarAst
  sem mkEvalF += | TmVar x ->
    let s = nameToSymInt [x.info] "Unsymbolized TmVar in mkEvalF!" x.ident in
    let instantiated = x.instantiated in
    let lookup = lam pair. match pair with (s2, v) in
      if eqi s s2 then Some v else None () in
    if mapIsEmpty instantiated then
      lam env. lam st.
        match listFindMap lookup env.values with Some v
        then (st, v)
        else errorSingle [x.info] "Unbound variable in mkEvalF!"
    else
      lam env. lam st.
        let instantiated = mapMap (pegSubstTy env) instantiated in
        match listFindMap lookup env.values with Some v
        then (st, pegInst instantiated v)
        else errorSingle [x.info] "Unbound variable in mkEvalF!"
end

lang PEvalGraphApp = PEvalGraph + AppAst
  sem mkEvalF += | tm & TmApp _ ->
    recursive let collect = lam args. lam tm.
      match tm with TmApp x
      then collect (cons x.rhs args) x.lhs
      else (tm, args) in
    match collect [] tm with (f, args) in
    let ty = tyTm tm in
    let f = mkEvalF f in
    let args = map mkEvalF args in
    lam env. lam st.
      match f env st with (st, f) in
      match mapAccumL (lam st. lam arg. arg env st) st args with (st, args) in
      applyF env st (pegSubstTy env ty) (f, args)
end

lang PEvalGraphOpaque =
  PEvalGraphConst + PEvalGraphLam + OpaqueAst + MExprFreeVars + MExprResymbolize

  -- The body is residualized as is, except that its free variables are
  -- renamed, and `bindings` gives the value each of them refers to
  syn PEGInstr +=
  | IOpaque
    { bindings : Map Name (Either PEGFunArg PEGVal)
    , body : Expr
    }

  sem fixRecursiveInstantiate tyEnv +=
  | TmOpaque x -> TmOpaque {x with body = fixRecursiveInstantiate tyEnv x.body}

  -- The type and instantiation of the first occurrence of each of
  -- `names`
  sem _collectOccurrences : Set Name -> Map Name (Type, Map Name Type) -> Expr -> Map Name (Type, Map Name Type)
  sem _collectOccurrences names acc =
  | TmVar x ->
    if and (setMem x.ident names) (not (mapMem x.ident acc))
    then mapInsert x.ident (x.ty, x.instantiated) acc
    else acc
  | tm -> sfold_Expr_Expr (_collectOccurrences names) acc tm

  sem mkEvalF += | TmOpaque x ->
    let free = freeVars x.body in
    let subst = mapFromSeq nameCmp
      (map (lam n. (n, nameSetNewSym n)) (setToSeq free)) in
    let body = resymbolizeExpr subst x.body in
    -- TODO(vipa, 2026-10-05): We assume that each function referenced
    -- in a `TmOpaque` is only used monomorphically. This is not
    -- generally true, but tends to be true in practice.
    let occurrences = _collectOccurrences free (mapEmpty nameCmp) x.body in
    let prepFree = lam old. lam new.
      match mapLookup old occurrences with Some (ty, instantiated) in
      ( new
      , { sym = nameToSymInt [x.info] "Unsymbolized free variable in TmOpaque in mkEvalF!" old
        , ty = ty
        , instantiated = instantiated
        }
      ) in
    let free = mapFromSeq nameCmp (mapValues (mapMapWithKey prepFree subst)) in
    let ty = x.ty in
    lam env. lam st.
      let prepBinding = lam st. lam. lam f.
        let lookup = lam pair. match pair with (s, v) in
          if eqi s f.sym then Some v else None () in
        match listFindMap lookup env.values with Some v in
        let v = pegInst (mapMap (pegSubstTy env) f.instantiated) v in
        match v with VLam l then
          recursive let splitArrows = lam n. lam ty.
            if eqi n 0 then ([], ty) else
            match unwrapType ty with TyArrow a in
            match splitArrows (subi n 1) a.to with (params, ret) in
            (cons a.from params, ret) in
          match splitArrows (subi l.arity (length l.applied)) (pegSubstTy env f.ty)
          with (params, ret) in
          match pegFunArg env st ret params v with (st, fArg) in
          (st, Left fArg)
        else (st, Right v) in
      match mapMapAccum prepBinding st free with (st, bindings) in
      pegEmit (pegSubstTy env ty) st (IOpaque {bindings = bindings, body = body})

  sem pegInstrToString firstVRef += | IOpaque x ->
    let bindingToString = lam b.
      match b with (n, arg) in
      switch arg
      case Right v then join ["\n      ", nameGetStr n, " = ", pegValToString v]
      case Left fArg then
        join
          [ "\n      ", nameGetStr n, " = \\", strJoin " " (map pegValToString fArg.params), " ->\n"
          , pegInstrsToString "        "
            (addi firstVRef (length fArg.params)) [fArg.instr]
          , "        out ", pegValToString fArg.ret
          ]
      end in
    ( 1
    , join
      [ "opaque"
      , join (map bindingToString (mapBindings x.bindings))
      , "\n      in ", (pprintCode 9 pprintEnvEmpty x.body).1
      ]
    )
end

lang PEvalGraphExt = PEvalGraph + ExtDeclAst + FunArity
  syn PEGInstr +=
  | IExtCall
    { ident : Name
    , args : [PEGVal]
    }

  syn PEGVal += | VExtF {ident : Name, argCount : Int, info : Info}

  sem applyF env st ty += | (VExtF x, args) ->
    if eqi x.argCount (length args)
    then pegEmit ty st (IExtCall {ident = x.ident, args = args})
    else errorSingle [x.info] (join ["Wrong number of arguments to external, got ", int2string (length args), ", expected ", int2string x.argCount])

  sem pegValTy += | VExtF _ -> tyunknown_

  sem mkEvalDeclF += | DeclExt x ->
    let info = x.info in
    let s = nameToSymInt [info] "Unsymbolized DeclExt in mkEvalDeclF!" x.ident in
    match arityFunType x.tyIdent with argCount & !0 then
      lam env. lam st.
        let val = VExtF {ident = x.ident, argCount = argCount, info = info} in
        (st, {env with values = Cons ((s, val), env.values)})
    else
      lam env. lam st.
        match pegEmit (pegSubstTy env x.tyIdent) st (IExtCall {ident = x.ident, args = []})
        with (st, val) in
        (st, {env with values = Cons ((s, val), env.values)})

  sem pegValToString += | VExtF x -> join ["<external ", nameGetStr x.ident, ">"]

  sem pegGenPairs += | (VExtF a, VExtF b) -> nameEq a.ident b.ident

  sem pegInstrToString firstVRef += | IExtCall x ->
    ( 1
    , join [nameGetStr x.ident, " ", strJoin " " (map pegValToString x.args)]
    )
end

lang PEvalGraphMatch = PEvalGraph + MatchAst + VarAst + NamedPat
  -- The three things an arm needs: how to match its pattern against a
  -- known value, the names the pattern binds (which become fresh
  -- `VRef`s when the target is residual), and its body
  type PEGArmF =
    { patF : PEGEnv -> PEGVal -> Option PEGEnv
    , patNames : [(SymInt, Type)]
    , bodyF : PEGEnv -> PEGState -> (PEGState, PEGVal)
    }

  sem prepArm : (Pat, Expr) -> PEGArmF
  sem prepArm = | (pat, body) ->
    { patF =
      match pat with PatNamed {ident = PWildcard _}
      then lam env. lam. Some env
      else mkPatF pat
    , patNames = map
      (lam pair.
        ( nameToSymInt [infoPat pat] "Unsymbolized pat name in prepArm!" pair.0
        , pair.1
        ))
      (collectPatNames pat)
    , bodyF = mkEvalF body
    }

  syn PEGInstr +=
  | IMatch
    { target : VRef
    -- Each arm is a pattern, the instructions it runs in its own
    -- namespace of `VRef`s (which starts after the ones its pattern
    -- binds), and the values it passes out
    , arms : [(Pat, [PEGInstr], [PEGVal])]
    }

  -- The values each arm passes out, and the value the `match` as a
  -- whole produces from them
  sem homogenizeArms : PEGState -> [PEGVal] -> (PEGState, [[PEGVal]], PEGVal)
  sem homogenizeArms st = | vals ->
    let replace = lam acc. lam vs.
      match acc with (st, valss) in
      match pegNewVRef (pegValTy (head vs)) st with (st, v) in
      ((st, zipWith snoc valss vs), v) in
    match homogenizeValues replace (st, map (lam. []) vals) vals
    with ((st, valss), val) in
    (st, valss, val)

  sem mkEvalF += | tm & TmMatch {target = target & TmVar {ident = ident}} ->
    recursive let collectArms = lam arms. lam tm.
      match tm with TmMatch (x & {target = TmVar {ident = newIdent}})
      then if nameEq ident newIdent
        then collectArms (snoc arms (x.pat, x.thn)) x.els
        else snoc arms (pvarw_, tm)
      else snoc arms (pvarw_, tm) in
    let target = mkEvalF target in
    let arms = collectArms [] tm in
    let pats = map (lam x. x.0) arms in
    let arms = map prepArm arms in
    lam env. lam st.
      match target env st with (st, target) in
      match target with VRef x then
        let outerInstrs = st.instructions in
        let base = st.nextVRef in
        -- We don't inline functions under residualized branches
        let armEnv = {env with inline = lam. false} in
        let evalArm = lam st. lam arm.
          let addName = lam acc. lam pair.
            match acc with (st, values) in
            match pegNewVRef (pegSubstTy env pair.1) st with (st, v) in
            (st, Cons ((pair.0, v), values)) in
          match foldl addName ({st with instructions = [], nextVRef = base}, env.values) arm.patNames
          with (st, values) in
          match arm.bodyF {armEnv with values = values} st with (st, val) in
          (st, (st.instructions, val)) in
        match mapAccumL evalArm st arms with (st, armResults) in
        let st = {st with instructions = outerInstrs, nextVRef = base} in
        match homogenizeArms st (map (lam r. r.1) armResults) with (st, valss, ret) in
        let mkArm = lam pat. lam pair. (pegSubstPat env pat, (pair.0).0, pair.1) in
        let instr = IMatch
          {target = x.ref, arms = zipWith mkArm pats (zip armResults valss)} in
        ({st with instructions = snoc st.instructions instr}, ret)
      else
        let runArm = lam arm.
          match arm.patF env target with Some env
          then Some (arm.bodyF env st)
          else None () in
        match findMap runArm arms with Some res
        then res
        else error "Inexhaustive match"

  sem pegInstrToString firstVRef += | IMatch x ->
    let armToString = lam arm.
      match arm with (pat, instrs, vals) in
      let armVRef = addi firstVRef (length (collectPatNames pat)) in
      join
        [ "\n      | ", pat2str pat, " ->\n"
        , pegInstrsToString "        " armVRef instrs
        , "        out ", pegValsToString vals
        ] in
    ( foldl (lam acc. lam arm. maxi acc (length arm.2)) 0 x.arms
    , join
      [ "match ", vrefToString x.target
      , strJoin "" (map armToString x.arms)
      ]
    )
end

lang PEvalGraphInt = PEvalGraphConst + IntAst
  syn PEGVal += | VInt Int

  sem mkDeltaF += | CInt {val = i} -> VInt i

  sem cmpPEGValH += | (VInt a, VInt b) -> subi a b

  sem pegGenPairs += | (VInt _, VInt _) -> true

  sem pegValTy += | VInt _ -> tyint_

  sem homogenizeValues replace st += | allVs & [VInt i] ++ vs ->
    if forAll (lam v. match v with VInt i2 then eqi i i2 else false) vs
    then (st, VInt i)
    else replace st allVs

  sem pegValToString += | VInt i -> int2string i
end

-- Small helper for `homogenizeValues` tests, which replaces each
-- difference with a fresh `VRef`, and returns the number of them
-- along with what each input had in their place. Only the index of a
-- `VRef` is compared, so its type does not matter here.
let _homogenizeTest = use PEvalGraph in
  lam homogenize. lam vs.
    let replace = lam acc. lam diff.
      match acc with (n, fillerss) in
      ((addi n 1, zipWith snoc fillerss diff), VRef {ty = tyunknown_, ref = n}) in
    match homogenize replace (0, map (lam. []) vs) vs
    with ((n, fillerss), v) in
    (n, v, fillerss)

let _homogenizeTestEq = lam cmp. lam l. lam r.
  match (l, r) with ((n1, v1, fs1), (n2, v2, fs2)) in
  let eqVal = lam a. lam b. eqi (cmp a b) 0 in
  and (eqi n1 n2) (and (eqVal v1 v2) (eqSeq (eqSeq eqVal) fs1 fs2))

utest
  use PEvalGraphInt in
  utest (_homogenizeTest homogenizeValues [VInt 1, VInt 1])
  with (0, VInt 1, [[], []])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphInt in
  utest (_homogenizeTest homogenizeValues [VInt 1, VInt 2])
  with (1, VRef {ty = tyint_, ref = 0}, [[VInt 1], [VInt 2]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphInt in
  utest (_homogenizeTest homogenizeValues [VInt 1, VRef {ty = tyint_, ref = 7}])
  with
    ( 1
    , VRef {ty = tyint_, ref = 0}
    , [[VInt 1], [VRef {ty = tyint_, ref = 7}]]
    )
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphIntPat = PEvalGraphInt + IntPat
  sem mkPatF += | PatInt x ->
    let i = x.val in
    lam env. lam val.
      match val with VInt i2 then
        if eqi i i2
        then Some env
        else None ()
      else None ()
end

lang PEvalGraphChar = PEvalGraphConst + CharAst + CharCmp
  syn PEGVal += | VChar Char

  sem mkDeltaF += | CChar {val = c} -> VChar c

  sem cmpPEGValH += | (VChar a, VChar b) -> subi (char2int a) (char2int b)

  sem pegGenPairs += | (VChar a, VChar b) -> eqc a b

  sem pegValTy += | VChar _ -> tychar_

  sem homogenizeValues replace st += | allVs & [VChar c] ++ vs ->
    if forAll (lam v. match v with VChar c2 then eqc c c2 else false) vs
    then (st, VChar c)
    else replace st allVs

  sem pegValToString += | VChar c -> join ["\'", [c], "\'"]
end

utest
  use PEvalGraphChar in
  utest (_homogenizeTest homogenizeValues [VChar 'a', VChar 'a'])
  with (0, VChar 'a', [[], []])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphChar in
  utest (_homogenizeTest homogenizeValues [VChar 'a', VChar 'b'])
  with (1, VRef {ty = tychar_, ref = 0}, [[VChar 'a'], [VChar 'b']])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphCharPat = PEvalGraphChar + CharPat
  sem mkPatF += | PatChar x ->
    let c = x.val in
    lam env. lam val.
      match val with VChar c2 then
        if eqc c c2
        then Some env
        else None ()
      else None ()
end

lang PEvalGraphFloat = PEvalGraphConst + FloatAst + FloatCmp
  syn PEGVal += | VFloat Float

  sem mkDeltaF += | CFloat {val = f} -> VFloat f

  sem cmpPEGValH += | (VFloat a, VFloat b) ->
    if ltf a b then negi 1 else if ltf b a then 1 else 0

  sem pegGenPairs += | (VFloat _, VFloat _) -> true

  sem pegValTy += | VFloat _ -> tyfloat_

  sem homogenizeValues replace st += | allVs & [VFloat f] ++ vs ->
    if forAll (lam v. match v with VFloat f2 then eqf f f2 else false) vs
    then (st, VFloat f)
    else replace st allVs

  sem pegValToString += | VFloat f -> float2string f
end

utest
  use PEvalGraphFloat in
  utest (_homogenizeTest homogenizeValues [VFloat 1.5, VFloat 1.5])
  with (0, VFloat 1.5, [[], []])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphFloat in
  utest (_homogenizeTest homogenizeValues [VFloat 1.5, VFloat 2.5])
  with (1, VRef {ty = tyfloat_, ref = 0}, [[VFloat 1.5], [VFloat 2.5]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphBool = PEvalGraphConst + BoolAst + BoolCmp
  syn PEGVal += | VBool Bool

  sem mkDeltaF += | CBool {val = b} -> VBool b

  sem cmpPEGValH += | (VBool a, VBool b) ->
    subi (if a then 1 else 0) (if b then 1 else 0)

  sem pegGenPairs += | (VBool a, VBool b) -> eqBool a b

  sem pegValTy += | VBool _ -> tybool_

  sem homogenizeValues replace st += | allVs & [VBool b] ++ vs ->
    if forAll (lam v. match v with VBool b2 then eqBool b b2 else false) vs
    then (st, VBool b)
    else replace st allVs

  sem pegValToString += | VBool b -> if b then "true" else "false"
end

utest
  use PEvalGraphBool in
  utest (_homogenizeTest homogenizeValues [VBool true, VBool true])
  with (0, VBool true, [[], []])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphBool in
  utest (_homogenizeTest homogenizeValues [VBool true, VBool false])
  with (1, VRef {ty = tybool_, ref = 0}, [[VBool true], [VBool false]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphBoolPat = PEvalGraphBool + BoolPat
  sem mkPatF += | PatBool x ->
    let b = x.val in
    lam env. lam val.
      match val with VBool b2 then
        if eqBool b b2
        then Some env
        else None ()
      else None ()
end

lang PEvalGraphData = PEvalGraph + DataAst + DataDeclAst
  syn PEGVal += | VConApp {ty : Type, ident : Name, body : PEGVal}

  sem mkEvalF += | TmConApp x ->
    let body = mkEvalF x.body in
    lam env. lam st.
      match body env st with (st, body) in
      (st, VConApp {ty = pegSubstTy env x.ty, ident = x.ident, body = body})

  sem mkEvalDeclF += | DeclConDef _ -> lam env. lam st. (st, env)

  sem smapAccumL_PEGVal_PEGVal f acc += | VConApp x ->
    match f acc x.body with (acc, body) in
    (acc, VConApp {x with body = body})

  sem cmpPEGValH += | (VConApp a, VConApp b) ->
    let res = nameCmp a.ident b.ident in
    if neqi res 0 then res else
    cmpPEGVal a.body b.body

  sem pegGenPairs += | (VConApp a, VConApp b) ->
    if nameEq a.ident b.ident then pegGenEmbeds a.body b.body else false

  sem pegValTy += | VConApp x -> x.ty

  sem homogenizeValues replace st += | allVs & [VConApp x] ++ _ ->
    let check = lam v.
      match v with VConApp x2
      then if nameEq x.ident x2.ident
        then Some x2.body
        else None ()
      else None () in
    match optionMapM check allVs with Some vs then
      match homogenizeValues replace st vs with (st, v) in
      (st, VConApp {x with body = v})
    else replace st allVs

  sem pegValToString += | VConApp x ->
    join [nameGetStr x.ident, " (", pegValToString x.body, ")"]
end

utest
  use PEvalGraphData in
  let ident = nameSym "Foo" in
  let mk = lam r.
    VConApp {ty = tyunknown_, ident = ident, body = VRef {ty = tyint_, ref = r}} in
  utest (_homogenizeTest homogenizeValues [mk 3, mk 4])
  with
    ( 1
    , mk 0
    , [[VRef {ty = tyint_, ref = 3}], [VRef {ty = tyint_, ref = 4}]]
    )
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphData in
  let mk = lam str.
    VConApp
    { ty = tyunknown_
    , ident = nameSym str
    , body = VRef {ty = tyint_, ref = 3}
    } in
  let a = mk "Foo" in
  let b = mk "Bar" in
  utest (_homogenizeTest homogenizeValues [a, b])
  with (1, VRef {ty = tyunknown_, ref = 0}, [[a], [b]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphDataPat = PEvalGraph + DataPat + PEvalGraphData + NamedPat
  sem mkPatF +=
  | PatCon (x & {subpat = PatNamed {ident = PWildcard _}}) ->
    let ident = x.ident in
    lam env. lam val.
      match val with VConApp {ident = n} then
        if nameEq ident n
        then Some env
        else None ()
      else None ()
  | PatCon (x & {subpat = PatNamed {ident = PName n}}) ->
    let ident = x.ident in
    let s = nameToSymInt [x.info] "Unsymbolized PatCon subpattern in mkPatF!" n in
    lam env. lam val.
      match val with VConApp {ident = n, body = body} then
        if nameEq ident n
        then Some {env with values = Cons ((s, body), env.values)}
        else None ()
      else None ()
end

lang PEvalGraphRecord = PEvalGraph + RecordAst
  syn PEGVal += | VRecord {ty : Type, bindings : Map SID PEGVal}

  sem mkEvalF += | TmRecord x ->
    let bindings = mapMap mkEvalF x.bindings in
    lam env. lam st.
      match mapMapAccum (lam st. lam. lam f. f env st) st bindings
      with (st, bindings) in
      (st, VRecord {ty = pegSubstTy env x.ty, bindings = bindings})

  sem smapAccumL_PEGVal_PEGVal f acc += | VRecord x ->
    match mapMapAccum (lam acc. lam. lam v. f acc v) acc x.bindings
    with (acc, bindings) in
    (acc, VRecord {x with bindings = bindings})

  sem cmpPEGValH += | (VRecord a, VRecord b) ->
    mapCmp cmpPEGVal a.bindings b.bindings

  sem pegGenPairs += | (VRecord a, VRecord b) ->
    mapEq pegGenEmbeds a.bindings b.bindings

  sem pegValTy += | VRecord x -> x.ty

  sem homogenizeValues replace st += | allVs & [VRecord x] ++ _ ->
    let check = lam v.
      match v with VRecord x2 then Some x2.bindings else None () in
    match optionMapM check allVs with Some bindingss then
      let merge = lam a. lam b.
        match (a, b) with (Some a, Some b)
        then Some (concat a b)
        else error "Records of differing shape in homogenizeValues!" in
      let columns = foldl
        (lam acc. lam bindings. mapMerge merge acc (mapMap (lam v. [v]) bindings))
        (mapMap (lam. []) x.bindings)
        bindingss in
      match mapMapAccum (lam st. lam. homogenizeValues replace st) st columns
      with (st, bindings) in
      (st, VRecord {x with bindings = bindings})
    else replace st allVs

  sem pegValToString += | VRecord x -> join
    [ "{"
    , strJoin ", "
      (map
        (lam b. join [sidToString b.0, " = ", pegValToString b.1])
        (mapBindings x.bindings))
    , "}"
    ]
end

utest
  use PEvalGraphRecord in
  let mk = lam r. VRecord
    { ty = tyunknown_
    , bindings = mapFromSeq cmpSID [(stringToSid "a", VRef {ty = tyint_, ref = r})]
    } in
  utest (_homogenizeTest homogenizeValues [mk 3, mk 4])
  with
    ( 1
    , mk 0
    , [[VRef {ty = tyint_, ref = 3}], [VRef {ty = tyint_, ref = 4}]]
    )
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphRecord in
  -- NOTE(vipa, 2026-09-16): Having more than one differing field
  -- makes the result depend on the order of stringids, which we can't
  -- depend on. The invariant tests later on are not affected by this.
  let mk = lam r. VRecord
    { ty = tyunknown_
    , bindings = mapFromSeq cmpSID
      [ (stringToSid "a", VRecord {ty = tyunknown_, bindings = mapEmpty cmpSID})
      , (stringToSid "b", VRef {ty = tyint_, ref = r})
      ]
    } in
  utest (_homogenizeTest homogenizeValues [mk 2, mk 3])
  with
    ( 1
    , mk 0
    , [[VRef {ty = tyint_, ref = 2}], [VRef {ty = tyint_, ref = 3}]]
    )
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphRecordPat = PEvalGraphRecord + RecordPat + NamedPat
  sem mkPatF += | PatRecord x ->
    let getSymInt = lam pat.
      match pat with PatNamed {ident = PName n}
      then Some (nameToSymInt [x.info] "Unsymbolized PatRecord subpattern in mkPatF!" n)
      else None () in
    let bindings = mapBindings (mapMapOption getSymInt x.bindings) in
    lam env. lam val.
      match val with VRecord v then
        let values = foldl
          (lam values. lam pair. Cons ((pair.1, mapFindExn pair.0 v.bindings), values))
          env.values
          bindings in
        Some {env with values = values}
      else None ()
end

lang PEvalGraphSeq = PEvalGraph + SeqAst + SeqTypeAst
  syn PEGVal += | VSeq {ty : Type, vals : [PEGVal]}

  sem mkEvalF += | TmSeq x ->
    let vals = map mkEvalF x.tms in
    lam env. lam st.
      match mapAccumL (lam st. lam v. v env st) st vals with (st, vals) in
      (st, VSeq {ty = pegSubstTy env x.ty, vals = vals})

  sem smapAccumL_PEGVal_PEGVal f acc += | VSeq x ->
    match mapAccumL f acc x.vals with (acc, vals) in
    (acc, VSeq {x with vals = vals})

  sem cmpPEGValH += | (VSeq a, VSeq b) -> seqCmp cmpPEGVal a.vals b.vals

  -- Matching each element as early as possible finds an embedding in
  -- a subsequence whenever there is one
  sem pegGenPairs += | (VSeq a, VSeq b) ->
    recursive let work = lam ls. lam rs.
      match ls with [l] ++ lsTail then
        match rs with [r] ++ rsTail then
          if pegGenEmbeds l r then work lsTail rsTail else work ls rsTail
        else false
      else true in
    work a.vals b.vals

  sem pegValTy += | VSeq x -> x.ty

  sem homogenizeValues replace st += | allVs & [VSeq x] ++ _ ->
    let count = length x.vals in
    let check = lam v.
      match v with VSeq x2
      then if eqi count (length x2.vals) then Some x2.vals else None ()
      else None () in
    match optionMapM check allVs with Some valss then
      match mapAccumL (homogenizeValues replace) st (transpose valss)
      with (st, vals) in
      (st, VSeq {x with vals = vals})
    else replace st allVs

  sem pegValToString += | VSeq x ->
    join ["[", strJoin ", " (map pegValToString x.vals), "]"]
end

utest
  use PEvalGraphSeq in
  let mk = lam r. VSeq
    { ty = tyunknown_
    , vals = [VRef {ty = tyint_, ref = 1}, VRef {ty = tyint_, ref = r}]
    } in
  utest (_homogenizeTest homogenizeValues [mk 2, mk 3])
  with
    ( 2
    , VSeq
      { ty = tyunknown_
      , vals = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
      }
    , [ [VRef {ty = tyint_, ref = 1}, VRef {ty = tyint_, ref = 2}]
      , [VRef {ty = tyint_, ref = 1}, VRef {ty = tyint_, ref = 3}]
      ]
    )
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphSeq in
  let a = VSeq {ty = tyunknown_, vals = [VRef {ty = tyint_, ref = 1}]} in
  let b = VSeq {ty = tyunknown_, vals = []} in
  utest (_homogenizeTest homogenizeValues [a, b])
  with (1, VRef {ty = tyunknown_, ref = 0}, [[a], [b]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphArith = PEvalGraphInt + PEvalGraphConst + ArithIntAst
  sem mkDeltaF +=
  | c & CAddi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (addi a b))
    else None ())
  | c & CSubi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (subi a b))
    else None ())
  | c & CMuli _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (muli a b))
    else None ())
  | c & CDivi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (divi a b))
    else None ())
  | c & CModi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (modi a b))
    else None ())
  | c & CNegi _ -> deltaF c (lam args.
    match args with [VInt a]
    then Some (VInt (negi a))
    else None ())
end

lang PEvalGraphIO = PEvalGraph + PEvalGraphConst + IOAst
  sem mkDeltaF +=
  | c & CReadLine _ -> residualDeltaF c
  | c & CReadBytesAsString _ -> residualDeltaF c
  | c & (CPrint _ | CPrintError _ | CDPrint _ | CFlushStdout _
        | CFlushStderr _) ->
    residualDeltaF c
end

lang PEvalGraphSymb = PEvalGraphInt + SymbAst + SymbCmp
  syn PEGVal += | VSymb Symbol

  sem mkDeltaF +=
  | CSymb {val = s} -> VSymb s
  | c & CGensym _ ->
    residualDeltaF c
  | c & CSym2hash _ -> deltaF c (lam args.
    match args with [VSymb s]
    then Some (VInt (sym2hash s))
    else None ())

  sem cmpPEGValH += | (VSymb a, VSymb b) -> subi (sym2hash a) (sym2hash b)

  sem pegGenPairs += | (VSymb _, VSymb _) -> true

  sem pegValTy += | VSymb _ -> ntycon_ (mapFindExn "Symbol" builtinTypeNames)

  sem homogenizeValues replace st += | allVs & [VSymb s] ++ vs ->
    if forAll (lam v. match v with VSymb s2 then eqsym s s2 else false) vs
    then (st, VSymb s)
    else replace st allVs

  sem pegValToString += | VSymb s -> concat "sym" (int2string (sym2hash s))

end

utest
  use PEvalGraphSymb in
  let s = gensym () in
  utest (_homogenizeTest homogenizeValues [VSymb s, VSymb s])
  with (0, VSymb s, [[], []])
  using _homogenizeTestEq cmpPEGVal
in () with ()

utest
  use PEvalGraphSymb in
  let s1 = gensym () in
  let s2 = gensym () in
  utest (_homogenizeTest homogenizeValues [VSymb s1, VSymb s2])
  with (1, VRef {ty = pegValTy (VSymb s1), ref = 0}, [[VSymb s1], [VSymb s2]])
  using _homogenizeTestEq cmpPEGVal
in () with ()

lang PEvalGraphShiftInt = PEvalGraphInt + ShiftIntAst
  sem mkDeltaF +=
  | c & CSlli _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (slli a b))
    else None ())
  | c & CSrli _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (srli a b))
    else None ())
  | c & CSrai _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VInt (srai a b))
    else None ())
end

lang PEvalGraphArithFloat = PEvalGraphFloat + ArithFloatAst
  sem mkDeltaF +=
  | c & CAddf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VFloat (addf a b))
    else None ())
  | c & CSubf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VFloat (subf a b))
    else None ())
  | c & CMulf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VFloat (mulf a b))
    else None ())
  | c & CDivf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VFloat (divf a b))
    else None ())
  | c & CNegf _ -> deltaF c (lam args.
    match args with [VFloat a]
    then Some (VFloat (negf a))
    else None ())
end

lang PEvalGraphFloatIntConversion =
  PEvalGraphInt + PEvalGraphFloat + FloatIntConversionAst

  sem mkDeltaF +=
  | c & CFloorfi _ -> deltaF c (lam args.
    match args with [VFloat a]
    then Some (VInt (floorfi a))
    else None ())
  | c & CCeilfi _ -> deltaF c (lam args.
    match args with [VFloat a]
    then Some (VInt (ceilfi a))
    else None ())
  | c & CRoundfi _ -> deltaF c (lam args.
    match args with [VFloat a]
    then Some (VInt (roundfi a))
    else None ())
  | c & CInt2float _ -> deltaF c (lam args.
    match args with [VInt a]
    then Some (VFloat (int2float a))
    else None ())
end

lang PEvalGraphIntCharConversion =
  PEvalGraphInt + PEvalGraphChar + IntCharConversionAst

  sem mkDeltaF +=
  | c & CInt2Char _ -> deltaF c (lam args.
    match args with [VInt a]
    then Some (VChar (int2char a))
    else None ())
  | c & CChar2Int _ -> deltaF c (lam args.
    match args with [VChar a]
    then Some (VInt (char2int a))
    else None ())
end

lang PEvalGraphFloatStringConversion =
  PEvalGraphSeq + PEvalGraphChar + PEvalGraphFloat + PEvalGraphBool +
  FloatStringConversionAst

  sem pegValStr : PEGVal -> Option String
  sem pegValStr =
  | VSeq x -> optionMapM (lam v. match v with VChar c then Some c else None ()) x.vals
  | _ -> None ()

  sem pegStrVal : String -> PEGVal
  sem pegStrVal = | s -> VSeq {ty = tystr_, vals = map (lam c. VChar c) s}

  sem mkDeltaF +=
  | c & CStringIsFloat _ -> deltaF c (lam args.
    match args with [a] then
      match pegValStr a with Some s
      then Some (VBool (stringIsFloat s))
      else None ()
    else None ())
  | c & CString2float _ -> deltaF c (lam args.
    match args with [a] then
      match pegValStr a with Some s
      then Some (VFloat (string2float s))
      else None ()
    else None ())
  | c & CFloat2string _ -> deltaF c (lam args.
    match args with [VFloat a]
    then Some (pegStrVal (float2string a))
    else None ())
end

lang PEvalGraphCmpInt = PEvalGraphInt + PEvalGraphBool + CmpIntAst
  sem mkDeltaF +=
  | c & CEqi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (eqi a b))
    else None ())
  | c & CNeqi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (neqi a b))
    else None ())
  | c & CLti _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (lti a b))
    else None ())
  | c & CGti _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (gti a b))
    else None ())
  | c & CLeqi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (leqi a b))
    else None ())
  | c & CGeqi _ -> deltaF c (lam args.
    match args with [VInt a, VInt b]
    then Some (VBool (geqi a b))
    else None ())
end

lang PEvalGraphCmpFloat = PEvalGraphFloat + PEvalGraphBool + CmpFloatAst
  sem mkDeltaF +=
  | c & CEqf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (eqf a b))
    else None ())
  | c & CNeqf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (neqf a b))
    else None ())
  | c & CLtf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (ltf a b))
    else None ())
  | c & CGtf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (gtf a b))
    else None ())
  | c & CLeqf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (leqf a b))
    else None ())
  | c & CGeqf _ -> deltaF c (lam args.
    match args with [VFloat a, VFloat b]
    then Some (VBool (geqf a b))
    else None ())
end

lang PEvalGraphCmpChar = PEvalGraphChar + PEvalGraphBool + CmpCharAst
  sem mkDeltaF +=
  | c & CEqc _ -> deltaF c (lam args.
    match args with [VChar a, VChar b]
    then Some (VBool (eqc a b))
    else None ())
end

lang PEvalGraphCmpSymb = PEvalGraphSymb + PEvalGraphBool + CmpSymbAst
  sem mkDeltaF +=
  | c & CEqsym _ -> deltaF c (lam args.
    match args with [VSymb a, VSymb b]
    then Some (VBool (eqsym a b))
    else None ())
end

lang PEvalGraphSeqOp =
  PEvalGraphSeq + PEvalGraphInt + PEvalGraphBool + PEvalGraphRecord +
  SeqOpAst + FunTypeAst

  sem mkDeltaF +=
  | c & CGet _ -> deltaF c (lam args.
    match args with [VSeq s, VInt i]
    then Some (get s.vals i)
    else None ())
  | c & CSet _ -> deltaF c (lam args.
    match args with [VSeq s, VInt i, v]
    then Some (VSeq {s with vals = set s.vals i v})
    else None ())
  | c & CCons _ -> deltaF c (lam args.
    match args with [v, VSeq s]
    then Some (VSeq {s with vals = cons v s.vals})
    else None ())
  | c & CSnoc _ -> deltaF c (lam args.
    match args with [VSeq s, v]
    then Some (VSeq {s with vals = snoc s.vals v})
    else None ())
  | c & CConcat _ -> deltaF c (lam args.
    match args with [VSeq a, VSeq b]
    then Some (VSeq {a with vals = concat a.vals b.vals})
    else None ())
  | c & CLength _ -> deltaF c (lam args.
    match args with [VSeq s]
    then Some (VInt (length s.vals))
    else None ())
  | c & CReverse _ -> deltaF c (lam args.
    match args with [VSeq s]
    then Some (VSeq {s with vals = reverse s.vals})
    else None ())
  | c & CHead _ -> deltaF c (lam args.
    match args with [VSeq s] then
      match s.vals with [v] ++ _
      then Some v
      else None ()
    else None ())
  | c & CTail _ -> deltaF c (lam args.
    match args with [VSeq s] then
      match s.vals with [_] ++ rest
      then Some (VSeq {s with vals = rest})
      else None ()
    else None ())
  | c & CNull _ -> deltaF c (lam args.
    match args with [VSeq s]
    then Some (VBool (null s.vals))
    else None ())
  | c & CSubsequence _ -> deltaF c (lam args.
    match args with [VSeq s, VInt off, VInt n]
    then Some (VSeq {s with vals = subsequence s.vals off n})
    else None ())
  | c & CSplitAt _ -> deltaF c (lam args.
    match args with [VSeq s, VInt i] then
      match splitAt s.vals i with (l, r) in
      Some (VRecord
        { ty = tytuple_ [s.ty, s.ty]
        , bindings = mapFromSeq cmpSID
          [ (stringToSid "0", VSeq {s with vals = l})
          , (stringToSid "1", VSeq {s with vals = r})
          ]
        })
    else None ())
end

lang PEvalGraphSeqHigherOrderOp = PEvalGraphSeqOp
  sem _seqElemTy : Type -> Type
  sem _seqElemTy = | ty ->
    match unwrapType ty with TySeq x in
    x.ty

  sem _vunit : Type -> PEGVal
  sem _vunit = | ty -> VRecord {ty = ty, bindings = mapEmpty cmpSID}

  sem _wrongArity : all a. Const -> a
  sem _wrongArity = | c ->
    error (join
      ["Wrong number of arguments to ", getConstStringCode 0 c, " in mkDeltaF!"])

  sem mkDeltaF +=
  | c & CMap _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, seq] then
      let elemTy = _seqElemTy retTy in
      switch seq
      case VSeq s then
        match mapAccumL (lam st. lam x. applyF env st elemTy (f, [x])) st s.vals
        with (st, vals) in
        (st, VSeq {ty = retTy, vals = vals})
      case VRef r then
        match pegFunArg env st elemTy [_seqElemTy r.ty] f with (st, fArg) in
        pegEmit retTy st (IConstFCall {const = c, args = [Left fArg, Right seq]})
      end
    else _wrongArity c)

  | c & CMapi _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, seq] then
      let elemTy = _seqElemTy retTy in
      switch seq
      case VSeq s then
        let step = lam acc. lam x.
          match acc with (st, i) in
          match applyF env st elemTy (f, [VInt i, x]) with (st, v) in
          ((st, addi i 1), v) in
        match mapAccumL step (st, 0) s.vals with ((st, _), vals) in
        (st, VSeq {ty = retTy, vals = vals})
      case VRef r then
        match pegFunArg env st elemTy [tyint_, _seqElemTy r.ty] f
        with (st, fArg) in
        pegEmit retTy st (IConstFCall {const = c, args = [Left fArg, Right seq]})
      end
    else _wrongArity c)

  | c & CIter _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, seq] then
      switch seq
      case VSeq s then
        match mapAccumL (lam st. lam x. applyF env st retTy (f, [x])) st s.vals
        with (st, _) in
        (st, _vunit retTy)
      case VRef r then
        match pegFunArg env st retTy [_seqElemTy r.ty] f with (st, fArg) in
        pegEmit retTy st (IConstFCall {const = c, args = [Left fArg, Right seq]})
      end
    else _wrongArity c)

  | c & CIteri _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, seq] then
      switch seq
      case VSeq s then
        let step = lam acc. lam x.
          match acc with (st, i) in
          match applyF env st retTy (f, [VInt i, x]) with (st, v) in
          ((st, addi i 1), v) in
        match mapAccumL step (st, 0) s.vals with ((st, _), _) in
        (st, _vunit retTy)
      case VRef r then
        match pegFunArg env st retTy [tyint_, _seqElemTy r.ty] f
        with (st, fArg) in
        pegEmit retTy st (IConstFCall {const = c, args = [Left fArg, Right seq]})
      end
    else _wrongArity c)

  | c & CFoldl _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, acc, seq] then
      switch seq
      case VSeq s then
        foldl (lam p. lam x. applyF env p.0 retTy (f, [p.1, x])) (st, acc) s.vals
      case VRef r then
        match pegFunArg env st retTy [retTy, _seqElemTy r.ty] f with (st, fArg) in
        pegEmit retTy st
          (IConstFCall {const = c, args = [Left fArg, Right acc, Right seq]})
      end
    else _wrongArity c)

  | c & CFoldr _ -> VConstF (lam env. lam st. lam retTy. lam args.
    match args with [f, acc, seq] then
      switch seq
      case VSeq s then
        foldr (lam x. lam p. applyF env p.0 retTy (f, [x, p.1])) (st, acc) s.vals
      case VRef r then
        match pegFunArg env st retTy [_seqElemTy r.ty, retTy] f with (st, fArg) in
        pegEmit retTy st
          (IConstFCall {const = c, args = [Left fArg, Right acc, Right seq]})
      end
    else _wrongArity c)

  | c & (CCreate _ | CCreateList _ | CCreateRope _) ->
    VConstF (lam env. lam st. lam retTy. lam args.
      match args with [n, f] then
        let elemTy = _seqElemTy retTy in
        switch n
        case VInt n then
          match mapAccumL
            (lam st. lam i. applyF env st elemTy (f, [VInt i]))
            st (create n (lam i. i))
          with (st, vals) in
          (st, VSeq {ty = retTy, vals = vals})
        case VRef _ then
          match pegFunArg env st elemTy [tyint_] f with (st, fArg) in
          pegEmit retTy st (IConstFCall {const = c, args = [Right n, Left fArg]})
        end
      else _wrongArity c)
end

lang PEvalGraphFileOp = PEvalGraphConst + FileOpAst
  sem mkDeltaF +=
  | c & CFileRead _ -> residualDeltaF c
  | c & CFileExists _ -> residualDeltaF c
  | c & (CFileWrite _ | CFileDelete _) -> residualDeltaF c
end

lang PEvalGraphSys = PEvalGraphConst + SysAst
  sem mkDeltaF +=
  | c & CCommand _ -> residualDeltaF c
  | c & CArgv _ -> residualDeltaF c
  | c & (CExit _ | CError _ | CExec _) -> residualDeltaF c
end

lang PEvalGraphTime = PEvalGraphConst + TimeAst
  sem mkDeltaF +=
  | c & CWallTimeMs _ -> residualDeltaF c
  | c & CSleepMs _ -> residualDeltaF c
end

lang PEvalGraphRandomNumberGenerator =
  PEvalGraphConst + RandomNumberGeneratorAst

  sem mkDeltaF +=
  | c & CRandIntU _ -> residualDeltaF c
  | c & CRandSetSeed _ -> residualDeltaF c
end

lang PEvalGraphConTag = PEvalGraphConst + ConTagAst
  sem mkDeltaF += | c & CConstructorTag _ -> residualDeltaF c
end

lang PEvalGraphTest =
  PEvalGraphDecl + PEvalGraphLam + PEvalGraphLet + PEvalGraphRecLets +
  PEvalGraphType + PEvalGraphVar + PEvalGraphApp + PEvalGraphConst +
  PEvalGraphExt +
  PEvalGraphMatch + PEvalGraphInt + PEvalGraphIntPat +
  PEvalGraphChar + PEvalGraphCharPat + PEvalGraphFloat + PEvalGraphBool +
  PEvalGraphBoolPat + PEvalGraphData + PEvalGraphDataPat +
  PEvalGraphRecord + PEvalGraphRecordPat + PEvalGraphSeq + PEvalGraphArith +
  PEvalGraphIO + PEvalGraphSymb + PEvalGraphShiftInt + PEvalGraphArithFloat +
  PEvalGraphFloatIntConversion + PEvalGraphIntCharConversion +
  PEvalGraphFloatStringConversion + PEvalGraphCmpInt + PEvalGraphCmpFloat +
  PEvalGraphCmpChar + PEvalGraphCmpSymb + PEvalGraphSeqOp +
  PEvalGraphSeqHigherOrderOp +
  PEvalGraphFileOp + PEvalGraphSys + PEvalGraphTime +
  PEvalGraphRandomNumberGenerator + PEvalGraphConTag + PEvalGraphOpaque +
  KeywordMakerOpaque +

  BootParser + MExprSym + MExprTypeCheck + MExprPrettyPrint

  -- Comparison of instructions, which only the tests below need. Note
  -- that this forces the return value of an `IBlockCall` that has
  -- one, which is only possible once every block has been forced and
  -- `finalBlocks` has been written, i.e. only for a result that came
  -- out of `callEvalF`.
  sem cmpPEGInstr : PEGInstr -> PEGInstr -> Int
  sem cmpPEGInstr a = | b -> cmpPEGInstrH (a, b)

  sem cmpPEGFunArg : PEGFunArg -> PEGFunArg -> Int
  sem cmpPEGFunArg l = | r ->
    let res = seqCmp cmpPEGVal l.params r.params in
    if neqi res 0 then res else
    let res = cmpPEGInstr l.instr r.instr in
    if neqi res 0 then res else cmpPEGVal l.ret r.ret

  sem cmpPEGInstrH : (PEGInstr, PEGInstr) -> Int
  sem cmpPEGInstrH =
  | (IConstCall a, IConstCall b) ->
    let res = cmpConst a.const b.const in
    if neqi res 0 then res else seqCmp cmpPEGVal a.args b.args
  | (IConstFCall a, IConstFCall b) ->
    let res = cmpConst a.const b.const in
    if neqi res 0 then res else
    seqCmp (eitherCmp cmpPEGFunArg cmpPEGVal) a.args b.args
  -- The bodies are compared as printed, so that their bound names
  -- need not have the same symbols
  | (IOpaque a, IOpaque b) ->
    let res = mapCmp (eitherCmp cmpPEGFunArg cmpPEGVal) a.bindings b.bindings in
    if neqi res 0 then res else cmpString (expr2str a.body) (expr2str b.body)
  | (IExtCall a, IExtCall b) ->
    let res = nameCmp a.ident b.ident in
    if neqi res 0 then res else seqCmp cmpPEGVal a.args b.args
  | (IBlockCall a, IBlockCall b) ->
    let res = nameCmp a.block b.block in
    if neqi res 0 then res else
    let res = seqCmp subi a.args b.args in
    if neqi res 0 then res else
    eitherCmp
      (lam l. lam r. cmpPEGVal (lazyForce l) (lazyForce r))
      (seqCmp cmpType)
      a.return
      b.return
  | (IMatch a, IMatch b) ->
    let res = subi a.target b.target in
    if neqi res 0 then res else
    let cmpArm = lam l. lam r.
      let res = cmpPat l.0 r.0 in
      if neqi res 0 then res else
      let res = seqCmp cmpPEGInstr l.1 r.1 in
      if neqi res 0 then res else seqCmp cmpPEGVal l.2 r.2 in
    seqCmp cmpArm a.arms b.arms
  | (a, b) ->
    let res = subi (constructorTag a) (constructorTag b) in
    if eqi res 0
    then error "Missing case in cmpPEGInstrH for instructions with equal indices."
    else res
end

mexpr

use PEvalGraphTest in


-- === Embedding values ===

let gseq_ : [PEGVal] -> PEGVal = lam vals. VSeq {ty = tyunknown_, vals = vals} in
let gcon_ : String -> PEGVal -> PEGVal = lam ident. lam body.
  VConApp {ty = tyunknown_, ident = nameNoSym ident, body = body} in

-- Values with an infinite domain always pair, others must be equal
utest pegGenEmbeds (VInt 1) (VInt 2) with true in
utest pegGenEmbeds (VFloat 1.0) (VFloat 2.0) with true in
utest pegGenEmbeds (VChar 'a') (VChar 'a') with true in
utest pegGenEmbeds (VChar 'a') (VChar 'b') with false in
utest pegGenEmbeds (VBool true) (VBool false) with false in
utest pegGenEmbeds (VInt 1) (VChar 'a') with false in

-- The needle may be found inside the haystack, and its sub-terms
-- inside the corresponding sub-terms of the haystack
utest pegGenEmbeds (gcon_ "Foo" (VChar 'a')) (gcon_ "Foo" (VChar 'a')) with true in
utest pegGenEmbeds (gcon_ "Foo" (VChar 'a')) (gcon_ "Bar" (VChar 'a')) with false in
utest pegGenEmbeds (gcon_ "Foo" (VChar 'a')) (gcon_ "Bar" (gcon_ "Foo" (VChar 'a'))) with true in
utest pegGenEmbeds (gcon_ "Foo" (VChar 'a')) (gcon_ "Foo" (gcon_ "Bar" (VChar 'a'))) with true in
utest pegGenEmbeds (gcon_ "Foo" (gcon_ "Bar" (VChar 'a'))) (gcon_ "Foo" (VChar 'a')) with false in

-- Sequences embed in any sequence containing them as a subsequence
utest pegGenEmbeds (gseq_ []) (gseq_ [VChar 'a']) with true in
utest pegGenEmbeds (gseq_ [VChar 'a', VChar 'c']) (gseq_ [VChar 'a', VChar 'b', VChar 'c']) with true in
utest pegGenEmbeds (gseq_ [VChar 'c', VChar 'a']) (gseq_ [VChar 'a', VChar 'b', VChar 'c']) with false in
utest pegGenEmbeds (gseq_ [VChar 'a', VChar 'a']) (gseq_ [VChar 'a']) with false in
utest pegGenEmbeds (gseq_ [VChar 'a']) (gseq_ [gcon_ "Foo" (VChar 'a')]) with true in


-- === Homogenizing values ===

-- Homogenizes, then reconstructs each original value from the
-- homogenized one and its own fillers, which is the invariant
-- `homogenizeValues` is built for
let checkHomogenizationInvariant : [PEGVal] -> () = lam vs.
  recursive let reconstruct = lam fillers. lam v.
    match v with VRef {ref = idx}
    then get fillers idx
    else smap_PEGVal_PEGVal (reconstruct fillers) v in
  match _homogenizeTest homogenizeValues vs with (_, v, fillerss) in
  utest vs with map (lam fillers. reconstruct fillers v) fillerss
  using eqSeq (lam a. lam b. eqi (cmpPEGVal a b) 0)
  in ()
in

-- TODO(vipa, 2026-09-16): This bit is very much written for use with
-- PBT, but we don't have such a framework for now, so we test the
-- invariant with some particular examples instead

let vref_ : Int -> PEGVal = lam idx. VRef {ty = tyint_, ref = idx} in
let vseq_ : [PEGVal] -> PEGVal = lam vals. VSeq {ty = tyunknown_, vals = vals} in
let vcon_ : Name -> PEGVal -> PEGVal = lam ident. lam body.
  VConApp {ty = tyunknown_, ident = ident, body = body} in
let vrec2_ : PEGVal -> PEGVal -> PEGVal = lam a. lam b. VRecord
  { ty = tyunknown_
  , bindings = mapFromSeq cmpSID [(stringToSid "a", a), (stringToSid "b", b)]
  } in

let foo = nameSym "Foo" in
let bar = nameSym "Bar" in

-- Scalars, identical and differing
checkHomogenizationInvariant [VInt 1, VInt 1];
checkHomogenizationInvariant [VInt 1, VInt 2, VInt 3];
checkHomogenizationInvariant [VInt 1, vref_ 7];
checkHomogenizationInvariant [vref_ 7, vref_ 7];

-- Values of different shapes entirely, which homogenize to one hole
checkHomogenizationInvariant [VInt 1, VChar 'a'];
checkHomogenizationInvariant [vcon_ foo (VInt 1), vcon_ bar (VInt 1)];
checkHomogenizationInvariant [vseq_ [VInt 1], vseq_ []];

-- Two fields that both become holes, which pins the order the fillers
-- of a record are concatenated in
checkHomogenizationInvariant
  [ vrec2_ (vref_ 1) (vref_ 2)
  , vrec2_ (vref_ 3) (vref_ 4)
  ];

-- Constructors, sequences and records nested in each other
checkHomogenizationInvariant
  [ vseq_ [VInt 1, vcon_ foo (vref_ 2)]
  , vseq_ [VInt 1, vcon_ foo (vref_ 3)]
  ];
checkHomogenizationInvariant
  [ vrec2_ (vseq_ [VInt 1, vref_ 2]) (vcon_ foo (VInt 7))
  , vrec2_ (vseq_ [VInt 1, vref_ 3]) (vcon_ foo (VInt 7))
  , vrec2_ (vseq_ [VInt 4, vref_ 5]) (vcon_ foo (VInt 7))
  ];
checkHomogenizationInvariant
  [ vcon_ foo (vrec2_ (vseq_ [vref_ 1, VBool true]) (VFloat 1.5))
  , vcon_ foo (vrec2_ (vseq_ [vref_ 2, VBool false]) (VFloat 1.5))
  ];

-- A hole nested inside a value that is itself only reachable in some
-- of the inputs
checkHomogenizationInvariant
  [ vseq_ [vcon_ foo (vref_ 1), VInt 2]
  , vseq_ [vcon_ bar (vref_ 1), VInt 2]
  ];


-- === Test helpers ===

let prepare
  : String -> EvalF
  = lam src.
    mkTopEvalF
      (typeCheck
        (symbolize
          (constTransform (snoc builtin ("testResidual", CResidualIdentity ()))
            (makeKeywords
              (parseMExprStringExn defaultBootParserParseMExprStringArg src)))))
in

type InlineF = (PEGVal, [PEGVal]) -> Bool in

let inlineAll : InlineF = lam. true in
let inlineNone : InlineF = lam. false in

let callEvalFWith
  : InlineF -> EvalF -> (PEGState, PEGVal)
  = lam inline. lam f.
    let finalBlocks = mkThunk (lazy (lam. "finalBlocks")) in
    let initEnv : PEGEnv =
      { values = listEmpty
      , tyValues = mapEmpty nameCmp
      , finalBlocks = finalBlocks
      , inline = inline
      } in
    let initState : PEGState =
      { computedBlocks = mapEmpty cmpPEGBlockKey
      , requestedBlocks = mapEmpty cmpPEGBlockKey
      , instructions = []
      , nextVRef = 0
      , callStack = []
      } in
    match f initEnv initState with (st, val) in
    let st = forceAllBlocks st in
    finalBlocks.write
      (mapFromSeq nameCmp
        (map (lam b. (b.name, b)) (mapValues st.computedBlocks)));
    (st, val)
in

let callEvalF : EvalF -> (PEGState, PEGVal) = callEvalFWith inlineAll in

-- A test that writes down instructions and a value expects no blocks
-- at all, so this also checks that none were computed and that none
-- were left unforced; use `eqBlocksInstrAndVal` for a test that does
-- expect blocks
let eqInstrAndVal
  : (PEGState, PEGVal) -> ([PEGInstr], PEGVal) -> Bool
  = lam l. lam r.
    match (l, r) with ((st, val1), (instr, val2)) in
    if neqi (mapSize st.computedBlocks) 0 then false else
    if neqi (mapSize st.requestedBlocks) 0 then false else
    if neqi (seqCmp cmpPEGInstr st.instructions instr) 0 then false else
    eqi (cmpPEGVal val1 val2) 0
in

let ppInstrAndVal
  : (PEGState, PEGVal) -> ([PEGInstr], PEGVal) -> String
  = lam l. lam r.
    match l with (st, val) in
    join
      [ "\n  LHS:\n", pegInstrsToString "    " 0 st.instructions
      , "    value ", pegValToString val, "\n"
      , "    ", int2string (mapSize st.computedBlocks), " computed block(s), "
      , int2string (mapSize st.requestedBlocks), " unforced request(s)\n"
      , "  RHS:\n", pegInstrsToString "    " 0 r.0
      , "    value ", pegValToString r.1
      ]
in


-- A test cannot build the names of a parsed program, since they are
-- symbolized, so these de-symbolize every name that a comparison can
-- reach: the names in patterns, in values, and in the types of
-- values. Block names are left alone, `canonicalizeBlocks` deals with
-- those.
let desymbolizeName = lam n. nameNoSym (nameGetStr n) in

let desymbolizePatName = lam pn.
  match pn with PName n then PName (desymbolizeName n) else pn in

recursive let desymbolizePat : Pat -> Pat = lam pat.
  let pat = smap_Pat_Pat desymbolizePat pat in
  switch pat
  case PatNamed x then PatNamed {x with ident = desymbolizePatName x.ident}
  case PatCon x then PatCon {x with ident = desymbolizeName x.ident}
  case PatSeqEdge x then
    PatSeqEdge {x with middle = desymbolizePatName x.middle}
  case pat then pat
  end
in

let desymbolizeNames = lam names.
  setOfSeq nameCmp (map desymbolizeName (setToSeq names)) in

recursive let desymbolizeType : Type -> Type = lam ty.
  let ty = smap_Type_Type desymbolizeType ty in
  switch ty
  case TyCon x then TyCon {x with ident = desymbolizeName x.ident}
  case TyVar x then TyVar {x with ident = desymbolizeName x.ident}
  case TyAll x then TyAll {x with ident = desymbolizeName x.ident}
  case TyData x then TyData
    { x with
      universe = mapFromSeq nameCmp
        (map
          (lam b. (desymbolizeName b.0, desymbolizeNames b.1))
          (mapBindings x.universe))
    , cons = desymbolizeNames x.cons
    }
  case ty then ty
  end
in

recursive let desymbolizeVal : PEGVal -> PEGVal = lam val.
  let val = smap_PEGVal_PEGVal desymbolizeVal val in
  switch val
  case VRef x then VRef {x with ty = desymbolizeType x.ty}
  case VConApp x then VConApp
    {x with ty = desymbolizeType x.ty, ident = desymbolizeName x.ident}
  case VRecord x then VRecord {x with ty = desymbolizeType x.ty}
  case VSeq x then VSeq {x with ty = desymbolizeType x.ty}
  case val then val
  end
in

recursive let desymbolizeInstr : PEGInstr -> PEGInstr = lam instr.
  let desymbolizeArm = lam arm.
    ( desymbolizePat arm.0
    , map desymbolizeInstr arm.1
    , map desymbolizeVal arm.2
    ) in
  switch instr
  case IMatch x then IMatch {x with arms = map desymbolizeArm x.arms}
  case IConstCall x then IConstCall {x with args = map desymbolizeVal x.args}
  case IConstFCall x then IConstFCall
    { x with args = map
      (eitherBiMap
        (lam fArg : PEGFunArg.
          { params = map desymbolizeVal fArg.params
          , instr = desymbolizeInstr fArg.instr
          , ret = desymbolizeVal fArg.ret
          })
        desymbolizeVal)
      x.args
    }
  case IExtCall x then IExtCall
    {x with ident = desymbolizeName x.ident, args = map desymbolizeVal x.args}
  case IBlockCall x then IBlockCall
    {x with return = eitherMapRight (map desymbolizeType) x.return}
  case IOpaque x then
    let desymbolizeArg = eitherBiMap
      (lam fArg : PEGFunArg.
        { params = map desymbolizeVal fArg.params
        , instr = desymbolizeInstr fArg.instr
        , ret = desymbolizeVal fArg.ret
        })
      desymbolizeVal in
    IOpaque
    { x with bindings = mapFromSeq nameCmp
      (map
        (lam b. (desymbolizeName b.0, desymbolizeArg b.1))
        (mapBindings x.bindings))
    }
  case instr then instr
  end in

let desymbolizeBlock : PEGBlock -> PEGBlock = lam block.
  { block with
    params = map desymbolizeType block.params
  , instructions = map desymbolizeInstr block.instructions
  , retValue = desymbolizeVal block.retValue
  } in

let eqInstrAndValIgnoringSymbols
  : (PEGState, PEGVal) -> ([PEGInstr], PEGVal) -> Bool
  = lam l. lam r.
    match l with (st, val) in
    eqInstrAndVal
      ( {st with instructions = map desymbolizeInstr st.instructions}
      , desymbolizeVal val
      )
      (map desymbolizeInstr r.0, desymbolizeVal r.1)
in


-- === Comparing blocks ===

let cmpPEGBlock : PEGBlock -> PEGBlock -> Int = lam a. lam b.
  let res = nameCmp a.name b.name in
  if neqi res 0 then res else
  let res = seqCmp cmpType a.params b.params in
  if neqi res 0 then res else
  let res = seqCmp cmpPEGInstr a.instructions b.instructions in
  if neqi res 0 then res else
  let res = seqCmp subi a.toRet b.toRet in
  if neqi res 0 then res else
  cmpPEGVal a.retValue b.retValue
in

-- Every block is named by a fresh symbol with the same string, so a
-- test cannot write the names it expects, and desymbolizing would
-- merge all blocks into one. What distinguishes two blocks is only
-- where they are referenced, so this numbers them by first reference
-- -- instructions top to bottom, arms left to right, descending into
-- a block the first time its name appears -- and renames them
-- `block0`, `block1`, and so on, returning them in that same order.
-- A block that is never referenced has no position to be written down
-- in, and is thus left out; `eqBlocksInstrAndVal` checks the count so
-- that one cannot go unnoticed.
let canonicalizeBlocks
  : (PEGState, PEGVal) -> ([PEGInstr], [PEGBlock], PEGVal)
  = lam l.
    match l with (st, val) in
    let byName = mapFromSeq nameCmp
      (map (lam b. (b.name, b)) (mapValues st.computedBlocks)) in
    recursive let referenced = lam instr.
      switch instr
      case IMatch x then join (map (lam arm. join (map referenced arm.1)) x.arms)
      case IBlockCall x then [x.block]
      case IConstFCall x then
        join
          (map
            (eitherEither (lam fArg : PEGFunArg. referenced fArg.instr) (lam. []))
            x.args)
      case IOpaque x then
        join
          (map
            (eitherEither (lam fArg : PEGFunArg. referenced fArg.instr) (lam. []))
            (mapValues x.bindings))
      case _ then []
      end in
    recursive
      let visitInstrs = lam order. lam instrs.
        foldl visitName order (join (map referenced instrs))
      let visitName = lam order. lam name.
        if mapMem name order then order else
        let order = mapInsert name (mapSize order) order in
        match mapLookup name byName with Some block
        then visitInstrs order block.instructions
        else order
    in
    let order = visitInstrs (mapEmpty nameCmp) st.instructions in

    let rename = lam name.
      match mapLookup name order with Some i
      then nameNoSym (concat "block" (int2string i))
      else name in
    recursive let renameInstr = lam instr.
      switch instr
      case IMatch x then
        let renameArm = lam arm. (arm.0, map renameInstr arm.1, arm.2) in
        IMatch {x with arms = map renameArm x.arms}
      case IBlockCall x then IBlockCall {x with block = rename x.block}
      case IConstFCall x then IConstFCall
        { x with args =
          map
            (eitherMapLeft
              (lam fArg : PEGFunArg. {fArg with instr = renameInstr fArg.instr}))
            x.args
        }
      case IOpaque x then IOpaque
        { x with bindings =
          mapMap
            (eitherMapLeft
              (lam fArg : PEGFunArg. {fArg with instr = renameInstr fArg.instr}))
            x.bindings
        }
      case instr then instr
      end in
    let renameBlock = lam block.
      { block with
        name = rename block.name
      , instructions = map renameInstr block.instructions
      } in

    let blocks = map
      (lam pair. renameBlock (mapFindExn pair.0 byName))
      (sort (lam a. lam b. subi a.1 b.1) (mapBindings order)) in
    (map renameInstr st.instructions, blocks, val)
in

let eqBlocksInstrAndVal
  : (PEGState, PEGVal) -> ([PEGInstr], [PEGBlock], PEGVal) -> Bool
  = lam l. lam r.
    match canonicalizeBlocks l with (instrs, blocks, val) in
    if neqi (mapSize (l.0).requestedBlocks) 0 then false else
    if neqi (mapSize (l.0).computedBlocks) (length blocks) then false else
    if neqi (seqCmp cmpPEGInstr instrs r.0) 0 then false else
    if neqi (seqCmp cmpPEGBlock blocks r.1) 0 then false else
    eqi (cmpPEGVal val r.2) 0
in

let ppBlocksInstrAndVal
  : (PEGState, PEGVal) -> ([PEGInstr], [PEGBlock], PEGVal) -> String
  = lam l. lam r.
    match canonicalizeBlocks l with (instrs, blocks, val) in
    let unreachable = subi (mapSize (l.0).computedBlocks) (length blocks) in
    join
      [ "\n  LHS:\n", pegInstrsToString "    " 0 instrs
      , "    value ", pegValToString val, "\n"
      , strJoin "" (map pegBlockToString blocks)
      , if eqi unreachable 0 then "" else
        join
          [ "    (", int2string unreachable
          , " computed block(s) unreachable, thus not listed)\n"
          ]
      , if eqi (mapSize (l.0).requestedBlocks) 0 then "" else
        join
          [ "    (", int2string (mapSize (l.0).requestedBlocks)
          , " request(s) never forced)\n"
          ]
      , "  RHS:\n", pegInstrsToString "    " 0 r.0
      , "    value ", pegValToString r.2, "\n"
      , strJoin "" (map pegBlockToString r.1)
      ]
in

let eqBlocksInstrAndValIgnoringSymbols
  : (PEGState, PEGVal) -> ([PEGInstr], [PEGBlock], PEGVal) -> Bool
  = lam l. lam r.
    match l with (st, val) in
    eqBlocksInstrAndVal
      ( { st with
          instructions = map desymbolizeInstr st.instructions
        , computedBlocks = mapMap desymbolizeBlock st.computedBlocks
        }
      , desymbolizeVal val
      )
      (map desymbolizeInstr r.0, map desymbolizeBlock r.1, desymbolizeVal r.2)
in


-- === Value construction helpers ===

let vstr_ : String -> PEGVal = lam s.
  VSeq {ty = tystr_, vals = map (lam c. VChar c) s} in

let vunit_ : PEGVal = VRecord {ty = tyunit_, bindings = mapEmpty cmpSID} in

let vrecord_ : [(String, PEGVal)] -> PEGVal = lam bs.
  VRecord
  { ty = tyrecord_ (map (lam b. (b.0, pegValTy b.1)) bs)
  , bindings = mapFromSeq cmpSID (map (lam b. (stringToSid b.0, b.1)) bs)
  } in

-- A call to `testResidual`, which is most of the instructions a test
-- writes down
let residual_ : PEGVal -> PEGInstr = lam arg.
  IConstCall {const = CResidualIdentity (), args = [arg]} in

-- The name of the block, the `VRef`s passed to it, and the types of
-- the values it returns
let blockCall_ : String -> [VRef] -> [Type] -> PEGInstr
  = lam name. lam args. lam tys.
    IBlockCall {block = nameNoSym name, args = args, return = Right tys} in

-- As above, but for a call made while the block was still being
-- computed, which passes out the return value of the block as a whole
let lazyBlockCall_ : String -> [VRef] -> PEGVal -> PEGInstr
  = lam name. lam args. lam val.
    IBlockCall {block = nameNoSym name, args = args, return = Left (lazyPure val)} in

-- The name, the types of the parameters, the instructions, the
-- residual values returned, and how to build the return value from
-- them
let block_ : String -> [Type] -> [PEGInstr] -> [VRef] -> PEGVal -> PEGBlock
  = lam name. lam params. lam instructions. lam toRet. lam retValue.
    { name = nameNoSym name
    , params = params
    , instructions = instructions
    , toRet = toRet
    , retValue = retValue
    } in

-- Takes the name of the data type as well as the constructor, since
-- the type of a `VConApp` is compared
let vconapp_ : String -> String -> PEGVal -> PEGVal
  = lam tyIdent. lam ident. lam body.
    VConApp {ty = tycon_ tyIdent, ident = nameNoSym ident, body = body} in


-- === Folding and residualization ===

utest callEvalF (prepare (strJoin "\n"
  [ "addi 1 2"
  ]))
with
  ([], VInt 3)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "print \"foo\""
  ]))
with
  ( [ IConstCall {const = CPrint () , args = [vstr_ "foo"]}
    ]
  , VRef {ty = tyunit_, ref = 0}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let x = addi 1 2 in"
  , "print \"bar\";"
  , "muli x 2"
  ]))
with
  ( [ IConstCall {const = CPrint (), args = [vstr_ "bar"]}
    ]
  , VInt 6
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "muli (testResidual 3) 2"
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [VInt 3]}
    , IConstCall
      { const = CMuli ()
      , args = [VRef {ty = tyint_, ref = 0}, VInt 2]
      }
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "addf (testResidual 1.5) 2.5"
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [VFloat 1.5]}
    , IConstCall
      { const = CAddf ()
      , args = [VRef {ty = tyfloat_, ref = 0}, VFloat 2.5]
      }
    ]
  , VRef {ty = tyfloat_, ref = 1}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "concat (testResidual \"a\") \"b\""
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [vstr_ "a"]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "b"]
      }
    ]
  , VRef {ty = tystr_, ref = 1}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Externals ===

let ext_ : String -> [PEGVal] -> PEGInstr = lam name. lam args.
  IExtCall {ident = nameNoSym name, args = args} in

utest callEvalF (prepare (strJoin "\n"
  [ "external e : Float -> Float in"
  , "e 1.5"
  ]))
with
  ( [ ext_ "e" [VFloat 1.5]
    ]
  , VRef {ty = tyfloat_, ref = 0}
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- `!` marks the external as side-effecting, which changes nothing here; the
-- unmarked external above residualizes just the same
utest callEvalF (prepare (strJoin "\n"
  [ "external e! : Int -> Float -> Int in"
  , "addi (e 1 2.5) 3"
  ]))
with
  ( [ ext_ "e" [VInt 1, VFloat 2.5]
    , IConstCall
      { const = CAddi ()
      , args = [VRef {ty = tyint_, ref = 0}, VInt 3]
      }
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- An external that is not a function is a value, and residualizes
-- where it is declared
utest callEvalF (prepare (strJoin "\n"
  [ "external e : Int in"
  , "addi e 1"
  ]))
with
  ( [ ext_ "e" []
    , IConstCall
      { const = CAddi ()
      , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
      }
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in


-- === Sharing in the instruction graph ===

utest callEvalF (prepare (strJoin "\n"
  [ "let x = readLine () in"
  , "let y = readLine () in"
  , "concat x y"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, VRef {ty = tystr_, ref = 1}]
      }
    ]
  , VRef {ty = tystr_, ref = 2}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let x = readLine () in"
  , "concat x x"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, VRef {ty = tystr_, ref = 0}]
      }
    ]
  , VRef {ty = tystr_, ref = 1}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let x = readLine () in"
  , "let a = concat x \"a\" in"
  , "let b = concat x \"b\" in"
  , "concat a b"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "a"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "b"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 1}, VRef {ty = tystr_, ref = 2}]
      }
    ]
  , VRef {ty = tystr_, ref = 3}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Lambdas ===

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. concat a b in"
  , "let a = f \"a\" \"b\" in"
  , "let b = f (readLine ()) a in"
  , "concat a b"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "ab"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [vstr_ "ab", VRef {ty = tystr_, ref = 1}]
      }
    ]
  , VRef {ty = tystr_, ref = 2}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. lam y. addi x y in"
  , "f 1 2"
  ]))
with ([], VInt 3)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let x = \"outer\" in"
  , "let f = lam x. concat x \"!\" in"
  , "concat (f \"inner\") x"
  ]))
with ([], vstr_ "inner!outer")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let x = readLine () in"
  , "let f = lam y. concat x y in"
  , "concat (f \"a\") (f \"b\")"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "a"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "b"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 1}, VRef {ty = tystr_, ref = 2}]
      }
    ]
  , VRef {ty = tystr_, ref = 3}
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam. readLine () in"
  , "concat (f ()) (f ())"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, VRef {ty = tystr_, ref = 1}]
      }
    ]
  , VRef {ty = tystr_, ref = 2}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Recursive lets ===

utest callEvalF (prepare (strJoin "\n"
  [ "recursive let f = lam x. concat x \"!\" in"
  , "f \"a\""
  ]))
with ([], vstr_ "a!")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "recursive"
  , "  let f = lam x. g (concat x \"1\")"
  , "  let g = lam x. concat x \"2\""
  , "in"
  , "f \"a\""
  ]))
with ([], vstr_ "a12")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let g = lam x. concat x \"outer\" in"
  , "recursive"
  , "  let f = lam x. g (concat x \"-\")"
  , "  let g = lam x. concat x \"inner\""
  , "in"
  , "f \"a\""
  ]))
with ([], vstr_ "a-inner")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "recursive let f = lam x. concat x \"!\" in"
  , "concat (f (readLine ())) (f \"b\")"
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 0}, vstr_ "!"]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 1}, vstr_ "b!"]
      }
    ]
  , VRef {ty = tystr_, ref = 2}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Pattern matching ===

utest callEvalF (prepare (strJoin "\n"
  [ "let n = 2 in"
  , "match n with 0 then concat \"zero\" \"!\""
  , "else match n with 1 then concat \"one\" \"!\""
  , "else match n with 2 then concat \"two\" \"!\""
  , "else concat \"many\" \"!\""
  ]))
with ([], vstr_ "two!")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let n = 7 in"
  , "match n with 0 then concat \"zero\" \"!\""
  , "else match n with 1 then concat \"one\" \"!\""
  , "else concat \"many\" \"!\""
  ]))
with ([], vstr_ "many!")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let c = 'b' in"
  , "match c with 'a' then addi 1 0"
  , "else match c with 'b' then addi 2 0"
  , "else addi 3 0"
  ]))
with ([], VInt 2)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let b = false in"
  , "match b with true then addi 1 0 else addi 2 0"
  ]))
with ([], VInt 2)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let r = {a = \"x\", b = \"y\"} in"
  , "match r with {a = a, b = b} then concat b a"
  , "else concat \"no\" \"pe\""
  ]))
with ([], vstr_ "yx")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let r = {a = readLine (), b = \"y\"} in"
  , "match r with {b = b} then concat b \"!\""
  , "else concat \"no\" \"pe\""
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    ]
  , vstr_ "y!"
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "type Foo in"
  , "con Bar : Int -> Foo in"
  , "con Baz : Int -> Foo in"
  , "let x = Baz 4 in"
  , "match x with Bar n then addi n 1"
  , "else match x with Baz n then muli n 2"
  , "else addi 0 0"
  ]))
with ([], VInt 8)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "type Foo in"
  , "con Bar : Int -> Foo in"
  , "con Baz : Int -> Foo in"
  , "let x = Bar 4 in"
  , "match x with Baz _ then addi 0 1 else addi 0 2"
  ]))
with ([], VInt 2)
using eqInstrAndVal else ppInstrAndVal in


-- === Recursion ===

utest callEvalF (prepare (strJoin "\n"
  [ "recursive let rep = lam n. lam acc."
  , "  match n with 0 then concat acc \"!\""
  , "  else rep (subi n 1) (concat acc \"x\")"
  , "in"
  , "rep 3 \"\""
  ]))
with ([], vstr_ "xxx!")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "recursive"
  , "  let even = lam n. lam acc."
  , "    match n with 0 then concat acc \"even\""
  , "    else odd (subi n 1) acc"
  , "  let odd = lam n. lam acc."
  , "    match n with 0 then concat acc \"odd\""
  , "    else even (subi n 1) acc"
  , "in"
  , "even 3 \"\""
  ]))
with ([], vstr_ "odd")
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "type Nat in"
  , "con Z : () -> Nat in"
  , "con S : Nat -> Nat in"
  , "recursive let toInt = lam n. lam acc."
  , "  match n with S m then toInt m (addi acc 1)"
  , "  else addi acc 0"
  , "in"
  , "toInt (S (S (S (Z ())))) 0"
  ]))
with ([], VInt 3)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "recursive let rep = lam n. lam acc."
  , "  match n with 0 then concat acc \"!\""
  , "  else rep (subi n 1) (concat acc (readLine ()))"
  , "in"
  , "rep 2 \"\""
  ]))
with
  ( [ IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [vstr_ "", VRef {ty = tystr_, ref = 0}]
      }
    , IConstCall {const = CReadLine (), args = [vunit_]}
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 1}, VRef {ty = tystr_, ref = 2}]
      }
    , IConstCall
      { const = CConcat ()
      , args = [VRef {ty = tystr_, ref = 3}, vstr_ "!"]
      }
    ]
  , VRef {ty = tystr_, ref = 4}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Residual match targets ===

utest callEvalF (prepare (strJoin "\n"
  [ "let x = testResidual 3 in"
  , "match x with 0 then 1 else 2"
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [VInt 3]}
    , IMatch
      { target = 0
      , arms =
        [ (pint_ 0, [], [VInt 1])
        , (pvarw_, [], [VInt 2])
        ]
      }
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqInstrAndVal else ppInstrAndVal in

-- The arms agree, so nothing has to be passed out of the match
utest callEvalF (prepare (strJoin "\n"
  [ "let x = testResidual 3 in"
  , "match x with 0 then 1 else 1"
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [VInt 3]}
    , IMatch
      { target = 0
      , arms = [(pint_ 0, [], []), (pvarw_, [], [])]
      }
    ]
  , VInt 1
  )
using eqInstrAndVal else ppInstrAndVal in

-- The arms agree on the shape, so only the differing components are
-- passed out
utest callEvalF (prepare (strJoin "\n"
  [ "let x = testResidual 3 in"
  , "match x with 0 then (1, 2) else (1, 3)"
  ]))
with
  ( [ IConstCall {const = CResidualIdentity (), args = [VInt 3]}
    , IMatch
      { target = 0
      , arms =
        [ (pint_ 0, [], [VInt 2])
        , (pvarw_, [], [VInt 3])
        ]
      }
    ]
  , vrecord_ [("0", VInt 1), ("1", VRef {ty = tyint_, ref = 1})]
  )
using eqInstrAndVal else ppInstrAndVal in

-- A pattern that binds a name, which becomes a `VRef` local to the arm
utest callEvalF (prepare (strJoin "\n"
  [ "let x = testResidual {a = 1, b = 2} in"
  , "match x with {a = a} then (a, 1) else (0, 2)"
  ]))
with
  ( [ IConstCall
      { const = CResidualIdentity ()
      , args = [vrecord_ [("a", VInt 1), ("b", VInt 2)]]
      }
    , IMatch
      { target = 0
      , arms =
        [ ( prec_ [("a", pvar_ "a")]
          , [], [VRef {ty = tyint_, ref = 1}, VInt 1]
          )
        , (pvarw_, [], [VInt 0, VInt 2])
        ]
      }
    ]
  , vrecord_
    [("0", VRef {ty = tyint_, ref = 1}), ("1", VRef {ty = tyint_, ref = 2})]
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- A constructor name, symbolized in the pattern, in the argument of
-- the instruction, and in the value passed out of the match
utest callEvalF (prepare (strJoin "\n"
  [ "type Foo in"
  , "con Bar : Int -> Foo in"
  , "let x = testResidual (Bar 4) in"
  , "match x with Bar n then Bar n else Bar 0"
  ]))
with
  ( [ IConstCall
      { const = CResidualIdentity ()
      , args = [vconapp_ "Foo" "Bar" (VInt 4)]
      }
    , IMatch
      { target = 0
      , arms =
        [ (pcon_ "Bar" (pvar_ "n"), [], [VRef {ty = tyint_, ref = 1}])
        , (pvarw_, [], [VInt 0])
        ]
      }
    ]
  , vconapp_ "Foo" "Bar" (VRef {ty = tyint_, ref = 1})
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- The arms disagree on the constructor, so each passes out a full
-- constructor application, and the result is a hole typed by the data
-- type
utest callEvalF (prepare (strJoin "\n"
  [ "type Foo in"
  , "con Bar : Int -> Foo in"
  , "con Baz : Int -> Foo in"
  , "let x = testResidual (Bar 4) in"
  , "match x with Bar n then Bar n else Baz 0"
  ]))
with
  ( [ IConstCall
      { const = CResidualIdentity ()
      , args = [vconapp_ "Foo" "Bar" (VInt 4)]
      }
    , IMatch
      { target = 0
      , arms =
        [ ( pcon_ "Bar" (pvar_ "n")
          , [], [vconapp_ "Foo" "Bar" (VRef {ty = tyint_, ref = 1})]
          )
        , (pvarw_, [], [vconapp_ "Foo" "Baz" (VInt 0)])
        ]
      }
    ]
  , VRef {ty = tycon_ "Foo", ref = 1}
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- === Blocks ===

-- The two arms call the same function with different arguments, thus
-- requesting one block each. The first call passes a residual value,
-- which becomes a parameter of its block, the second a static one,
-- which is baked into the block instead. Neither return value has any
-- structure to merge, so the match passes out one value per arm.
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. testResidual x in"
  , "let y = testResidual 3 in"
  , "match y with 0 then f y else f 4"
  ]))
with
  ( [ residual_ (VInt 3)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        , ( pvarw_
          , [blockCall_ "block1" [] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VInt 4)]
        [0] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- As above, but the two blocks return records of the same shape, so
-- the static field is merged and only the residual one is passed out
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. (1, testResidual x) in"
  , "let y = testResidual 3 in"
  , "match y with 0 then f y else f 4"
  ]))
with
  ( [ residual_ (VInt 3)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        , ( pvarw_
          , [blockCall_ "block1" [] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (vrecord_ [("0", VInt 1), ("1", VRef {ty = tyint_, ref = 0})])
    , block_ "block1" []
        [residual_ (VInt 4)]
        [0] (vrecord_ [("0", VInt 1), ("1", VRef {ty = tyint_, ref = 0})])
    ]
  , vrecord_ [("0", VInt 1), ("1", VRef {ty = tyint_, ref = 1})]
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- Both arms make the same call, which is the same block requested
-- twice, thus computed once and referenced from both arms
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. testResidual x in"
  , "let y = testResidual 3 in"
  , "match y with 0 then f y else f y"
  ]))
with
  ( [ residual_ (VInt 3)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        , ( pvarw_
          , [blockCall_ "block0" [0] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- The arms call the same function with *different* residual values,
-- which is still a single block: what identifies it is the static
-- structure of the arguments, and the residual parts are passed in,
-- here as a different `VRef` per arm
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. testResidual x in"
  , "let y = testResidual 3 in"
  , "let z = testResidual 4 in"
  , "match y with 0 then f y else f z"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VInt 4)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0] [tyint_]]
          , [VRef {ty = tyint_, ref = 2}]
          )
        , ( pvarw_
          , [blockCall_ "block0" [1] [tyint_]]
          , [VRef {ty = tyint_, ref = 2}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- Two residual arguments, passed in the opposite order in the second
-- arm, which pins the order the parameters of a block are in: it is
-- the order the `VRef`s are encountered in the arguments of the call
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. testResidual (subi a b) in"
  , "let y = testResidual 3 in"
  , "let z = testResidual 4 in"
  , "match y with 0 then f y z else f z y"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VInt 4)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0, 1] [tyint_]]
          , [VRef {ty = tyint_, ref = 2}]
          )
        , ( pvarw_
          , [blockCall_ "block0" [1, 0] [tyint_]]
          , [VRef {ty = tyint_, ref = 2}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CSubi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        , residual_ (VRef {ty = tyint_, ref = 2})
        ]
        [3] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- The residual values can sit inside a structure, which is then part
-- of what identifies the block, with a hole per residual value
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam p. testResidual p in"
  , "let y = testResidual 3 in"
  , "let z = testResidual 4 in"
  , "match y with 0 then f (y, z) else f (z, y)"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VInt 4)
    , IMatch
      { target = 0
      , arms =
        [ ( pint_ 0
          , [blockCall_ "block0" [0, 1] [tytuple_ [tyint_, tyint_]]]
          , [VRef {ty = tytuple_ [tyint_, tyint_], ref = 2}]
          )
        , ( pvarw_
          , [blockCall_ "block0" [1, 0] [tytuple_ [tyint_, tyint_]]]
          , [VRef {ty = tytuple_ [tyint_, tyint_], ref = 2}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ residual_
          (vrecord_
            [ ("0", VRef {ty = tyint_, ref = 0})
            , ("1", VRef {ty = tyint_, ref = 1})
            ])
        ]
        [2] (VRef {ty = tytuple_ [tyint_, tyint_], ref = 0})
    ]
  , VRef {ty = tytuple_ [tyint_, tyint_], ref = 2}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- The argument of the call is bound by the pattern, which makes it a
-- `VRef` local to the arm, and thus a parameter of the block
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. testResidual x in"
  , "let y = testResidual {a = 1, b = 2} in"
  , "match y with {a = a} then f a else f 0"
  ]))
with
  ( [ residual_ (vrecord_ [("a", VInt 1), ("b", VInt 2)])
    , IMatch
      { target = 0
      , arms =
        [ ( prec_ [("a", pvar_ "a")]
          , [blockCall_ "block0" [1] [tyint_]]
          , [VRef {ty = tyint_, ref = 2}]
          )
        , ( pvarw_
          , [blockCall_ "block1" [] [tyint_]]
          , [VRef {ty = tyint_, ref = 1}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VInt 0)]
        [0] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- A call to a function from inside its own `recursive` binding is a
-- block that is requested while it is being computed, so its return
-- value is a `Left`, only available once every block is forced.
utest callEvalF (prepare (strJoin "\n"
  [ "recursive let f = lam x."
  , "  let y = testResidual x in"
  , "  match y with 0 then f y else y"
  , "in"
  , "f (testResidual 3)"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VRef {ty = tyint_, ref = 0})
    , IMatch
      { target = 1
      , arms =
        [ ( pint_ 0
          , [lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})]
          , [VRef {ty = tyint_, ref = 2}]
          )
        , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ residual_ (VRef {ty = tyint_, ref = 0})
        , IMatch
          { target = 1
          , arms =
            [ ( pint_ 0
              , [lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})]
              , [VRef {ty = tyint_, ref = 2}]
              )
            , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
            ]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- A recursive call whose arguments embed those of an enclosing call
-- is generalized, which is what stops `n` from producing a new block
-- for each value it takes
utest callEvalF (prepare (strJoin "\n"
  [ "recursive let f = lam n. lam x."
  , "  match x with 0 then n else f (addi n 1) (subi x 1)"
  , "in"
  , "f 0 (testResidual 5)"
  ]))
with
  ( [ residual_ (VInt 5)
    , IMatch
      { target = 0
      , arms =
        [ (pint_ 0, [], [VInt 0])
        , ( pvarw_
          , [ IConstCall
              {const = CSubi (), args = [VRef {ty = tyint_, ref = 0}, VInt 1]}
            , lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})
            ]
          , [VRef {ty = tyint_, ref = 2}]
          )
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IMatch
          { target = 0
          , arms =
            [ (pint_ 0, [], [VInt 1])
            , ( pvarw_
              , [ IConstCall
                  {const = CSubi (), args = [VRef {ty = tyint_, ref = 0}, VInt 1]}
                , residual_ (VInt 2)
                , lazyBlockCall_ "block1" [2, 1] (VRef {ty = tyint_, ref = 0})
                ]
              , [VRef {ty = tyint_, ref = 3}]
              )
            ]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" [tyint_, tyint_]
        [ IMatch
          { target = 1
          , arms =
            [ (pint_ 0, [], [VRef {ty = tyint_, ref = 0}])
            , ( pvarw_
              , [ IConstCall
                  {const = CAddi (), args = [VRef {ty = tyint_, ref = 0}, VInt 1]}
                , IConstCall
                  {const = CSubi (), args = [VRef {ty = tyint_, ref = 1}, VInt 1]}
                , lazyBlockCall_ "block1" [2, 3] (VRef {ty = tyint_, ref = 0})
                ]
              , [VRef {ty = tyint_, ref = 4}]
              )
            ]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- Mutual recursion, where only the first call of the cycle finds an
-- uncomputed block. `f` is called at the top level, thus inlined, and
-- requests a block for `g`; that block in turn requests one for `f`,
-- with a `Left` return, but by the time the latter is computed `g` is
-- already in `computedBlocks`, so its return value is known, and that
-- arm can be merged with the other.
utest callEvalF (prepare (strJoin "\n"
  [ "recursive"
  , "  let f = lam x."
  , "    let y = testResidual x in"
  , "    match y with 0 then g y else y"
  , "  let g = lam x."
  , "    let y = testResidual x in"
  , "    match y with 1 then f y else y"
  , "in"
  , "f (testResidual 3)"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VRef {ty = tyint_, ref = 0})
    , IMatch
      { target = 1
      , arms =
        [ ( pint_ 0
          , [lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})]
          , [VRef {ty = tyint_, ref = 2}]
          )
        , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
        ]
      }
    ]
  , [ -- The block for `g`
      block_ "block0" [tyint_]
        [ residual_ (VRef {ty = tyint_, ref = 0})
        , IMatch
          { target = 1
          , arms =
            [ ( pint_ 1
              , [lazyBlockCall_ "block1" [1] (VRef {ty = tyint_, ref = 0})]
              , [VRef {ty = tyint_, ref = 2}]
              )
            , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
            ]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
      -- The block for `f`
    , block_ "block1" [tyint_]
        [ residual_ (VRef {ty = tyint_, ref = 0})
        , IMatch
          { target = 1
          , arms =
            [ ( pint_ 0
              , [blockCall_ "block0" [1] [tyint_]]
              , [VRef {ty = tyint_, ref = 2}]
              )
            , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
            ]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- The same call, with the same arguments, but at two different
-- instantiations of `f`, which thus are two different blocks
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let f = lam. testResidual [] in"
  , "let a : [Int] = f () in"
  , "let b : [Char] = f () in"
  , "(a, b)"
  ]))
with
  ( [ blockCall_ "block0" [] [tyseq_ tyint_]
    , blockCall_ "block1" [] [tyseq_ tychar_]
    ]
  , [ block_ "block0" []
        [residual_ (VSeq {ty = tyseq_ tyint_, vals = []})]
        [0] (VRef {ty = tyseq_ tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VSeq {ty = tyseq_ tychar_, vals = []})]
        [0] (VRef {ty = tyseq_ tychar_, ref = 0})
    ]
  , vrecord_
    [ ("0", VRef {ty = tyseq_ tyint_, ref = 0})
    , ("1", VRef {ty = tyseq_ tychar_, ref = 1})
    ]
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in


-- === Inlining predicates ===

-- Every call becomes a block, even one that could be computed here
-- and for all
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "f 2"
  ]))
with
  ( [ blockCall_ "block0" [] []
    ]
  , [ block_ "block0" [] [] [] (VInt 3)
    ]
  , VInt 3
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- A predicate that looks at the arguments: `f` is inlined where its
-- argument is known and turned into a block where it is residual
let inlineKnownArgs : InlineF = lam app.
  forAll (lam v. match v with VRef _ then false else true) app.1 in

utest callEvalFWith inlineKnownArgs (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "let y = testResidual 3 in"
  , "addi (f 2) (f y)"
  ]))
with
  ( [ residual_ (VInt 3)
    , blockCall_ "block0" [0] [tyint_]
    , IConstCall
      { const = CAddi ()
      , args = [VInt 3, VRef {ty = tyint_, ref = 1}]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- A recursive call that is not in the body of a `match` arm reaches
-- the block through `applyF`, and is emitted while its own block is
-- still being computed, so its return value is only known later. The
-- type of the call is known here, however, and is what `r2` gets.
let inlineNonRecursive : InlineF = lam app.
  match app.0 with VLam x then not x.isRecursiveCall else true in

utest callEvalFWith inlineNonRecursive (prepare (strJoin "\n"
  [ "recursive let f = lam x."
  , "  let y = testResidual x in"
  , "  addi (f y) 1"
  , "in"
  , "f (testResidual 3)"
  ]))
with
  ( [ residual_ (VInt 3)
    , residual_ (VRef {ty = tyint_, ref = 0})
    , lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})
    , IConstCall
      { const = CAddi ()
      , args = [VRef {ty = tyint_, ref = 2}, VInt 1]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ residual_ (VRef {ty = tyint_, ref = 0})
        , lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})
        , IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 2}, VInt 1]
          }
        ]
        [3] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 3}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- The result of the recursive call is in turn an argument of a call,
-- which makes its type a parameter type of `block1`, i.e. this is
-- where the type `applyF` is given for a not-yet-computed block shows
-- up in a comparison
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let g = lam z. addi z 1 in"
  , "recursive let f = lam x."
  , "  let y = testResidual x in"
  , "  g (f y)"
  , "in"
  , "f (testResidual 3)"
  ]))
with
  ( [ residual_ (VInt 3)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [ residual_ (VRef {ty = tyint_, ref = 0})
        , lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})
        , blockCall_ "block1" [2] [tyint_]
        ]
        [3] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in


-- === Instantiations in recursive lets ===

-- Inside a `recursive` group the bindings refer to each other
-- monomorphically, so the type checker gives such a reference no
-- instantiation; `fixRecursiveInstantiate` fills it in from the
-- generalized type of the binding. `h` is defined outside the group, so
-- calls to it are not recursive, and the parameter type of its block
-- shows the type of the value passed to it.

-- `f` and `g` share a type variable through the type of `g`, thus the
-- instantiation of `g` covers it, and `h` sees `[Int]`
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let h = lam z. testResidual z in"
  , "recursive"
  , "  let f = lam x. testResidual x"
  , "  let g = lam y. let z = f y in let w = h z in 1"
  , "in"
  , "g (testResidual [1])"
  ]))
with
  ( [ residual_ (VSeq {ty = tyseq_ tyint_, vals = [VInt 1]})
    , blockCall_ "block0" [0] []
    ]
  , [ block_ "block0" [tyseq_ tyint_]
        [ lazyBlockCall_ "block1" [0] (VRef {ty = tyseq_ tyint_, ref = 0})
        , blockCall_ "block2" [1] [tyseq_ tyint_]
        ]
        [] (VInt 1)
    , block_ "block1" [tyseq_ tyint_]
        [residual_ (VRef {ty = tyseq_ tyint_, ref = 0})]
        [1] (VRef {ty = tyseq_ tyint_, ref = 0})
    , block_ "block2" [tyseq_ tyint_]
        [residual_ (VRef {ty = tyseq_ tyint_, ref = 0})]
        [1] (VRef {ty = tyseq_ tyint_, ref = 0})
    ]
  , VInt 1
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- An annotated `f` is polymorphic in its own body, so the recursive
-- call is instantiated like any other, and ends up at the same block
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let h = lam z. testResidual z in"
  , "recursive let f : all a. a -> a = lam x."
  , "  let y = h x in"
  , "  let t = testResidual 0 in"
  , "  match t with 0 then f y else y"
  , "in"
  , "f (testResidual 3)"
  ]))
with
  ( [ residual_ (VInt 3)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [ blockCall_ "block1" [0] [tyint_]
        , residual_ (VInt 0)
        , IMatch
          { target = 2
          , arms =
            [ ( pint_ 0
              , [lazyBlockCall_ "block0" [1] (VRef {ty = tyint_, ref = 0})]
              , [VRef {ty = tyint_, ref = 3}]
              )
            , (pvarw_, [], [VRef {ty = tyint_, ref = 1}])
            ]
          }
        ]
        [3] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" [tyint_]
        [residual_ (VRef {ty = tyint_, ref = 0})]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in


-- TODO(vipa, 2026-09-30): This test essentially documents a flaw in
-- the type-checker, where a type-variable can leak from one mutually
-- recursive function to another. See `type-check.mc`, a TODO with the
-- same date, for details.
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let h = lam z. testResidual z in"
  , "recursive"
  , "  let f = lam x. testResidual x"
  , "  let g = lam n. let y = f [] in let w = h y in n"
  , "in"
  , "g (testResidual 1)"
  ]))
with
  ( [ residual_ (VInt 1)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [ lazyBlockCall_ "block1" [] (VRef {ty = tyunknown_, ref = 0})
        , blockCall_ "block2" [1] [tyseq_ (tyvar_ "a")]
        ]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VSeq {ty = tyunknown_, vals = []})]
        [0] (VRef {ty = tyunknown_, ref = 0})
    , block_ "block2" [tyseq_ (tyvar_ "a")]
        [residual_ (VRef {ty = tyunknown_, ref = 0})]
        [1] (VRef {ty = tyunknown_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- As above, but with `f` annotated, which makes the call to it in `g`
-- an instantiation of its own. Nothing constrains that instantiation,
-- so the type checker leaves `Unknown` there, as it would outside a
-- `recursive` group.
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let h = lam z. testResidual z in"
  , "recursive"
  , "  let f : all b. [b] -> [b] = lam x. testResidual x"
  , "  let g = lam n. let y = f [] in let w = h y in n"
  , "in"
  , "g (testResidual 1)"
  ]))
with
  ( [ residual_ (VInt 1)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [ lazyBlockCall_ "block1" [] (VRef {ty = tyunknown_, ref = 0})
        , blockCall_ "block2" [1] [tyseq_ tyunknown_]
        ]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VSeq {ty = tyunknown_, vals = []})]
        [0] (VRef {ty = tyunknown_, ref = 0})
    , block_ "block2" [tyseq_ tyunknown_]
        [residual_ (VRef {ty = tyunknown_, ref = 0})]
        [1] (VRef {ty = tyunknown_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- `f` is monomorphic, so the call to it in `g` has an empty
-- instantiation, and the two instantiations of `g` share the block for
-- `f`
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "recursive"
  , "  let f = lam x. testResidual (addi x 1)"
  , "  let g = lam y. f 1"
  , "in"
  , "let e1 : [Int] = [] in"
  , "let e2 : [Char] = [] in"
  , "(g e1, g e2)"
  ]))
with
  ( [ blockCall_ "block0" [] [tyint_]
    , blockCall_ "block2" [] [tyint_]
    ]
  , [ block_ "block0" []
        [lazyBlockCall_ "block1" [] (VRef {ty = tyint_, ref = 0})]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VInt 2)]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block2" []
        [lazyBlockCall_ "block1" [] (VRef {ty = tyint_, ref = 0})]
        [0] (VRef {ty = tyint_, ref = 0})
    ]
  , vrecord_
    [ ("0", VRef {ty = tyint_, ref = 0})
    , ("1", VRef {ty = tyint_, ref = 1})
    ]
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- As above, but with `g` annotated, which changes nothing, since the
-- call in `g` is to the unannotated, thus monomorphic, `f`
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "recursive"
  , "  let f = lam x. testResidual (addi x 1)"
  , "  let g : all c. c -> Int = lam y. f 1"
  , "in"
  , "let e1 : [Int] = [] in"
  , "let e2 : [Char] = [] in"
  , "(g e1, g e2)"
  ]))
with
  ( [ blockCall_ "block0" [] [tyint_]
    , blockCall_ "block2" [] [tyint_]
    ]
  , [ block_ "block0" []
        [lazyBlockCall_ "block1" [] (VRef {ty = tyint_, ref = 0})]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" []
        [residual_ (VInt 2)]
        [0] (VRef {ty = tyint_, ref = 0})
    , block_ "block2" []
        [lazyBlockCall_ "block1" [] (VRef {ty = tyint_, ref = 0})]
        [0] (VRef {ty = tyint_, ref = 0})
    ]
  , vrecord_
    [ ("0", VRef {ty = tyint_, ref = 0})
    , ("1", VRef {ty = tyint_, ref = 1})
    ]
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in


-- === Opaque terms ===

-- The body is residualized as is, and each free variable is bound to
-- the value it refers to, residual or not
utest callEvalF (prepare (strJoin "\n"
  [ "let x = testResidual 1 in"
  , "let y = 2 in"
  , "tmOpaque (addi x y)"
  ]))
with
  ( [ residual_ (VInt 1)
    , IOpaque
      { bindings = mapFromSeq nameCmp
        [ (nameNoSym "x", Right (VRef {ty = tyint_, ref = 0}))
        , (nameNoSym "y", Right (VInt 2))
        ]
      , body = addi_ (var_ "x") (var_ "y")
      }
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqInstrAndValIgnoringSymbols else ppInstrAndVal in

-- A function is saturated with a `VRef` per argument it is still
-- missing, here one, since it is partially applied already
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "let g = f 1 in"
  , "tmOpaque (g 2)"
  ]))
with
  ( [ IOpaque
      { bindings = mapFromSeq nameCmp
        [ ( nameNoSym "g"
          , Left
            { params = [VRef {ty = tyint_, ref = 0}]
            , instr = blockCall_ "block0" [0] [tyint_]
            , ret = VRef {ty = tyint_, ref = 1}
            }
          )
        ]
      , body = app_ (var_ "g") (int_ 2)
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VInt 1, VRef {ty = tyint_, ref = 0}]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 0}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a (char2int b) in"
  , "let g = f 1 in"
  , "tmOpaque (g 'c')"
  ]))
with
  ( [ IOpaque
      { bindings = mapFromSeq nameCmp
        [ ( nameNoSym "g"
          , Left
            { params = [VRef {ty = tychar_, ref = 0}]
            , instr = blockCall_ "block0" [0] [tyint_]
            , ret = VRef {ty = tyint_, ref = 1}
            }
          )
        ]
      , body = app_ (var_ "g") (char_ 'c')
      }
    ]
  , [ block_ "block0" [tychar_]
        [ IConstCall
          { const = CChar2Int ()
          , args = [VRef {ty = tychar_, ref = 0}]
          }
        , IConstCall
          { const = CAddi ()
          , args = [VInt 1, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 0}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- A polymorphic function is used at the instantiation of its
-- occurrence in the body
utest callEvalF (prepare (strJoin "\n"
  [ "let id = lam x. testResidual x in"
  , "tmOpaque (id 'c')"
  ]))
with
  ( [ IOpaque
      { bindings = mapFromSeq nameCmp
        [ ( nameNoSym "id"
          , Left
            { params = [VRef {ty = tychar_, ref = 0}]
            , instr = blockCall_ "block0" [0] [tychar_]
            , ret = VRef {ty = tychar_, ref = 1}
            }
          )
        ]
      , body = app_ (var_ "id") (char_ 'c')
      }
    ]
  , [ block_ "block0" [tychar_]
        [residual_ (VRef {ty = tychar_, ref = 0})]
        [1] (VRef {ty = tychar_, ref = 0})
    ]
  , VRef {ty = tychar_, ref = 0}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- Nothing in the body is evaluated, not even the calls to `f`, and the
-- names it binds itself are left alone
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "tmOpaque (lam y. f (f y))"
  ]))
with
  ( [ IOpaque
      { bindings = mapFromSeq nameCmp
        [ ( nameNoSym "f"
          , Left
            { params = [VRef {ty = tyint_, ref = 0}]
            , instr = blockCall_ "block0" [0] [tyint_]
            , ret = VRef {ty = tyint_, ref = 1}
            }
          )
        ]
      , body = ulam_ "y" (app_ (var_ "f") (app_ (var_ "f") (var_ "y")))
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyarrow_ tyint_ tyint_, ref = 0}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in

-- A function partially applied to a residual value, which is passed on
-- to the block along with the `VRef` for the missing argument. Only
-- variables free in the body are bound, i.e., not `f` or `a`.
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "let a = testResidual 1 in"
  , "let g = f a in"
  , "tmOpaque (g 2)"
  ]))
with
  ( [ residual_ (VInt 1)
    , IOpaque
      { bindings = mapFromSeq nameCmp
        [ ( nameNoSym "g"
          , Left
            { params = [VRef {ty = tyint_, ref = 1}]
            , instr = blockCall_ "block0" [0, 1] [tyint_]
            , ret = VRef {ty = tyint_, ref = 2}
            }
          )
        ]
      , body = app_ (var_ "g") (int_ 2)
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndValIgnoringSymbols else ppBlocksInstrAndVal in


-- === Functions as values ===

-- A function passed to a function that becomes a block is part of
-- the key of that block
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "let app = lam g. lam y. g y in"
  , "app f (testResidual 1)"
  ]))
with
  ( [ residual_ (VInt 1)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [blockCall_ "block1" [0] [tyint_]]
        [1] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- A residual value a function is partially applied to becomes a
-- parameter of the block, like any other residual argument
utest callEvalFWith inlineNone (prepare (strJoin "\n"
  [ "let add = lam a. lam b. addi a b in"
  , "let app = lam g. lam y. g y in"
  , "let r = testResidual 1 in"
  , "app (add r) 2"
  ]))
with
  ( [ residual_ (VInt 1)
    , blockCall_ "block0" [0] [tyint_]
    ]
  , [ block_ "block0" [tyint_]
        [blockCall_ "block1" [0] [tyint_]]
        [1] (VRef {ty = tyint_, ref = 0})
    , block_ "block1" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 2]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- The arms of a residual match produce the same function, so nothing
-- has to be passed out, and the call after it is known
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "let t = testResidual 0 in"
  , "let h = match t with 0 then f else f in"
  , "h 2"
  ]))
with
  ( [ residual_ (VInt 0)
    , IMatch {target = 0, arms = [(pint_ 0, [], []), (pvarw_, [], [])]}
    ]
  , VInt 3
  )
using eqInstrAndVal else ppInstrAndVal in

-- As above, but the function is applied to different arguments, which
-- are passed out as usual
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "let t = testResidual 0 in"
  , "let h = match t with 0 then f 1 else f 2 in"
  , "h 10"
  ]))
with
  ( [ residual_ (VInt 0)
    , IMatch
      { target = 0
      , arms = [(pint_ 0, [], [VInt 1]), (pvarw_, [], [VInt 2])]
      }
    , IConstCall
      { const = CAddi ()
      , args = [VRef {ty = tyint_, ref = 1}, VInt 10]
      }
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqInstrAndVal else ppInstrAndVal in


-- === Higher-order constants ===

let vintseq_ : [Int] -> PEGVal = lam is.
  VSeq {ty = tyseq_ tyint_, vals = map (lam i. VInt i) is} in

-- A fully known sequence is mapped here and now, one application per
-- element, so nothing at all is left of the `map` itself
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "map f [1, 2, 3]"
  ]))
with
  ([], vintseq_ [2, 3, 4])
using eqInstrAndVal else ppInstrAndVal in

-- As above, with a partially applied function
utest callEvalF (prepare (strJoin "\n"
  [ "let g = lam a. lam b. addi a b in"
  , "map (g 1) [1, 2, 3]"
  ]))
with
  ([], vintseq_ [2, 3, 4])
using eqInstrAndVal else ppInstrAndVal in

-- The sequence is known but the function residualizes, so the
-- applications are emitted individually and the result is a known
-- sequence of residual values
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. testResidual x in"
  , "map f [1, 2]"
  ]))
with
  ( [ residual_ (VInt 1)
    , residual_ (VInt 2)
    ]
  , VSeq
    { ty = tyseq_ tyint_
    , vals = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
    }
  )
using eqInstrAndVal else ppInstrAndVal in

-- A residual sequence cannot be mapped element by element, so the
-- `map` is residualized as an `IConstFCall`. Its function argument is
-- evaluated once, in an inner scope where the element is `r1`, the
-- number the call itself returns into; inlining is off in that scope,
-- hence the block call.
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. addi x 1 in"
  , "map f (testResidual [1, 2, 3])"
  ]))
with
  ( [ residual_ (vintseq_ [1, 2, 3])
    , IConstFCall
      { const = CMap ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 1}]
          , instr = blockCall_ "block0" [1] [tyint_]
          , ret = VRef {ty = tyint_, ref = 2}
          }
        , Right (VRef {ty = tyseq_ tyint_, ref = 0})
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 1]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyseq_ tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- The mapped function closes over a residual value, so the inner
-- scope reaches outside itself: `r0` is passed to the block alongside
-- the element. This is why the element gets the number the call
-- returns into rather than starting over at `r0`.
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "map (f (testResidual 1)) (testResidual [1, 2, 3])"
  ]))
with
  ( [ residual_ (VInt 1)
    , residual_ (vintseq_ [1, 2, 3])
    , IConstFCall
      { const = CMap ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 2}]
          , instr = blockCall_ "block0" [0, 2] [tyint_]
          , ret = VRef {ty = tyint_, ref = 3}
          }
        , Right (VRef {ty = tyseq_ tyint_, ref = 1})
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyseq_ tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- `mapi` differs from `map` only in the extra parameter
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. lam x. addi i x in"
  , "mapi f [10, 20, 30]"
  ]))
with
  ([], vintseq_ [10, 21, 32])
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. lam x. addi i x in"
  , "mapi f (testResidual [10, 20, 30])"
  ]))
with
  ( [ residual_ (vintseq_ [10, 20, 30])
    , IConstFCall
      { const = CMapi ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 1}, VRef {ty = tyint_, ref = 2}]
          , instr = blockCall_ "block0" [1, 2] [tyint_]
          , ret = VRef {ty = tyint_, ref = 3}
          }
        , Right (VRef {ty = tyseq_ tyint_, ref = 0})
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyseq_ tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- `iter` keeps the effects of each application and discards the
-- values, so a known sequence leaves the applications behind but not
-- the `iter`
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. print x in"
  , "iter f [\"a\", \"b\"]"
  ]))
with
  ( [ IConstCall {const = CPrint (), args = [vstr_ "a"]}
    , IConstCall {const = CPrint (), args = [vstr_ "b"]}
    ]
  , vunit_
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. print x in"
  , "iter f (testResidual [\"a\", \"b\"])"
  ]))
with
  ( [ residual_ (VSeq {ty = tyseq_ tystr_, vals = [vstr_ "a", vstr_ "b"]})
    , IConstFCall
      { const = CIter ()
      , args =
        [ Left
          { params = [VRef {ty = tystr_, ref = 1}]
          , instr = blockCall_ "block0" [1] [tyunit_]
          , ret = VRef {ty = tyunit_, ref = 2}
          }
        , Right (VRef {ty = tyseq_ tystr_, ref = 0})
        ]
      }
    ]
  , [ block_ "block0" [tystr_]
        [ IConstCall {const = CPrint (), args = [VRef {ty = tystr_, ref = 0}]}
        ]
        [1] (VRef {ty = tyunit_, ref = 0})
    ]
  , VRef {ty = tyunit_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. lam x. print (subsequence x i 1) in"
  , "iteri f [\"ab\", \"cd\"]"
  ]))
with
  ( [ IConstCall {const = CPrint (), args = [vstr_ "a"]}
    , IConstCall {const = CPrint (), args = [vstr_ "d"]}
    ]
  , vunit_
  )
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. lam x. print x in"
  , "iteri f (testResidual [\"a\", \"b\"])"
  ]))
with
  ( [ residual_ (VSeq {ty = tyseq_ tystr_, vals = [vstr_ "a", vstr_ "b"]})
    , IConstFCall
      { const = CIteri ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 1}, VRef {ty = tystr_, ref = 2}]
          , instr = blockCall_ "block0" [1, 2] [tyunit_]
          , ret = VRef {ty = tyunit_, ref = 3}
          }
        , Right (VRef {ty = tyseq_ tystr_, ref = 0})
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tystr_]
        [ IConstCall {const = CPrint (), args = [VRef {ty = tystr_, ref = 1}]}
        ]
        [2] (VRef {ty = tyunit_, ref = 0})
    ]
  , VRef {ty = tyunit_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- A fold over a known sequence threads the accumulator through the
-- applications, which leaves nothing of the fold itself
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "foldl f 0 [1, 2, 3]"
  ]))
with
  ([], VInt 6)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam a. lam b. addi a b in"
  , "foldl f (testResidual 0) (testResidual [1, 2, 3])"
  ]))
with
  ( [ residual_ (VInt 0)
    , residual_ (vintseq_ [1, 2, 3])
    , IConstFCall
      { const = CFoldl ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 2}, VRef {ty = tyint_, ref = 3}]
          , instr = blockCall_ "block0" [2, 3] [tyint_]
          , ret = VRef {ty = tyint_, ref = 4}
          }
        , Right (VRef {ty = tyint_, ref = 0})
        , Right (VRef {ty = tyseq_ tyint_, ref = 1})
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CAddi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- `foldr` associates the other way, and takes the element first
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. lam a. subi x a in"
  , "foldr f 0 [1, 2, 3]"
  ]))
with
  ([], VInt 2)
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam x. lam a. subi x a in"
  , "foldr f (testResidual 0) (testResidual [1, 2, 3])"
  ]))
with
  ( [ residual_ (VInt 0)
    , residual_ (vintseq_ [1, 2, 3])
    , IConstFCall
      { const = CFoldr ()
      , args =
        [ Left
          { params = [VRef {ty = tyint_, ref = 2}, VRef {ty = tyint_, ref = 3}]
          , instr = blockCall_ "block0" [2, 3] [tyint_]
          , ret = VRef {ty = tyint_, ref = 4}
          }
        , Right (VRef {ty = tyint_, ref = 0})
        , Right (VRef {ty = tyseq_ tyint_, ref = 1})
        ]
      }
    ]
  , [ block_ "block0" [tyint_, tyint_]
        [ IConstCall
          { const = CSubi ()
          , args = [VRef {ty = tyint_, ref = 0}, VRef {ty = tyint_, ref = 1}]
          }
        ]
        [2] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyint_, ref = 2}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

-- `create` takes its function last, so the residual form has a value
-- argument before the function one
utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. muli i 2 in"
  , "create 3 f"
  ]))
with
  ([], vintseq_ [0, 2, 4])
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. muli i 2 in"
  , "createRope 3 f"
  ]))
with
  ([], vintseq_ [0, 2, 4])
using eqInstrAndVal else ppInstrAndVal in

utest callEvalF (prepare (strJoin "\n"
  [ "let f = lam i. muli i 2 in"
  , "create (testResidual 3) f"
  ]))
with
  ( [ residual_ (VInt 3)
    , IConstFCall
      { const = CCreate ()
      , args =
        [ Right (VRef {ty = tyint_, ref = 0})
        , Left
          { params = [VRef {ty = tyint_, ref = 1}]
          , instr = blockCall_ "block0" [1] [tyint_]
          , ret = VRef {ty = tyint_, ref = 2}
          }
        ]
      }
    ]
  , [ block_ "block0" [tyint_]
        [ IConstCall
          { const = CMuli ()
          , args = [VRef {ty = tyint_, ref = 0}, VInt 2]
          }
        ]
        [1] (VRef {ty = tyint_, ref = 0})
    ]
  , VRef {ty = tyseq_ tyint_, ref = 1}
  )
using eqBlocksInstrAndVal else ppBlocksInstrAndVal in

()
