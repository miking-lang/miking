-- This file provides a streamlined interface for loading files and their
-- dependencies, and ensuring they are symbolized and type-checked.
--
-- Usage centers around the Loader type, which represents a set of
-- loaded files and all their declarations. New files can be loaded
-- incrementally. Note that loading a file is a no-op if the file is
-- already loaded. Note also that since type-checking uses
-- side-effects for unification you cannot generally use a Loader as a
-- persistent value, i.e., always only use the newly returned Loader,
-- do not keep the old value.
--
-- NOTE(vipa, 2024-11-26): The implementation wraps the `boot` backed
-- pipeline rather than the new mlang-pipeline present in this
-- folder. This is temporary, until the new pipeline is sufficiently
-- stable. The external interface should remain largely the same
-- however.

include "stdlib.mc"
include "digraph.mc"

include "mexpr/boot-parser.mc"

include "mexpr/json-debug.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/resymbolize.mc"
include "mexpr/type-check.mc"

include "mlang/boot-parser.mc"
include "mlang/ast.mc"
include "mlang/pprint.mc"
include "mexpr/symbolize.mc"
include "name.mc"
include "basic-types.mc"
include "map.mc"
include "seq.mc"
include "mexpr/ast.mc"
include "error.mc"
include "string.mc"
include "bool.mc"
include "option.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
include "fileutils.mc"
include "mexpr/builtin.mc"
include "mexpr/pattern-analysis.mc"
include "set.mc"
include "lazy.mc"
include "mexpr/pprint.mc"
include "result.mc"
include "mexpr/type.mc"

lang SymGetters = Sym
  -- Helpers for looking up names from known symbolization
  -- environments
  sem _getVarExn : String -> {path : String, env : SymEnv} -> Name
  sem _getVarExn str = | {path = path, env = env} ->
    match mapLookup str env.currentEnv.varEnv
    with Some n then n
    else error (join
      [ "Compiler error: expected variable \"", str, "\" to be defined in\n"
      , path
      ])
  sem _getConExn : String -> {path : String, env : SymEnv} -> Name
  sem _getConExn str = | {path = path, env = env} ->
    match mapLookup str env.currentEnv.conEnv
    with Some n then n
    else error (join
      [ "Compiler error: expected constructor \"", str, "\" to be defined in\n"
      , path
      ])
  sem _getTyConExn : String -> {path : String, env : SymEnv} -> Name
  sem _getTyConExn str = | {path = path, env = env} ->
    match mapLookup str env.currentEnv.tyConEnv
    with Some n then n
    else error (join
      [ "Compiler error: expected type \"", str, "\" to be defined in\n"
      , path
      ])
end

lang MCoreKeywordMaker = KeywordMaker + KeywordMakerOpaque
end

-- TODO(vipa, 2026-07-13): I'm making some breaking changes to the
-- loader API to work better with a more proper self-hosting
-- path. I'll propagate that later, but it means there'll be some
-- duplication of code until that's done.
lang LoaderInterface
  = Ast + DeclAst + DeclSym + DeclTypeCheck + SymGetters

  -- The loader itself
  syn Loader =
  -- How to load a given file
  syn FileType =


  -- === External interface, when using a Loader ===

  sem mkLoader : TCEnv -> [Hook] -> Loader
  sem addHook : Loader -> Hook -> Loader
  sem remHook : (Hook -> Bool) -> Loader -> Loader
  sem hasHook : (Hook -> Bool) -> Loader -> Bool
  sem getHookOpt : all a. (Hook -> Option a) -> Loader -> Option a
  sem withHookState : all a. (Loader -> Hook -> Option (Loader, a)) -> Loader -> (Loader, a)
  -- Include a file (second String) relative to a directory (first
  -- String). Returns a symbolization enviroment containing only
  -- definitions from that specific file. Including a file is
  -- idempotent, the second include merely returns the previously
  -- discovered environment.
  sem includeFileExn : String -> String -> Loader -> ({path : String, env : SymEnv}, Loader)
  sem includeFileExn dir path = | loader -> includeFileTypeExn (_fileType path) dir path loader
  sem includeFileTypeExn : FileType -> String -> String -> Loader -> ({path : String, env : SymEnv}, Loader)
  sem getDecls : Loader -> [Decl]
  sem buildFullAst : Loader -> Expr


  -- === Internal interface, for supporting new files ===

  -- == Implemented by the loader, can be used ==

  -- Add decls to the loader. Added code is symbolized and
  -- type-checked, unless the used function contains `Symbolized` (in
  -- which case only type-checking is run) or `Typechecked` (in which
  -- case neither is run).
  sem _addDeclExn : SymEnv -> Loader -> Decl -> (SymEnv, Loader)
  sem _addSymbolizedDeclExn : Loader -> Decl -> Loader
  sem _addTypecheckedDecl : Loader -> Decl -> Loader

  -- Type-checking related functions
  sem _withTCEnv : all a. (TCEnv -> (TCEnv, a)) -> Loader -> (Loader, a)

  -- Run a function, capturing any added Decls in a separate
  -- environment, which is returned.
  sem _captureEnv : all a. (Loader -> (a, Loader)) -> Loader -> (a, SymEnv, Loader)
  -- Update the current file env. Should only be used in manual
  -- implementations of _addDeclExn et. al., the default
  -- implementation already adds whatever `Decl` is returned from
  -- symbolization and typechecking.
  sem _updateFileEnv : (SymEnv -> SymEnv) -> Loader -> Loader

  -- == To be implemented by a new file ==

  -- Called with a fully resolved path to a file to load. Paired to
  -- enable special handling based on file type.
  sem _loadFile : String -> (FileType, Loader) -> Loader

  -- Called to automatically determine how to load a given file based
  -- on its path, typically by the file extension.
  sem _fileType : String -> FileType
  sem _fileType =
  | path -> errorSingle [] (concat "No known handler for this file: " path)

  -- Used to carry extra state for hooks
  syn Hook =

  -- Hooks for additional processing around each phase.
  sem _preSymbolize : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _preSymbolize loader decl = | _ -> (loader, decl)

  sem _postSymbolize : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _postSymbolize loader decl = | _ -> (loader, decl)

  sem _preTypecheck : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _preTypecheck loader decl = | _ -> (loader, decl)

  sem _postTypecheck : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _postTypecheck loader decl = | _ -> (loader, decl)

  sem _preBuildFullAst : Loader -> Hook -> Loader
  sem _preBuildFullAst loader = | _ -> loader

  sem _postBuildFullAst : Loader -> Expr -> Hook -> Expr
  sem _postBuildFullAst loader ast = | _ -> ast
end

lang LoaderImpl = LoaderInterface

  -- The loader itself
  syn Loader +=
  -- How to load a given file
  syn FileType +=


  type LoaderRec =
    { decls : [Decl]
    , includedFiles : Map String {path : String, env : SymEnv}
    , tcEnv : TCEnv
    , hooks : [Hook]
    , includeStack : Map String Int
    , currentFileEnv : SymEnv
    }
  syn Loader +=
  | Loader LoaderRec

  sem mkLoader tcEnv += | hooks -> Loader
    { decls = []
    , includedFiles = mapEmpty cmpString
    , tcEnv = tcEnv
    , hooks = hooks
    , includeStack = mapEmpty cmpString
    , currentFileEnv = _symEnvEmpty
    }
  sem addHook loader += | hook ->
    match loader with Loader x in
    Loader {x with hooks = snoc x.hooks hook}
  sem remHook check += | Loader x ->
    Loader {x with hooks = filter (lam x. not (check x)) x.hooks}
  sem hasHook check += | Loader x ->
    optionIsSome (find check x.hooks)
  sem getHookOpt check += | Loader x ->
    findMap check x.hooks
  sem withHookState f += | loader & Loader x ->
    match findMap (f loader) x.hooks with Some res
    then res
    else error "Compiler error: missing hook in loader"

  sem _captureEnv f += | Loader x ->
    let prev = x.currentFileEnv in
    match f (Loader {x with currentFileEnv = _symEnvEmpty}) with (a, Loader x) in
    (a, x.currentFileEnv, Loader {x with currentFileEnv = prev})

  sem _updateFileEnv f += | Loader x ->
    Loader {x with currentFileEnv = f x.currentFileEnv}

  sem includeFileTypeExn ftype dir path += | loader & Loader x ->
    let resolved = stdlibResolveFileOr (lam x. error x) dir path in

    match mapLookup resolved x.includedFiles with Some env then
      (env, loader)
    else

    match mapLookup resolved x.includeStack with Some idx then
      let stack = mapValues (mapFromSeq subi (map (lam x. (x.1, x.0)) (mapBindings x.includeStack))) in
      let stack = snoc (subsequence stack idx (subi (length stack) idx)) resolved in
      error (strJoin "\n"
        (cons "Encountered an include cycle (each file is included by the previous one):"
          (map (lam f. concat "  - " f) stack)))
    else

    let prevStack = x.includeStack in
    let loader = Loader
      { x with includeStack = mapInsert resolved (mapSize x.includeStack) prevStack
      } in

    match _captureEnv (lam loader. ((), _loadFile resolved (ftype, loader))) loader with (_, env, Loader y) in

    let env = {path = resolved, env = env} in
    let loader = Loader
      { y with includeStack = prevStack
      , includedFiles = mapInsert resolved env y.includedFiles
      } in

    (env, loader)

  sem _withTCEnv f += | Loader x ->
    match f x.tcEnv with (tcEnv, a) in
    (Loader {x with tcEnv = tcEnv}, a)

  sem getDecls += | Loader x -> x.decls
  sem buildFullAst += | loader & Loader x ->
    match foldl (lam loader. lam cb. _preBuildFullAst loader cb) loader x.hooks
      with loader & Loader x in
    let ast = foldr bind_ unit_ x.decls in
    foldl (lam ast. lam cb. _postBuildFullAst loader ast cb) ast x.hooks

  sem _doHook : (Loader -> Decl -> Hook -> (Loader, Decl)) -> Loader -> Decl -> (Loader, Decl)
  sem _doHook f loader = | decl ->
    match loader with Loader {hooks = hooks} in
    foldl (lam acc. lam cb. f acc.0 acc.1 cb) (loader, decl) hooks

  sem _addDeclExn symEnv loader += | decl ->
    match _doHook _preSymbolize loader decl with (loader, decl) in
    match symbolizeDecl symEnv decl with (symEnv, decl) in
    match _doHook _postSymbolize loader decl with (loader, decl) in

    match _doHook _preTypecheck loader decl with (loader, decl) in
    match _withTCEnv (lam tcEnv. typeCheckDecl tcEnv decl) loader with (loader, decl) in
    match _doHook _postTypecheck loader decl with (Loader x, decl) in

    let loader = Loader
      { x with decls = snoc x.decls decl
      , currentFileEnv = declAddDefinition x.currentFileEnv decl
      } in

    (symEnv, loader)

  sem _addSymbolizedDeclExn loader += | decl ->
    match _doHook _preTypecheck loader decl with (loader, decl) in
    match _withTCEnv (lam tcEnv. typeCheckDecl tcEnv decl) loader with (loader, decl) in
    match _doHook _postTypecheck loader decl with (Loader x, decl) in

    let loader = Loader
      { x with decls = snoc x.decls decl
      , currentFileEnv = declAddDefinition x.currentFileEnv decl
      } in

    loader

  sem _addTypecheckedDecl loader += | decl ->
    match loader with Loader x in

    let loader = Loader
      { x with decls = snoc x.decls decl
      , currentFileEnv = declAddDefinition x.currentFileEnv decl
      } in

    loader
end

lang IncludeLoader = LoaderImpl + IncludeDeclAst
  sem _addDeclExn symEnv loader +=
  | DeclInclude x ->
    match x.info with Info {filename = filename} in
    match includeFileExn (dirname filename) x.path loader with (incEnv, loader) in
    (mergeSymEnv symEnv incEnv.env, loader)
end

lang BuiltinLoader = LoaderInterface
  syn Hook +=
  | BuiltinHook {env : SymEnv}

  sem includeBuiltinEnv : Loader -> (SymEnv, Loader)
  sem includeBuiltinEnv = | loader ->
    match getHookOpt (lam x. match x with BuiltinHook x then Some x.env else None ()) loader
    with Some env then (env, loader) else

    let addBuiltin = lam loader. lam pair.
      (_addDeclExn _symEnvEmpty loader (ulet_ pair.0 (uconst_ pair.1))).1 in
    let f = lam loader.
      let loader = foldl addBuiltin loader builtin in
      ((), loader) in
    match _captureEnv f loader with (_, env, loader) in
    let env = symbolizeUpdateTyConEnv env (mapUnion env.currentEnv.tyConEnv builtinTypeNames) in
    let loader = addHook loader (BuiltinHook {env = env}) in
    (env, loader)
end

lang MLangLoader = LoaderImpl + BootParserMLang
  + Sym + TypeCheck
  + BuiltinLoader
  + Resymbolize
  + NormPat

  syn FileType +=
  | FMCore {includeMExpr : Bool}
  sem _fileType += | _ ++ ".mc" -> FMCore {includeMExpr = false}

  type BranchId = Int

  type Order =
    { subset : BranchId
    , superset : BranchId
    }
  type OrderCache =
    { cache : Ref (Map BranchId (Either (Info -> Option Order) Order))
    , id : BranchId
    }

  type Branch =
    -- NOTE(vipa, 2026-07-13): The definitional stuff for the branch,
    -- included to be able to resymbolize when we include it in a
    -- materialized `sem`.
    { pat : Pat
    , body : Expr
    , params : {params : [Name], tyParams : [Name]}
    -- NOTE(vipa, 2026-07-13): Caches to not have to recompute pattern
    -- analysis.
    , posPat : Lazy NormPat
    , negPat : Lazy NormPat
    , orderCache : OrderCache -- order against all *earlier* branches
    }

  sem addToDigraph : Info -> Set BranchId -> OrderCache -> Digraph BranchId () -> Digraph BranchId ()
  sem addToDigraph info used cache = | dig ->
    let force = lam l. lam. switch l
      case Right order then Some order
      case Left f then f info
      end in
    let orders = mapIntersectWith force (deref cache.cache) used in
    let updateCache = lam pre. lam post. switch (pre, post)
      case (None _, _) | (_, Some (None _)) then None ()
      case (Some _, Some (Some post)) then Some (Right post)
      case (Some pre, None _) then Some pre
      end in
    modref cache.cache (mapMerge updateCache (deref cache.cache) orders);
    let addOrder = lam dig. lam. lam order.
      match order with Some order
      then digraphAddEdge order.subset order.superset () dig
      else dig in
    mapFoldWithKey addOrder (digraphAddVertex cache.id dig) orders

  sem mkBranch : [Branch] -> {params : [Name], tyParams : [Name]} -> Pat -> Expr -> Branch
  sem mkBranch older params pat = | body ->
    let id = length older in
    let posPat = lazy (lam. patToNormpat pat) in
    let negPat = lazy (lam. normpatComplement (lazyForce posPat)) in
    let computeOrder = lam otherId. lam info.
      let other = get older otherId in
      let thisInfo = infoPat pat in
      let otherInfo = infoPat other.pat in
      match normpatJointProof (lazyForce posPat) (lazyForce other.posPat) with Some jointProof then
        let thisMinusOther = normpatJointProof (lazyForce posPat) (lazyForce other.negPat) in
        let otherMinusThis = normpatJointProof (lazyForce negPat) (lazyForce other.posPat) in
        switch (thisMinusOther, otherMinusThis)
        case (Some _, None _) then
          Some {superset = id, subset = otherId}
        case (None _, Some _) then
          Some {superset = otherId, subset = id}
        case (None _, None _) then
          errorExtra thisInfo "This pattern matches exactly the same values as a previous pattern:"
            [ (info, "In 'sem' defined here:")
            , (otherInfo, "Previous pattern:")
            ]
        case (Some this, Some other) then
          let env = pprintEnvEmpty in
          match getPatStringCode 0 env (npatToPat jointProof) with (env, jointProof) in
          match getPatStringCode 0 env (npatToPat this) with (env, this) in
          match getPatStringCode 0 env (npatToPat other) with (env, other) in
          errorExtra info
            (join ["This 'sem' has overlapping patterns (e.g., both match '", jointProof, "'), but neither is more specific than the other."])
            [ (otherInfo, join ["Pattern 1 (matches '", other, "'):"])
            , (thisInfo, join ["Pattern 2 (matches '", this, "'):"])
            ]
        end
      else None () in
    let cache = mapFromSeq subi (create id (lam other. (other, Left (computeOrder other)))) in
    { pat = pat
    , body = body
    , params = params
    , posPat = posPat
    , negPat = negPat
    , orderCache =
      { id = id
      , cache = ref cache
      }
    }

  syn LangDefVar =
  | LDSem

  syn LangDefTyCon =
  | LDSyn
  | LDAlias

  syn LangDefCon =
  | LDCon

  -- NOTE(vipa, 2026-07-15): In a language we are not allowed to
  -- shadow definitions, but we are (sometimes) allowed to extend
  -- them, thus we need to store more information in our version of a
  -- symbolize environment. This is maintanied in parallel with the
  -- normal SymEnv, so MExpr code does't have to handle the increased
  -- complexity. Note also that it only contains things originally
  -- defined in a language, not things from outside, meaning a Name
  -- might be in scope without being in a `LangEnv`.
  type LangEnv =
    { varEnv   : Map String (Name, Info, LangDefVar)
    , conEnv   : Map String (Name, Info, LangDefCon)
    , tyConEnv : Map String (Name, Info, LangDefTyCon)
    }
  sem emptyLangEnv : () -> LangEnv
  sem emptyLangEnv = | _ ->
    { varEnv = mapEmpty cmpString
    , conEnv = mapEmpty cmpString
    , tyConEnv = mapEmpty cmpString
    }

  type LocalSemData =
    { local : Name
    , branches : Set BranchId
    , info : Info
    }
  type LangData =
    { sems : Map Name LocalSemData
    , info : Info
    }

  type LangState =
    { sems : Map Name
      { branches : [Branch]
      , preMatchArguments : Option (Int, Info)
      }
    , localToGlobalSems : Map Name Name
    , langs : Map Name (LangEnv, LangData)
    }
  syn Hook +=
  | MLangHook (Ref LangState)

  sem mergeLangEnvExn : Option Info -> LangEnv -> LangEnv -> LangEnv
  sem mergeLangEnvExn info l = | r ->
    let cmp : all a. String -> (Name, Info, a) -> (Name, Info, a) -> (Name, Info, a) = lam kind. lam l. lam r.
      match (l, r) with ((ln, li, ld), (rn, ri, rd)) in
      let definitionsAgree =
        if eqi (constructorTag ld) (constructorTag rd)
        then nameEq ln rn
        else false in
      if definitionsAgree then l else
      let msg = join ["Conflicting/duplicate definition of ", kind, " '", nameGetStr ln, "'"] in
      match info with Some info
      then errorExtra info (concat msg " in language composition:")
        [ (li, "Definition 1:")
        , (ri, "Definition 2:")
        ]
      else errorExtra ri msg [(li, "Original definition here:")] in
    { varEnv = mapUnionWith (cmp "value") l.varEnv r.varEnv
    , conEnv = mapUnionWith (cmp "constructor") l.conEnv r.conEnv
    , tyConEnv = mapUnionWith (cmp "type constructor") l.tyConEnv r.tyConEnv
    }

  sem mergeLangData : LangData -> LangData -> LangData
  sem mergeLangData l = | r ->
    let mergeLocalSemData = lam l. lam r.
      { local = r.local
      , branches = setUnion l.branches r.branches
      , info = r.info
      } in
    { sems = mapUnionWith mergeLocalSemData l.sems r.sems
    , info = l.info
    }

  -- NOTE(vipa, 2026-07-15): `_langPre*` functions run over *all*
  -- decls in a `lang` before their respective main phase is run for
  -- *any* of them. Used to properly support mutual recursion withing
  -- a `lang`, amongst other things.
  sem _langPreSymbolize : Ref LangState -> LangEnv -> SymEnv -> Loader -> Decl -> (LangEnv, SymEnv, Option Decl, Loader)
  sem _langSymbolize : LangEnv -> SymEnv -> Loader -> Decl -> (LangEnv, SymEnv, Option Decl, Loader)
  sem _langSymbolize langEnv symEnv loader = | decl ->
    match symbolizeDecl symEnv decl with (symEnv, decl) in
    (langEnv, symEnv, Some decl, loader)
  sem _langPreTypecheck : Loader -> Decl -> (Loader, Option Decl)
  sem _langTypecheck : Loader -> Decl -> (Loader, Option Decl)
  sem _langTypecheck loader = | decl ->
    match _withTCEnv (lam tcEnv. typeCheckDecl tcEnv decl) loader with (loader, decl) in
    (loader, Some decl)

  sem _langMergeAdjacent : (Decl, Decl) -> Option Decl
  sem _langMergeAdjacent = | _ -> None ()

  -- NOTE(vipa, 2026-07-15): This runs after typechecking is done for
  -- all decls in a lang
  sem _langAddDecl : Ref LangState -> LangData -> Loader -> Decl -> (LangData, Loader)
  -- NOTE(vipa, 2026-07-15): This runs after all decls have been
  -- typechecked and added, and should emit, e.g., fully composed
  -- `sem`s.
  sem _langEmit : Loader -> Ref LangState -> LangData -> Loader
  sem _langEmit loader stateRef = | langData ->
    let state = deref stateRef in
    let resymEnv = mapMap
      (lam global. optionMapOr global (lam x. x.local) (mapLookup global langData.sems))
      state.localToGlobalSems in
    let mkSem : Name -> LocalSemData -> DeclLetRecord = lam base. lam local.
      let global = mapLookupOrElse (lam. error "Compiler error: missing data in state.sems")
        base state.sems in
      let addOrder = lam dig. lam id.
        let branch = get global.branches id in
        addToDigraph local.info local.branches branch.orderCache dig in
      let dig = setFold addOrder (digraphEmpty subi (lam. lam. true)) local.branches in
      let branches = map (get global.branches) (digraphTopologicalOrder dig) in
      let scrutName = nameSym "scrut" in
      let paramNames = optionMapOr [] (lam x. create x.0 (lam. nameSym "sp")) global.preMatchArguments in
      let prepBody = lam.
        -- OPT(vipa, 2026-07-17): The body of this function could be
        -- delayed until later, as a "lazy" body, to minimize the
        -- amount of work per language fragment until we know the
        -- function will actually be used.
        let addBranch = lam branch. lam acc.
          match acc with (resymEnv, tm) in
          let tm = withType (tyTm branch.body) (match_ (withType (tyPat branch.pat) (nvar_ scrutName))
            branch.pat
            branch.body
            tm) in
          let resymEnv = foldl2 (lam resymEnv. lam prev. lam new. mapInsert prev new resymEnv)
            resymEnv
            branch.params.params
            paramNames in
          (resymEnv, tm) in
        let default = match_ (nvar_ scrutName) pvarw_ never_ never_ in
        match foldr addBranch (resymEnv, default) branches with (resymEnv, body) in
        resymbolizeExpr resymEnv body in
      let body = foldr nulam_ (prepBody ()) (snoc paramNames scrutName) in
      let ty = (_withTCEnv
        (lam tcEnv. (tcEnv, mapLookupOrElse (lam. error "Compiler error: missing signature for base") base tcEnv.varEnv))
        loader).1 in
      { ident = local.local
      , tyAnnot = ty
      , tyBody = ty
      , body = body
      , info = local.info
      } in
    let decl = DeclRecLets
      { bindings = mapValues (mapMapWithKey mkSem langData.sems)
      , info = langData.info
      } in
    _addTypecheckedDecl loader decl

  sem _addDeclExn symEnv loader +=
  | DeclLang x ->
    match
      match getHookOpt (lam x. match x with MLangHook x then Some x else None ()) loader
      with Some stateRef then (stateRef, loader) else
      let stateRef = ref
        { sems = mapEmpty nameCmp
        , langs = mapEmpty nameCmp
        , localToGlobalSems = mapEmpty nameCmp
        } in
      (stateRef, addHook loader (MLangHook stateRef))
    with (stateRef, loader) in

    let incSymEnv = _symEnvEmpty in
    let incLangEnv =
      { varEnv = mapEmpty cmpString
      , conEnv = mapEmpty cmpString
      , tyConEnv = mapEmpty cmpString
      } in
    let incLangData =
      { sems = mapEmpty nameCmp
      , info = x.info
      } in

    let state = deref stateRef in
    let f = lam acc. lam inc.
      match acc with (incSymEnv, incLangEnv, incLangData) in
      match inc with (n, info) in
      let n = getSymbol
        {kind = "language fragment", info = [info], allowFree = symEnv.allowFree}
        symEnv.namespaceEnv
        n in
      match mapLookup n symEnv.langEnv with Some langSymEnv in
      match mapLookup n state.langs with Some (langEnv, langData) in
      ( {incSymEnv with currentEnv = mergeNameEnv incSymEnv.currentEnv langSymEnv}
      , mergeLangEnvExn (Some x.info) incLangEnv langEnv
      , mergeLangData incLangData langData
      ) in
    match foldl f (incSymEnv, incLangEnv, incLangData) x.includes
      with (incSymEnv, incLangEnv, incLangData) in
    let mkIncSem = lam global. lam local. DeclSem
      { ident = nameNoSym (nameGetStr global)
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , impl = None ()
      , info = x.info
      , kind = SemSum {base = global}
      } in
    let incDecls = mapValues (mapMapWithKey mkIncSem incLangData.sems) in

    let f = lam loader.
      let symEnv = mergeSymEnv symEnv incSymEnv in
      let langEnv = incLangEnv in
      let langData = incLangData in
      recursive let mergeDecls = lam prev. lam decls.
        match decls with [a, b] ++ decls then
          match _langMergeAdjacent (a, b) with Some d
          then mergeDecls prev (cons d decls)
          else mergeDecls (snoc prev a) (cons b decls)
        else concat prev decls in
      let decls = concat incDecls (mergeDecls [] x.decls) in

      let symPre = lam acc. lam decl.
        match acc with (langEnv, symEnv, loader) in
        match _langPreSymbolize stateRef langEnv symEnv loader decl with (langEnv, symEnv, decl, loader) in
        ((langEnv, symEnv, loader), decl) in
      match mapAccumL symPre (langEnv, symEnv, loader) decls with ((langEnv, symEnv, loader), decls) in
      let decls = filterOption decls in

      let symNormal = lam acc. lam decl.
        match acc with (langEnv, symEnv, loader) in
        match _doHook _preSymbolize loader decl with (loader, decl) in
        match _langSymbolize langEnv symEnv loader decl with (langEnv, symEnv, decl, loader) in
        match decl with Some decl then
          match _doHook _postSymbolize loader decl with (loader, decl) in
          ((langEnv, symEnv, loader), Some decl)
        else ((langEnv, symEnv, loader), None ()) in
      match mapAccumL symNormal (langEnv, symEnv, loader) decls with ((langEnv, symEnv, loader), decls) in
      let decls = filterOption decls in

      let lvlPreTypecheck = (_withTCEnv (lam tcEnv. (tcEnv, tcEnv.currentLvl)) loader).1 in

      match mapAccumL _langPreTypecheck loader decls with (loader, decls) in
      let decls = filterOption decls in

      let tcNormal = lam loader. lam decl.
        match _doHook _preTypecheck loader decl with (loader, decl) in
        match _langTypecheck loader decl with (loader, decl) in
        match decl with Some decl
        then match _doHook _postTypecheck loader decl with (loader, decl) in (loader, Some decl)
        else (loader, None ()) in
      match mapAccumL tcNormal loader decls with (loader, decls) in
      let decls = filterOption decls in

      let lvlPostTypecheck = (_withTCEnv (lam tcEnv. (tcEnv, tcEnv.currentLvl)) loader).1 in
      (if neqi lvlPreTypecheck lvlPostTypecheck then
        error "Compiler error: tcEnv.currentLvl increased during lang typecheck, this would break `sem` typechecking in the general case."
       else ());

      let add = lam acc. lam decl.
        match acc with (langData, loader) in
        _langAddDecl stateRef langData loader decl in
      match foldl add (langData, loader) decls with (langData, loader) in

      let loader = _langEmit loader stateRef langData in

      ((langEnv, langData), loader)
    in
    match _captureEnv f loader with ((langEnv, langData), langSymEnv, loader) in

    let n = nameSetNewSym x.ident in

    let langSymEnv = mergeSymEnv incSymEnv langSymEnv in
    let state = deref stateRef in
    modref stateRef {state with langs = mapInsert n (langEnv, langData) state.langs};
    let updateSymEnv = lam symEnv.
      { symEnv with langEnv = mapInsert n langSymEnv.currentEnv symEnv.langEnv
      , namespaceEnv = mapInsert (nameGetStr n) n symEnv.namespaceEnv
      } in
    let symEnv = updateSymEnv symEnv in
    let loader = _updateFileEnv updateSymEnv loader in

    (symEnv, loader)

  sem _loadFile path += | (FMCore {includeMExpr = includeMExpr}, loader) ->
    let prog = switch result.consume (parseMLangFile path)
      case (_, Right prog) then prog
      case (_, Left errs) then
        errorMulti errs (join ["Parse error while parsing '", path, "'"])
      end in

    match includeBuiltinEnv loader with (env, loader) in
    match foldl (lam acc. _addDeclExn acc.0 acc.1) (env, loader) prog.decls with (env, loader) in
    if includeMExpr
    then (_addDeclExn env loader (declWithInfo (infoTm prog.expr) (ulet_ "" prog.expr))).1
    else loader
end

lang MLangTypeAlias = MLangLoader + TypeDeclAst
  sem _langPreSymbolize stateRef langEnv symEnv loader += | decl & DeclType {tyIdent = !TyVariant _} ->
    (langEnv, symEnv, Some decl, loader)

  sem _langSymbolize langEnv symEnv loader += | decl & DeclType {tyIdent = !TyVariant _} ->
    match symbolizeDecl symEnv decl with (symEnv, decl & DeclType x) in
    let langEnv = mergeLangEnvExn (None ()) langEnv
      {emptyLangEnv () with tyConEnv = mapSingleton cmpString (nameGetStr x.ident) (x.ident, x.info, LDAlias ())} in
    let loader = _addSymbolizedDeclExn loader decl in
    (langEnv, symEnv, None (), loader)
end

lang MLangSyn = MLangLoader + SynDeclAst
  sem _langPreSymbolize stateRef langEnv symEnv loader += | DeclSyn x ->
    match
      switch x.kind
      case SynBase _ then (nameSetNewSym x.ident, x.kind)
      case SynSum {base = base} then
        match mapLookup (nameGetStr base) langEnv.tyConEnv with Some (n, _, LDSyn _)
        then (n, SynSum {base = n})
        else errorSingle [x.info] (join ["There is no previously defined syn '", nameGetStr x.ident, "'."])
      end
    with (ident, kind) in
    let langEnv = mergeLangEnvExn (None ()) langEnv
      {emptyLangEnv () with tyConEnv = mapSingleton cmpString (nameGetStr x.ident) (ident, x.info, LDSyn ())} in
    let f = lam acc. lam def.
      match acc with (langEnv, conEnv) in
      match setSymbol conEnv def.ident with (conEnv, ident) in
      let langEnv = mergeLangEnvExn (None ()) langEnv
        {emptyLangEnv () with conEnv = mapSingleton cmpString (nameGetStr ident) (ident, def.info, LDCon ())} in
      ((langEnv, conEnv), {def with ident = ident}) in
    match mapAccumL f (langEnv, symEnv.currentEnv.conEnv) x.defs with ((langEnv, conEnv), defs) in
    let tyConEnv = mapInsert (nameGetStr ident) ident symEnv.currentEnv.tyConEnv in
    let symEnv = symbolizeUpdateConEnv (symbolizeUpdateTyConEnv symEnv tyConEnv) conEnv in
    let loader = match kind with SynBase _
      then _addSymbolizedDeclExn loader (DeclType
        { ident = ident
        , params = map nameSetNewSym x.params
        , info = x.info
        , tyIdent = tyWithInfo x.info (tyvariant_ [])
        })
      else loader in
    (langEnv, symEnv, Some (DeclSyn {x with ident = ident, kind = kind, defs = defs}), loader)

  sem _langSymbolize langEnv symEnv loader += | DeclSyn x ->
    let f = lam loader. lam def.
      let params = map nameSetNewSym x.params in
      let tyVarEnv = foldl
        (lam tyVarEnv. lam n. mapInsert (nameGetStr n) n tyVarEnv)
        symEnv.currentEnv.tyVarEnv
        params in
      let tyIdent = symbolizeType (symbolizeUpdateTyVarEnv symEnv tyVarEnv) def.tyIdent in
      let tyIdent = foldr ntyall_ (tyarrow_ tyIdent (tyapps_ (ntycon_ x.ident) (map ntyvar_ params))) params in
      _addSymbolizedDeclExn loader
        (DeclConDef {ident = def.ident, tyIdent = tyIdent, info = def.info}) in
    match foldl f loader x.defs with loader in
    (langEnv, symEnv, None (), loader)
end

lang MLangSem = MLangLoader + SemDeclAst + LetSym + PatTypeCheck + SubstituteUnknown + SubstituteNewReprs + ResolveType
  sem _langMergeAdjacent += | (DeclSem a, DeclSem b) ->
    match a.kind with SemBase _
    then match (a.tyAnnot, b.tyAnnot) with (!TyUnknown _, TyUnknown _)
      then match (a.impl, b.impl) with (None _, Some impl)
        then if nameEqStr a.ident b.ident
          then Some (DeclSem
            { ident = a.ident
            , tyAnnot = a.tyAnnot
            , tyBody = b.tyBody
            , impl = Some impl
            , info = mergeInfo a.info b.info
            , kind = b.kind
            })
          else None ()
        else None ()
      else None ()
    else None ()

  sem _langPreSymbolize stateRef langEnv symEnv loader += | DeclSem x ->
    match setSymbol symEnv.currentEnv.varEnv x.ident with (varEnv, ident) in
    let symEnv = symbolizeUpdateVarEnv symEnv varEnv in

    match
      switch x.kind
      case SemBase _ then
        ( mergeLangEnvExn (None ()) langEnv
          {emptyLangEnv () with varEnv = mapSingleton cmpString (nameGetStr ident) (ident, x.info, LDSem ())}
        , SemBase ()
        )
      case SemSum {base = base} then
        match mapLookup (nameGetStr base) langEnv.varEnv with Some (baseIdent, _, LDSem _) then
          let state = deref stateRef in
          modref stateRef {state with localToGlobalSems = mapInsert ident baseIdent state.localToGlobalSems};
          (langEnv, SemSum {base = baseIdent})
        else errorSingle [x.info] (join ["There is no previously defined sem '", nameGetStr base, "'."])
      end
    with (langEnv, kind) in

    (langEnv, symEnv, Some (DeclSem {x with ident = ident, kind = kind}), loader)

  sem _langSymbolize langEnv symEnv loader += | DeclSem x ->
    match symbolizeTyAnnot symEnv x.tyAnnot with (tyVarEnv, tyAnnot) in

    let symImpl = lam impl.
      let symEnv = symbolizeUpdateTyVarEnv symEnv tyVarEnv in
      let symParam = lam varEnv. lam param.
        match setSymbol varEnv param.ident with (varEnv, ident) in
        let tyAnnot = symbolizeType symEnv param.tyAnnot in
        (varEnv, {param with tyAnnot = tyAnnot, ident = ident}) in
      match mapAccumL symParam symEnv.currentEnv.varEnv impl.params with (varEnv, params) in
      let symEnv = symbolizeUpdateVarEnv symEnv varEnv in
      let symCase = lam caseImpl.
        match symbolizePat symEnv (mapEmpty cmpString) caseImpl.pat with (bodyVarEnv, pat) in
        let symEnv = symbolizeUpdateVarEnv symEnv (mapUnion symEnv.currentEnv.varEnv bodyVarEnv) in
        let body = symbolizeExpr symEnv caseImpl.body in
        {caseImpl with pat = pat, body = body} in
      {impl with params = params, cases = map symCase impl.cases} in
    let impl = optionMap symImpl x.impl in

    (langEnv, symEnv, Some (DeclSem {x with tyAnnot = tyAnnot, impl = impl}), loader)

  sem _langPreTypecheck loader += | DeclSem x ->
    _withTCEnv (lam tcEnv.
      let newLvl = addi 1 tcEnv.currentLvl in
      let tyAnnot = resolveType x.info tcEnv false x.tyAnnot in
      let tyAnnot = substituteNewReprs tcEnv tyAnnot in
      let tyBody = substituteUnknown x.info {tcEnv with currentLvl = newLvl} (Poly ()) tyAnnot in

      (switch x.kind
      case SemSum {base = base} then
        match mapLookup base tcEnv.varEnv with Some prevTy
        then unify tcEnv [infoTy tyBody] prevTy tyBody
        else ()
      case SemBase _ then ()
      end);

      (_insertVar x.ident tyBody tcEnv, Some (DeclSem {x with tyAnnot = tyAnnot, tyBody = tyBody}))) loader

  sem _langTypecheck loader +=
  | decl & DeclSem {impl = None _} -> (loader, Some decl)
  | DeclSem (x & {impl = Some impl}) ->
    let f = lam tcEnv.
      let newLvl = addi 1 tcEnv.currentLvl in
      let tyVarEnv = foldr (lam pair. mapInsert pair.0 (newLvl, pair.1)) tcEnv.tyVarEnv (stripTyAll x.tyBody).0 in
      let tcEnv = {tcEnv with tyVarEnv = tyVarEnv, currentLvl = addi 1 tcEnv.currentLvl} in

      recursive let collectParamTypes = lam acc. lam count. lam ty.
        switch (count, unwrapType ty)
        case (0, ty) then (acc, ty)
        case (_, TyAll x) then collectParamTypes acc count x.ty
        case (_, TyArrow x) then collectParamTypes (snoc acc x.from) (subi count 1) x.to
        case (_, ty) then
          let lhs = newmonovar tcEnv.currentLvl (infoTy ty) in
          let rhs = newpolyvar tcEnv.currentLvl (infoTy ty) in
          let expected = ityarrow_ x.info lhs rhs in
          unify tcEnv [infoTy ty] expected ty;
          collectParamTypes (snoc acc lhs) (subi count 1) rhs
        end in
      match collectParamTypes [] (addi (length impl.params) 1) x.tyBody with (inferredParams ++ [scrutTy], retTy) in
      let tcParam = lam tcEnv. lam pair.
        let param = switch pair
          case (param & {tyAnnot = TyUnknown _}, ty) then {param with tyAnnot = ty}
          case (param, _) then param
          end in
        let tyAnnot = resolveType param.info tcEnv false param.tyAnnot in
        let tyAnnot = substituteNewReprs tcEnv tyAnnot in
        let tyParam = substituteUnknown param.info tcEnv (Mono ()) tyAnnot in
        (_insertVar param.ident tyParam tcEnv, {param with tyAnnot = tyAnnot, tyParam = tyParam}) in
      match mapAccumL tcParam tcEnv (zip impl.params inferredParams) with (tcEnv, params) in

      let tcCase = lam c.
        match typeCheckPat tcEnv (mapEmpty nameCmp) c.pat with (patEnv, pat) in
        unify tcEnv [infoTy scrutTy, infoPat pat] scrutTy (tyPat pat);
        let matchEnv =
          { tcEnv with matchLvl = addi 1 tcEnv.matchLvl
          , varEnv = mapUnion tcEnv.varEnv patEnv
          } in
        let body = typeCheckExpr matchEnv c.body in
        unify tcEnv [infoTy retTy, infoTm body] retTy (tyTm body);
        {c with pat = pat, body = body} in
      let cases = map tcCase impl.cases in

      (tcEnv, DeclSem {x with impl = Some {impl with params = params, cases = cases}}) in

    -- NOTE(vipa, 2026-07-16): We intentionally drop tcEnv, because it
    -- was only relevant for the body, not after
    let decl = (_withTCEnv f loader).1 in
    (loader, Some decl)

  sem _langAddDecl stateRef langData loader +=
  | DeclSem x ->
    let state = deref stateRef in
    let base = switch x.kind
      case SemBase _ then x.ident
      case SemSum x then x.base
      end in

    let semGlobalData = mapLookupOrElse (lam. {branches = [], preMatchArguments = None ()}) base state.sems in
    match
      match x.impl with Some impl then
        let mergePreMatch = lam l. lam r.
          if eqi l.0 r.0 then l else
          errorExtra r.1
            (join ["This 'sem' has ", int2string r.0, " pre-match argument(s), expected ", int2string l.0, ":"])
            [(l.1, join ["Previous definition (with ", int2string l.0, " pre-match argument(s)):"])] in
        let preMatchArguments = optionOrWith mergePreMatch
          semGlobalData.preMatchArguments
          (Some (length impl.params, x.info)) in
        let params =
          { params = map (lam p. p.ident) impl.params
          , tyParams = map (lam p. p.0) (stripTyAll x.tyBody).0
          } in
        let addBranch = lam branches. lam c.
          let id = length branches in
          (snoc branches (mkBranch branches params c.pat c.body), id) in
        match mapAccumL addBranch semGlobalData.branches impl.cases with (branches, newBranches) in
        let semGlobalData = {semGlobalData with branches = branches, preMatchArguments = preMatchArguments} in
        (semGlobalData, newBranches)
      else
        (semGlobalData, [])
    with (semGlobalData, newBranches) in
    let state = {state with sems = mapInsert base semGlobalData state.sems} in

    let semLocalData = mapLookupOrElse
      (lam. {local = x.ident, branches = setEmpty subi, info = x.info})
      base
      langData.sems in
    let semLocalData =
      { semLocalData with local = x.ident
      , branches = setUnion semLocalData.branches (setOfSeq subi newBranches)
      , info = x.info
      } in
    let langData = {langData with sems = mapInsert base semLocalData langData.sems} in

    modref stateRef state;
    (langData, loader)
end

let updateEnv : SymEnv -> NameEnv -> SymEnv = lam symEnv. lam langEnv.
  {symEnv with currentEnv = mergeNameEnv (symEnv.currentEnv) langEnv}

lang DeclUseSym = Sym + UseDeclAst + DeclAst + RecLetsDeclAst
  sem symbolizeDecl env +=
  | DeclUse x ->
    let n = getSymbol {kind = "language fragment", info = [x.info], allowFree = env.allowFree}
      env.namespaceEnv x.ident in
    match mapLookup n env.langEnv with Some langEnv
    -- NOTE(vipa, 2026-07-16): An empty reclets decl is a no-op decl,
    -- so this is a way to remove the DeclUse
    then (updateEnv env langEnv, DeclRecLets {bindings = [], info = x.info})
    else if env.allowFree
      then (env, DeclUse {x with ident = n})
      else error "Compiler error: missing langEnv"
end

lang TyUseSym = Sym + TyUseAst
  sem symbolizeType env +=
  | TyUse x ->
    let n = getSymbol {kind = "language fragment", info = [x.info], allowFree = env.allowFree}
      env.namespaceEnv x.ident in
    match mapLookup n env.langEnv with Some langEnv
      then symbolizeType (updateEnv env langEnv) x.inty
      else if env.allowFree
        then TyUse {x with inty = symbolizeType env x.inty}
        else error "Compiler error: missing langEnv"
end

lang ComposedMLangLoader
  = MLangTypeAlias + MLangSyn + MLangSem + MExprResymbolize + MExprSym + DeclUseSym + TyUseSym
  + MExprTypeCheck + MExprPatAnalysis + IncludeLoader
end

mexpr

-- use MCoreLoader in
-- use MExprCmp in

-- -- TODO(vipa, 2024-11-28): In the absence of proper comparison of
-- -- decls, we just compare the contained exprs
-- let declCmp = lam a. lam b.
--   let as = sfold_Decl_Expr snoc [] a in
--   let bs = sfold_Decl_Expr snoc [] b in
--   seqCmp cmpExpr as bs in

-- -- Loading actually loads something
-- let loader = mkLoader _symEnvEmpty typcheckEnvDefault [] in
-- match includeFileExn (sysGetCwd ()) "stdlib::bool.mc" loader with (symEnv, loader) in
-- utest length (getDecls loader) with 1 using lam count. lam limit. geqi count limit in
-- utest mapLookup "eqBool" symEnv.env.currentEnv.varEnv with () using lam x. lam. optionIsSome x in

-- -- Inclusion is idempotent
-- let loader = mkLoader _symEnvEmpty typcheckEnvDefault [] in
-- let loader = (includeFileExn (sysGetCwd ()) "stdlib::seq.mc" loader).1 in
-- let boolDecls = getDecls loader in
-- let loader = (includeFileExn (sysGetCwd ()) "stdlib::seq.mc" loader).1 in
-- utest boolDecls with getDecls loader using lam a. lam b. eqi 0 (seqCmp declCmp a b) in

use ComposedMLangLoader in

(match argv with [_] then exit 0 else ());
match argv with [_, input] ++ _ in

let loader = mkLoader typcheckEnvDefault [] in
let loader = (includeFileTypeExn (FMCore {includeMExpr = true}) "." input loader).1 in
let ast = buildFullAst loader in

-- printLn (expr2str ast);
-- exit 1;

-- let ocamlCompile : [String] -> [String] -> String -> String = lam libs. lam clibs. lam prog.
--   let opts =
--     { defaultCompileOptions
--     with libraries = libs
--     , cLibraries = clibs
--     } in
--   let res = ocamlCompileWithConfig opts prog in
--   sysMoveFile res.binaryPath output;
--   sysChmodWriteAccessFile output;
--   res.cleanup ();
--   output in

-- let hooks = mkEmptyHooks ocamlCompile in
-- let ast = lowerAll ast in

()
