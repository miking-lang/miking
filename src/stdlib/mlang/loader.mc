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

include "mexpr/boot-parser.mc"
include "stdlib.mc"
include "ast.mc"
include "symbolize.mc"
include "type-check.mc"
include "pprint.mc"
include "mexpr/json-debug.mc"

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

lang MCoreLoader
  = Ast + DeclAst + DeclSym + DeclTypeCheck + SymGetters

  -- The loader itself
  syn Loader =
  -- How to load a given file
  syn FileType =


  -- === External interface, when using a Loader ===

  sem mkLoader : SymEnv -> TCEnv -> [Hook] -> Loader
  sem addHook : Loader -> Hook -> Loader
  sem remHook : (Hook -> Bool) -> Loader -> Loader
  sem hasHook : (Hook -> Bool) -> Loader -> Bool
  sem withHookState : all a. (Loader -> Hook -> Option (Loader, a)) -> Loader -> (Loader, a)
  -- Include a file (second String) relative to a directory (first
  -- String). Returns a symbolization enviroment containing only
  -- definitions from that specific file
  sem includeFileExn : String -> String -> Loader -> ({path : String, env : SymEnv}, Loader)
  sem includeFileExn dir path = | loader -> includeFileTypeExn (_fileType path) dir path loader
  sem includeFileTypeExn : FileType -> String -> String -> Loader -> ({path : String, env : SymEnv}, Loader)
  sem getDecls : Loader -> [Decl]
  sem buildFullAst : Loader -> Expr


  -- === Internal interface, for supporting new files

  -- Called with a fully resolved path to a file to load. Paired to
  -- enable special handling based on file type. Should ensure that
  -- the same file isn't loaded twice.
  sem _loadFile : String -> (FileType, Loader) -> (SymEnv, Loader)

  -- Called to automatically determine how to load a given file based
  -- on its path, typically by the file extension.
  sem _fileType : String -> FileType
  sem _fileType =
  | path -> errorSingle [] "No known handler for this file"

  -- Used to carry extra state for hooks
  syn Hook =

  -- Add decls to the loader. Added code is symbolized and
  -- type-checked, unless the used function contains `Symbolized` (in
  -- which case only type-checking is run) or `Typechecked` (in which
  -- case neither is run). The `WithEnv` variant runs symbolize with
  -- the given environment instead of the running one. Note that new
  -- names are still added to the running environment as well.
  sem _addDeclExn : Loader -> Decl -> Loader
  sem _addDeclWithEnvExn : SymEnv -> Loader -> Decl -> (SymEnv, Loader)
  sem _addSymbolizedDeclExn : Loader -> Decl -> Loader
  sem _addTypecheckedDecl : Loader -> Decl -> Loader

  -- Symbolization related functions
  sem _getSymEnv : Loader -> SymEnv
  sem _setSymEnv : SymEnv -> Loader -> Loader

  -- Type-checking related functions
  sem _getTCEnv : Loader -> TCEnv
  sem _setTCEnv : TCEnv -> Loader -> Loader

  -- Hooks for additional processing around each phase
  sem _preSymbolize : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _preSymbolize loader decl = | _ -> (loader, decl)
  sem _postSymbolize : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _postSymbolize loader decl = | _ -> (loader, decl)
  sem _preTypecheck : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _preTypecheck loader decl = | _ -> (loader, decl)
  sem _postTypecheck : Loader -> Decl -> Hook -> (Loader, Decl)
  sem _postTypecheck loader decl = | _ -> (loader, decl)
end

-- Use MCore-style path resolution, e.g., using libraries set in
-- MCORE_LIBS
lang MCorePathResolution = MCoreLoader
  sem includeFileTypeExn ftype dir path = | loader ->
    let resolved = stdlibResolveFileOr (lam x. error x) dir path in
    match _loadFile resolved (ftype, loader) with (env, loader) in
    ({path = resolved, env = env}, loader)
end

lang BootParserLoader = MCorePathResolution + DeclAst + ExprAsDecl + BootParser
  + LetDeclAst + RecLetsDeclAst + TypeDeclAst + DataDeclAst + ExtDeclAst
  + MLangPrettyPrint + AstToJson
  type LoaderRec =
    { decls : [Decl]
    -- NOTE(vipa, 2024-11-27): We check each Decl if their info field
    -- points to a file in this set. The set is updated only after all
    -- decls from a file have been filtered (but before they've been
    -- added, symbolized, and type-checked), thus we can do simpler
    -- de-duplication than previously.
    , includedFiles : Map String SymEnv
    , symEnv : SymEnv
    , tcEnv : TCEnv
    , hooks : [Hook]
    }
  syn Loader =
  | Loader LoaderRec
  syn FileType =
  | FMCore ()

  sem mkLoader symEnv tcEnv = | hooks -> Loader
    { decls = []
    , includedFiles = mapEmpty cmpString
    , symEnv = symEnv
    , tcEnv = tcEnv
    , hooks = hooks
    }
  sem addHook loader = | hook ->
    match loader with Loader x in
    Loader {x with hooks = snoc x.hooks hook}
  sem remHook check = | Loader x ->
    Loader {x with hooks = filter (lam x. not (check x)) x.hooks}
  sem hasHook check = | Loader x ->
    optionIsSome (find check x.hooks)
  sem withHookState f = | loader & Loader x ->
    match findMap (f loader) x.hooks with Some res
    then res
    else error "Compiler error: missing hook in loader"

  sem _getSymEnv = | Loader x -> x.symEnv
  sem _setSymEnv symEnv = | Loader x -> Loader {x with symEnv = symEnv}

  sem _getTCEnv = | Loader x -> x.tcEnv
  sem _setTCEnv tcEnv = | Loader x -> Loader {x with tcEnv = tcEnv}

  sem getDecls = | Loader x -> x.decls
  sem buildFullAst = | Loader x -> foldr (lam decl. lam cont. declAsExpr cont decl) unit_ x.decls

  sem _fileType = | _ ++ ".mc" -> FMCore ()

  sem _loadFile path = | (FMCore _, loader & Loader x) ->
    -- NOTE(vipa, 2024-12-05): Don't reload previously loaded files
    match mapLookup path x.includedFiles with Some symEnv then (symEnv, loader) else
    let args =
      { _defaultBootParserParseMCoreFileArg ()
      -- NOTE(vipa, 2024-12-03): It's important to not remove dead
      -- code, because that code might end up not-dead later, at which
      -- point it would end up included then, out of order and in
      -- various ways messing with assumptions made in the loader.
      with eliminateDeadCode = false
      -- NOTE(vipa, 2024-12-03): This largely lets us error later,
      -- which gives better error messages.
      , allowFree = true
      } in
    let ast = parseMCoreFile args path in
    recursive let f = lam decls. lam ast.
      match exprAsDecl ast with Some (decl, ast)
      then f (snoc decls decl) ast
      else decls in
    match _addDeclsByFile loader (f [] ast) with loader & Loader x in
    match mapLookup path x.includedFiles with Some env
    then (env, loader)
    else (_symEnvEmpty, Loader {x with includedFiles = mapInsert path _symEnvEmpty x.includedFiles})

  -- Conceptually, take a list of decls from multiple files, split them to one list per file
  sem _addDeclsByFile : Loader -> [Decl] -> Loader
  sem _addDeclsByFile loader =
  | [first] ++ rest ->
    let getFName = lam decl.
      match infoDecl decl with Info {filename = filename}
      then filename
      else errorSingle [] "Missing info for decl" in
    recursive
      let newFile = lam filename. lam decl. lam loader. lam decls.
        match loader with Loader x in
        if mapMem filename x.includedFiles then
          dropNext filename loader decls
        else
          let loader = Loader {x with includedFiles = mapInsert filename _symEnvEmpty x.includedFiles} in
          addNext filename (_addDeclExn loader decl) decls
      let addNext = lam currFilename. lam loader. lam decls.
        match decls with [decl] ++ decls then
          let newFilename = getFName decl in
          if eqString newFilename currFilename then
            addNext currFilename (_addDeclExn loader decl) decls
          else
            newFile newFilename decl loader decls
        else loader
      let dropNext = lam currFilename. lam loader. lam decls.
        match decls with [decl] ++ decls then
          let newFilename = getFName decl in
          if eqString newFilename currFilename then
            dropNext currFilename loader decls
          else
            newFile newFilename decl loader decls
        else loader
    in newFile (getFName first) first loader rest
  | [] -> loader

  sem _doHook : (Loader -> Decl -> Hook -> (Loader, Decl)) -> Loader -> Decl -> (Loader, Decl)
  sem _doHook f loader = | decl ->
    match loader with Loader {hooks = hooks} in
    foldl (lam acc. lam cb. f acc.0 acc.1 cb) (loader, decl) hooks

  sem _addDeclWithEnvExn symEnv loader = | decl ->
    match _doHook _preSymbolize loader decl with (Loader x, decl) in
    match symbolizeDecl symEnv decl with (newEnv, decl) in
    let symEnv = _addDefinition x.symEnv decl in
    match _doHook _postSymbolize (Loader {x with symEnv = symEnv}) decl with (loader, decl) in

    match _doHook _preTypecheck loader decl with (Loader x, decl) in
    match typeCheckDecl x.tcEnv decl with (tcEnv, decl) in
    match _doHook _postTypecheck (Loader {x with tcEnv = tcEnv}) decl with (Loader x, decl) in

    let includedFiles = match infoDecl decl with Info {filename = filename}
      then mapUpdate filename (optionMap (lam env. _addDefinition env decl)) x.includedFiles
      else x.includedFiles in

    (newEnv, Loader {x with decls = snoc x.decls decl, includedFiles = includedFiles})

  sem _addDeclExn loader = | decl ->
    match _doHook _preSymbolize loader decl with (Loader x, decl) in
    match symbolizeDecl x.symEnv decl with (symEnv, decl) in
    match _doHook _postSymbolize (Loader {x with symEnv = symEnv}) decl with (loader, decl) in

    match _doHook _preTypecheck loader decl with (Loader x, decl) in
    match typeCheckDecl x.tcEnv decl with (tcEnv, decl) in
    match _doHook _postTypecheck (Loader {x with tcEnv = tcEnv}) decl with (Loader x, decl) in

    let includedFiles = match infoDecl decl with Info {filename = filename}
      then mapUpdate filename (optionMap (lam env. _addDefinition env decl)) x.includedFiles
      else x.includedFiles in

    Loader {x with decls = snoc x.decls decl, includedFiles = includedFiles}

  sem _addSymbolizedDeclExn loader = | decl ->
    match _doHook _preTypecheck loader decl with (Loader x, decl) in
    match typeCheckDecl x.tcEnv decl with (tcEnv, decl) in
    match _doHook _postTypecheck (Loader {x with tcEnv = tcEnv}) decl with (Loader x, decl) in

    let includedFiles = match infoDecl decl with Info {filename = filename}
      then mapUpdate filename (optionMap (lam env. _addDefinition env decl)) x.includedFiles
      else x.includedFiles in

    Loader {x with decls = snoc x.decls decl}

  sem _addTypecheckedDecl loader = | decl ->
    match loader with Loader x in

    let includedFiles = match infoDecl decl with Info {filename = filename}
      then mapUpdate filename (optionMap (lam env. _addDefinition env decl)) x.includedFiles
      else x.includedFiles in

    Loader {x with decls = snoc x.decls decl}

  sem _addDefinition : SymEnv -> Decl -> SymEnv
  sem _addDefinition env =
  | _ -> env
  | DeclLet t ->
    let varEnv = mapInsert (nameGetStr t.ident) t.ident env.currentEnv.varEnv in
    symbolizeUpdateVarEnv env varEnv
  | DeclType t ->
    let tyConEnv = mapInsert (nameGetStr t.ident) t.ident env.currentEnv.tyConEnv in
    symbolizeUpdateTyConEnv env tyConEnv
  | DeclRecLets t ->
    let add = lam acc. lam b. mapInsert (nameGetStr b.ident) b.ident acc in
    let varEnv = foldl add env.currentEnv.varEnv t.bindings in
    symbolizeUpdateVarEnv env varEnv
  | DeclConDef t ->
    let conEnv = mapInsert (nameGetStr t.ident) t.ident env.currentEnv.conEnv in
    symbolizeUpdateConEnv env conEnv
  | DeclExt t ->
    let varEnv = mapInsert (nameGetStr t.ident) t.ident env.currentEnv.varEnv in
    symbolizeUpdateVarEnv env varEnv
end

lang MCoreLoader
  = MCorePathResolution + BootParserLoader + MExprAsDecl
  + MExprSym + MLangSym
  + MExprTypeCheck + MLangTypeCheck
end

mexpr

use MCoreLoader in
use MExprCmp in

-- TODO(vipa, 2024-11-28): In the absence of proper comparison of
-- decls, we just compare the contained exprs
let declCmp = lam a. lam b.
  let as = sfold_Decl_Expr snoc [] a in
  let bs = sfold_Decl_Expr snoc [] b in
  seqCmp cmpExpr as bs in

-- Loading actually loads something
let loader = mkLoader _symEnvEmpty typcheckEnvDefault [] in
match includeFileExn (sysGetCwd ()) "stdlib::bool.mc" loader with (symEnv, loader) in
utest length (getDecls loader) with 1 using lam count. lam limit. geqi count limit in
utest mapLookup "eqBool" symEnv.env.currentEnv.varEnv with () using lam x. lam. optionIsSome x in

-- Inclusion is idempotent
let loader = mkLoader _symEnvEmpty typcheckEnvDefault [] in
let loader = (includeFileExn (sysGetCwd ()) "stdlib::seq.mc" loader).1 in
let boolDecls = getDecls loader in
let loader = (includeFileExn (sysGetCwd ()) "stdlib::seq.mc" loader).1 in
utest boolDecls with getDecls loader using lam a. lam b. eqi 0 (seqCmp declCmp a b) in

()
