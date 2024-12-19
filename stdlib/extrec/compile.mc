include "mlang/ast.mc"
include "mlang/ast-builder.mc"
include "mlang/compile.mc"
include "mlang/pprint.mc"
include "mlang/symbolize.mc"
include "mlang/composition-check.mc"
include "mlang/language-composer.mc"

include "mexpr/eval.mc"
include "mexpr/eq.mc"
include "mexpr/utils.mc"

include "ast.mc"

include "common.mc"
include "option.mc"
include "map.mc"
include "bool.mc"
include "name.mc"
include "error.mc"
include "set.mc"
include "result.mc"

let isCosynDecl = use ExtRecAst in
  lam d. match d with DeclCosyn _ then true else false
let isCosemDecl = use ExtRecAst in
  lam d. match d with DeclCosem _ then true else false
let isProdDecl = use ExtRecAst in
  lam d. match d with SynDeclProdExt _ then true else false

lang SynPayloadTypesDeclCompiler = SynDeclAst + ExtRecordAst
  sem compileSynPayloadTypes : CompilationContext -> Decl -> CompilationContext
  sem compileSynPayloadTypes ctx =
  | DeclSyn s ->
    -- Generate a record type for each definition in the syntax type.
    let work = lam ctx. lam def.
      withExpr ctx (TmRecType {ident = def.tyName,
                               params = s.params,
                               ty = tyunknown_,
                               inexpr = uunit_,
                               info = infoTy def.tyIdent}) in
    foldl work ctx s.defs
end

lang SynProdDeclCompiler = SynProdExtDeclAst + ExtRecordAst + RecordTypeAst
  sem compileSynProd : String -> CompilationContext -> Decl -> CompilationContext
  sem compileSynProd langStr ctx =
  | SynDeclProdExt s ->
    match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap
    with Some baseIdent in

    -- Compile indiv ext
    let compileExt = lam ctx. lam ext.
      match ext with {ident = ident, tyIdent = tyIdent} in
      match mapLookup ident ctx.conToExtType with Some recIdent in
      match tyIdent with TyRecord rec in
      let work = lam acc. lam sid. lam ty.
          let label = sidToString sid in
          let tyIdent = tyarrow_ (ntycon_ recIdent) ty in
          withExpr acc (TmRecField {label = label,
                                    tyIdent = nstyall_ (head s.params) (data_ recIdent) tyIdent,
                                    inexpr = uunit_,
                                    ty = tyunknown_,
                                    info = infoTy ty})
      in
      mapFoldWithKey work ctx rec.fields
    in
    let ctx = foldl compileExt ctx s.individualExts in

    -- Compile global ext
    match s.globalExt with Some globalExt then
      -- Global extension is currently unsupported so we just throw an error
      errorSingle [s.info] "* Global Product Extension is not supported!"
      -- match mapLookup s.ident ctx.baseMap with Some baseIdent in
      -- match mapLookup baseIdent ctx.baseToCons with Some allConstructors in
      -- let explicitConstructors = setOfSeq nameCmp (map (lam e. e.ident) s.individualExts) in

      -- let relevantCons = setSubtract allConstructors explicitConstructors in

      -- match globalExt with TyRecord rec in

      -- let compileGlobalExt = lam ctx. lam ident.
      --   match mapLookup ident ctx.conToExtType with Some recIdent in
      --   let work = lam acc. lam sid. lam ty.
      --     let label = sidToString sid in
      --     let tyIdent = tyarrow_ (ntycon_ recIdent) ty in
      --       withExpr acc (TmRecField {label = label,
      --                                 tyIdent = nstyall_ mapParamIdent (data_ s.ident) tyIdent,
      --                                 inexpr = uunit_,
      --                                 ty = tyunknown_,
      --                                 info = infoTy ty})
      --   in
      --   mapFoldWithKey work ctx rec.fields
      -- in

      -- let ctx = setFold compileGlobalExt ctx relevantCons in

      -- let newGlobalExt = mergeRecordTypes
      --   (mapLookupOrElse (lam. tyrecord_ []) baseIdent ctx.globalFields)
      --   globalExt in

      -- {ctx with globalFields = mapInsert baseIdent newGlobalExt ctx.globalFields}
    else
      ctx
end

lang ExtrecSynDefCompiler = SynDeclAst + ExtRecordAst + MExprAst
  sem compileSynConstructors : String -> CompilationContext -> Decl -> CompilationContext
  sem compileSynConstructors langStr ctx =
  | DeclSyn s ->
    match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap
    with Some baseIdent in

    let forallWrapper : Type -> Type =
      lam ty.
        let ty = foldl (lam ty. lam n. ntyall_ n ty) ty (tail s.params) in
        nstyall_ (head s.params) (data_ baseIdent) ty
    in

    let conappWrapper : Type -> Type = lam ty.
      foldl tyapp_ ty (map ntyvar_ (tail s.params)) in

    let tyconApp = TyCon {info = s.info, ident = baseIdent, data = intyvar_ s.info (head s.params)} in
    -- let tyconApp = foldl (lam acc. lam n. tyapp_ acc (intyvar_ s.info n)) (ntycon_ baseIdent) s.params in

    let compileDef = lam ctx. lam def : {ident : Name, tyIdent : Type, tyName : Name}.
      match def.tyIdent with TyRecord _ then
        let tyIdent = mergeRecordTypes
          def.tyIdent
          (mapLookupOrElse (lam. tyrecord_ []) baseIdent ctx.globalFields) in
        match tyIdent with TyRecord rec in

        let recIdent = def.tyName in
        let ctx = {ctx with conToExtType = mapInsert def.ident recIdent ctx.conToExtType} in

        let work = lam ctx. lam sid. lam ty.
          let label = sidToString sid in
          let tyIdent = tyarrow_ (conappWrapper (ntycon_ recIdent)) ty in
          withExpr ctx (TmRecField {label = label,
                                    tyIdent = forallWrapper tyIdent,
                                    inexpr = uunit_,
                                    ty = tyunknown_,
                                    info = infoTy ty}) in
        let ctx = mapFoldWithKey work ctx rec.fields in
        let lhs = TyCon {info = infoTy def.tyIdent,
                         ident = recIdent,
                         data = intyvar_ s.info (head s.params)} in
        withExpr ctx (TmConDef {ident = def.ident,
                                tyIdent = forallWrapper (tyarrow_ (conappWrapper lhs) (conappWrapper tyconApp)),
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info})
      else
        withExpr ctx (TmConDef {ident = def.ident,
                                tyIdent = forallWrapper (tyarrow_ def.tyIdent tyconApp),
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info})
    in
    let ctx = foldl compileDef ctx s.defs in

    -- Update baseToCons map
    let newSet = foldr
      setInsert
      (mapLookupOrElse (lam. setEmpty nameCmp) baseIdent ctx.baseToCons)
      (map (lam d. d.ident) s.defs) in
    let ctx = {ctx with baseToCons = mapInsert baseIdent newSet ctx.baseToCons} in

    ctx
end

lang CosemDeclCompiler = CosemDeclAst + MExprAst + ExtRecAst + MExprSubstitute
  sem compileCosem langStr ctx cosemNames =
  | DeclCosem d ->
    match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.cosemCaseMap
    with Some cases in

    if setIsEmpty cases then
      let result = TmExtRecord {ident = d.targetTyIdent,
                                bindings = mapEmpty cmpString,
                                info = d.info,
                                ty = tyunknown_} in
      let body = foldl (lam acc. lam arg. nulam_ arg.ident acc) result d.args in
      {ident = d.ident,
       tyAnnot = d.tyAnnot,
       tyBody = tyunknown_,
       body = body,
       info = d.info}
    else
      let cases = setToSeq cases in

      let syms = mapi (lam i. lam. (nameSym (concat "cosemResult" (int2string i)))) cases in

      let argsIdents = map (lam a. a.ident) d.args in

      let pairs = mapi (lam i. lam c. (get syms i, c)) cases in

      let compileThn = lam acc : Expr. lam pair : (Name, ExtendedCopat).
        match pair with (ident, c) in

        match mapLookup c.orig ctx.compositionCheckEnv.semArgsMap with Some (Some origArgs) in
        let pairs = join [zip origArgs argsIdents,
                          createPairsForSubst ctx c.orig.0 langStr] in
        let subst = mapFromSeq nameCmp pairs in
        let thn = substituteIdentifiersExpr subst c.thn in
        bind_ (nulet_ ident thn) acc in

      let f = lam acc. lam i. lam c.
        match c with {copat = RecordCopat {fields = fields}} in
        let g = lam acc. lam str.
          mapInsert str (recordproj_ str (nvar_ (get syms i))) acc in
        foldl g acc fields
      in
      let bindings = foldli f (mapEmpty cmpString) cases in
      let creator = TmExtRecord {ident = d.targetTyIdent,
                                 bindings = bindings,
                                 info = d.info,
                                 ty = tyunknown_} in

      let expr = foldl compileThn creator pairs in
      let expr = foldl (lam acc. lam arg. nulam_ arg.ident acc) expr (reverse d.args) in

      {ident = d.ident,
       tyAnnot = d.tyAnnot,
       tyBody = tyunknown_,
       body = expr,
       info = d.info}
end

lang CosynDeclCompiler = CosynDeclAst + RecordTypeAst + ExtRecAst
  sem compileCosyn : String -> CompilationContext -> Decl -> CompilationContext
  sem compileCosyn langStr ctx =
  | DeclCosyn s ->
    match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap
    with Some baseIdent in

    let ctx = if s.isBase
              then withExpr ctx (TmRecType {ident = s.ident,
                                            params = s.params,
                                            info = s.info,
                                            ty = tyunknown_,
                                            inexpr = uunit_})
              else ctx in

    let wrap = lam ty. lam n. nstyall_ n (data_ baseIdent) ty in

    let compileField = lam ctx. lam sid. lam ty.
      let tyIdent = tyarrow_ (ntycon_ baseIdent) ty in
      withExpr ctx (TmRecField {label = sidToString sid,
                                tyIdent = foldl wrap tyIdent s.params,
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info}) in

    match s.ty with TyRecord rec then
      mapFoldWithKey compileField ctx rec.fields
    else
      errorSingle [s.info] (join [
        " * A cosyn can only have record types as their type!"
      ])
end

lang ExtRecLangDeclCompiler = DeclCompiler + LangDeclAst + MExprAst + SemDeclAst +
                              SynDeclAst + TypeDeclAst + SynProdExtDeclAst +
                              ExtRecordAst + CosynDeclAst +
                              CosemDeclAst + RecordCopatAst +
                              SynTypeDeclCompiler + SynPayloadTypesDeclCompiler +
                              CosynDeclCompiler + ExtrecSynDefCompiler +
                              SynProdDeclCompiler + CosemDeclCompiler +
                              SemDeclCompiler
  sem compileDecl ctx =
  | DeclLang l ->
    let langStr = nameGetStr l.ident in

    let typeDecls = filter isTypeDecl l.decls in
    let synDecls = filter isSynDecl l.decls in
    let cosynDecls = filter isCosynDecl l.decls in
    let semDecls = filter isSemDecl l.decls in
    let cosemDecls = filter isCosemDecl l.decls in
    let prodDecls = filter isProdDecl l.decls in

    let nameSeq =  (map (lam s. match s with DeclSem s in (nameGetStr s.ident, s.ident)) semDecls) in
    let semNames = mapFromSeq cmpString nameSeq in

    let ctx = foldl withSemSymbol ctx (map (lam s. match s with DeclSem s in s.ident) semDecls) in

    let ctx = foldl compileSynType ctx synDecls in
    let ctx = foldl compileSynPayloadTypes ctx synDecls in
    let res = result.foldlM compileDecl ctx typeDecls in
    let res = result.map (lam ctx. foldl (compileCosyn langStr) ctx cosynDecls) res in
    let res = result.map (lam ctx. foldl (compileSynConstructors langStr) ctx synDecls) res in
    let res = result.map (lam ctx. foldl (compileSynProd langStr) ctx prodDecls) res in

    let compileSemToResult : CompilationContext -> [Decl] -> [Decl] -> CompilationContext
      = lam ctx. lam sems. lam cosems.
        let semBindings = map (compileSem langStr ctx semNames) sems in
        let cosemBindings = map (compileCosem langStr ctx semNames) cosems in
        withExpr ctx (TmRecLets {bindings = concat semBindings cosemBindings,
                                 inexpr = uunit_,
                                 ty = tyunknown_,
                                 info = l.info})
    in
    result.map (lam ctx. compileSemToResult ctx semDecls cosemDecls) res
  | DeclSyn s ->
    error "Unexpected DeclSyn"
  | DeclSem s ->
    error "Unexpected DeclSem!"
end

lang MLangTopLevelCompiler = MLangTopLevel + DeclCompiler + LangDeclAst + SynDeclAst
  sem _gatherBaseSemNames : Set Name -> Decl -> Set Name
  sem _gatherBaseSemNames acc =
  | DeclLang d ->
    foldl _gatherBaseSemNames acc d.decls
  | DeclSyn {includes = [], ident = ident} ->
    setInsert ident acc
  | _ -> acc


  sem compileProg : CompilationContext -> MLangProgram -> CompilationResult
  sem compileProg ctx =
  | prog ->
    let ctx = {ctx with allBaseSyns = foldl _gatherBaseSemNames (setEmpty nameCmp) prog.decls} in

    let res = result.foldlM compileDecl ctx prog.decls in
    result.map (lam ctx. withExpr ctx prog.expr) res
end

lang MLangCompiler = MLangAst + MExprAst +
                     MLangTopLevelCompiler + ExtDeclCompiler +
                     ConDefDeclCompiler + TypeDeclCompiler + UtestDeclCompiler +
                     RecletsDeclCompiler + LetDeclCompiler
  sem compile : CompilationContext -> MLangProgram -> Result CompilationWarning CompilationError Expr
  sem compile ctx =| prog ->
    match result.consume (compileProg ctx prog) with (_, res) in
    switch res
      case Left err then
        result.err (head err)
      case Right ctx then
        result.ok (bindall_ (concat ctx.toplevelExprs ctx.exprs))
    end
end

lang ExtRecCompiler = MLangCompiler + ExtRecLangDeclCompiler
end