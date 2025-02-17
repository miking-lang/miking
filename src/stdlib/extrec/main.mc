-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input.
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "map.mc"
include "seq.mc"
include "stringid.mc"

include "boot-parser.mc"
include "symbolize.mc"
include "collect-env.mc"
include "conapp-sugar.mc"
include "pprint.mc"
include "compile.mc"
include "type-check.mc"
include "monomorphise.mc"
include "cosem-ty-annot.mc"
include "resolve-qualified-name.mc"
include "mlang-ty-deps.mc"
include "insert-implicit-recursion-var.mc"

include "mlang/include-handler.mc"
include "mlang/pprint.mc"
include "mlang/type-check.mc"
include "mlang/symbolize.mc"
include "mlang/const-transformer.mc"
include "mlang/language-composer.mc"
include "mlang/composition-check.mc"
include "mlang/postprocess.mc"
include "mlang/prune-unused-langs.mc"

include "mexpr/type-check.mc"
include "mexpr/phase-stats.mc"
include "mexpr/eval.mc"

lang BigPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint +
                      DeclCosemPrettyPrint + DeclCosynPrettyPrint
end

lang BigSym = ExtRecSym + MLangSymWihoutLang
end

lang BigTypeCheck = MExprTypeCheckMost + MExprTypeCheckLamLetVar +
                    ExtRecordTypeCheck
end

lang BigIncludeHandler = MLangIncludeHandler + BootParserMLang + ExtRecBootParser
end

lang BigPipeline = BigIncludeHandler +
                   BigSym +
                   BigPrettyPrint +
                   ExtRecCollectEnv +
                   BigTypeCheck +
                   PlaceholderAst +
                   ExtRecordTypeCheck +
                   MLangConstTransformer +
                   ExtRecMonomorphise +
                   MExprEval +
                   CosemTyAnnot +
                   LanguageComposer +
                   MLangCompositionCheck +
                   ExtRecCompiler +
                   ResolveQualifiedName +
                   ComputeMLangTyDeps +
                   PhaseStats +
                   PostProcess +
                   PruneUnusedLangs +
                   InsertImplictRecursionVar +
                   ExtrecConappSugar

  sem dumpKinds acc =
  -- | TyVar t -> cons (nameGetStr t.ident) acc
  | TyMetaVar t & ty ->
    switch deref t.contents
      case Unbound t then cons (nameGetStr t.ident, kind2str (t.kind)) acc
      case Link ty then dumpKinds acc ty
    end
  | other ->
    sfold_Type_Type dumpKinds acc other


  sem type2strWithKind =
  | ty ->
    let tyStr = type2str ty in

    let kinds = sfold_Type_Type dumpKinds [] ty in
    let kinds = map (lam p. join ["\t", p.0, " :: ", p.1]) kinds in

    if null kinds then
      tyStr
    else
      join [tyStr, " where\n", (strJoin "\n" kinds)]

  sem handleTypeOf =
  | TmApp {lhs = TmConst {val = CTypeOf _}, rhs = target} ->
    let ty = tyTm target in

    str_ (type2strWithKind (tyTm  target))
  | expr ->
    smap_Expr_Expr handleTypeOf expr

  -- For some reason, this is missing some function definitions, but
  -- I can not figure out why.
  sem dumpTypes : [String] -> Expr -> [String]
  sem dumpTypes acc =
  | TmLet t ->
    let acc = snoc acc (join [nameGetStr t.ident, " : ", type2str t.tyBody]) in
    let acc = sfold_Expr_Expr dumpTypes acc t.body in
    sfold_Expr_Expr dumpTypes acc t.inexpr
  | TmRecLets t ->
    let acc = foldl

      (lam acc. lam b. snoc acc (join [nameGetStr b.ident, " : ", type2str b.tyBody]))
      acc
      t.bindings in
    sfold_Expr_Expr dumpTypes acc t.inexpr
  | expr ->
    sfold_Expr_Expr dumpTypes acc expr

  sem dumpName =
  | name ->
    printLn (join [nameGetStr name, " ", int2string (sym2hash name.1)])

  -- It is currently not possible due to some issue with OCaml code gen
  -- To have an empty payload for a constructor. This work-around simply
  -- adds a '__dummy' field to empty constructor payloads.
  sem insertDummies =
  | p ->
    {p with decls = map (smap_Decl_Decl insertDummies_Decl) p.decls}

  sem insertDummies_Decl =
  | DeclSyn d ->
    let work = lam def.
      match def.tyIdent with TyRecord ty then
        if mapIsEmpty ty.fields then
          {def with tyIdent = TyRecord {ty with fields = mapSingleton cmpSID (stringToSid "__dummy") tyint_}}
        else
          def
      else
        def
    in
    DeclSyn {d with defs = map work d.defs}
  | other -> other

  sem collectSumTypes acc =
  | DeclSyn d ->
    setInsert d.ident acc
  | other ->
    sfold_Decl_Decl collectSumTypes acc other

  sem collectErecNames acc =
  | DeclSyn d ->
    let tyNames = map (lam def. def.tyName) d.defs in
    foldr setInsert acc tyNames
  | DeclCosyn d ->
    if d.isBase then
      setInsert d.ident acc
    else
      acc
  | other ->
    sfold_Decl_Decl collectErecNames acc other

  sem dumpTyVars_Expr =
  | expr ->
    smap_Expr_Type dumpTyVars_Type expr ;
    smap_Expr_Expr dumpTyVars_Expr expr ;
    expr

  sem dumpTyVars_Type =
  | TyAll t & ty ->
    dumpName t.ident ;
    dumpTyVars_Type t.ty ;
    ty
  | TyVar t & ty ->
    dumpName t.ident ;
    ty
  | ty ->
    smap_Type_Type dumpTyVars_Type ty

  sem stripTypes =
  | e ->
    let e = smap_Expr_Type (lam. tyunknown_) e in
    smap_Expr_Expr stripTypes e

  sem compileExtendedMLangToOcaml options runner =| filepath ->
    let log = mkPhaseLogState options.debugPhases in

    let p = parseAndHandleIncludes filepath in
    endPhaseStatsProg log "parsing-include-handling" p;

    let p = constTransformProgram builtin p in
    endPhaseStatsProg log "const-transformation" p;

    let p = insertDummies p in
    endPhaseStatsProg log "insert-dummies" p;

    let p = composeProgram p in
    endPhaseStatsProg log "language-inclusion-generation" p;

    let usedLangs = collectUsedLangs_Prog p in
    endPhaseStatsProg log "collect-used-langs" p;

    let p = insertImplicitParams p in
    endPhaseStatsProg log "insert-implicit-recursion-var" p;

    match symbolizeMLang symEnvDefault p with (_, p) in
    endPhaseStatsProg log "symbolization" p;

    let p = handleConappSugar p in
    endPhaseStatsProg log "handle-conapp-sugar" p;

    let checkOptions = {defaultCompositionCheckOptions with
      disableStrictSumExtension = options.disableStrictSumExtension} in

    match result.consume (checkCompositionWithOptions checkOptions p) with (_, res) in
    endPhaseStatsProg log "composition-check" p;

    -- let p = if options.keepDeadCode then p
    --         else pruneProgram usedLangs p in
    -- endPhaseStatsProg log "prune-unused-langs" p;

    switch res
      case Left errs then
        iter raiseError errs ;
        never
      case Right env then
        let p = handleCosemTyAnnot env.baseMap2 p in
        endPhaseStatsProg log "cosem-tyannot" p;
        -- printLn (mlang2str p);

        let ctx = _emptyCompilationContext env in

        let mlangTyDeps = getProgTyDeps env.baseMap2 p in
        endPhaseStatsProg log "mlang-dependency-analysis" p;

        let p = resolveQualifiedNameProgram mlangTyDeps env.baseMap2 p in
        endPhaseStatsProg log "resolve-qualified-name" p;

        let compilationCtx = _emptyCompilationContext env in
        let compilationCtx = {compilationCtx with baseMap = env.baseMap2} in

        let res = result.consume (compile compilationCtx p) in

        match res with (_, Right expr) in

        endPhaseStatsExpr log "mlang-to-mexpr-compilation" expr;

        (if options.debugGenerate then
          printLn " === MLang -> MExpr Result : ===" ;
          printLn (expr2str expr)
        else
          ());


        let accEnv = collectEnv _emptyAccEnv expr in
        let defs = accEnv.defs in

        let depGraph = createDependencyGraph defs in

        let tyDeps = computeTyDeps depGraph in

        let labelTyDeps = computeLabelTyDeps tyDeps defs in
        endPhaseStatsExpr log "dependency-analysis" expr ;

        let sumTypeNames = foldl collectSumTypes (setEmpty nameCmp) p.decls in
        let payloadNames = foldl collectErecNames (setEmpty nameCmp) p.decls in
        let tcEnv = {typcheckEnvDefault with
          disableConstructorTypes = false,
          extRecordType = {defs = defs,
                           tyDeps = tyDeps,
                           labelTyDeps = labelTyDeps,
                           sumTypeNames = sumTypeNames,
                           payloadNames = payloadNames}} in

        let expr = typeCheckExpr tcEnv expr in
        endPhaseStatsExpr log "extrec-type-check" expr;

        let expr = handleTypeOf expr in
        endPhaseStatsExpr log "handle-typeof" expr;

        let expr = monomorphiseExpr tcEnv.extRecordType expr in
        let expr = removeExtRecTypes_Expr tcEnv.extRecordType expr in
        endPhaseStatsExpr log "monomorphise" expr;


        -- TODO: replace this by its own dedicated debug flag
        (if options.debugParse then
          printLn " === Monomorphised result: ===" ;
          printLn (expr2str expr)
        else
          ());

        let expr = postprocess env.semSymMap expr in
        endPhaseStatsExpr log "postprocess" expr;

        runner options filepath expr;
        ()
    end
  sem doIt =| filepath ->
    let p = parseAndHandleIncludes filepath in

    let p = constTransformProgram builtin p in

    let p = composeProgram p in

    let usedLangs = collectUsedLangs_Prog p in

    let p = insertImplicitParams p in

    match symbolizeMLang symEnvDefault p with (_, p) in

    let p = handleConappSugar p in

    let res = result.consume (checkCompositionWithOptions defaultCompositionCheckOptions p) in
    let compositionCheckEnv =
      switch res
        case (_, Right compositionCheckEnv) then compositionCheckEnv
        case (_, Left errs) then iter raiseError errs; never
      end
    in

    let p = handleCosemTyAnnot compositionCheckEnv.baseMap2 p in
    printLn "=== Cosyn Ty Annot ===";
    printLn (mlang2str p);


    let mlangTyDeps = getProgTyDeps compositionCheckEnv.baseMap2 p in
    -- printLn (dumpTyDeps mlangTyDeps) ;

    let p = resolveQualifiedNameProgram mlangTyDeps compositionCheckEnv.baseMap2 p in
    -- let langEnvs = gatherLangEnvs mlangTyDeps p compositionCheckEnv.baseMap2 in

    -- printLn (mlang2str p);

    let compilationCtx = _emptyCompilationContext compositionCheckEnv in
    let compilationCtx = {compilationCtx with baseMap = compositionCheckEnv.baseMap2} in
    let res = result.consume (compile compilationCtx p) in

    match res with (_, Right expr) in

    -- printLn " === POST COMPILATION === ";
    -- printLn (expr2str expr);
    -- dumpTyVars_Expr expr;

    let accEnv = collectEnv _emptyAccEnv expr in
    let defs = accEnv.defs in

    let depGraph = createDependencyGraph defs in
    -- printLn (dumpDependencyGraph depGraph) ;

    let tyDeps = computeTyDeps depGraph in
    -- printLn (dumpTyDeps tyDeps) ;

    let labelTyDeps = computeLabelTyDeps tyDeps defs in

    let sumTypeNames = foldl collectSumTypes (setEmpty nameCmp) p.decls in
    let payloadNames = foldl collectErecNames (setEmpty nameCmp) p.decls in
    let tcEnv = {typcheckEnvDefault with
      disableConstructorTypes = false,
      extRecordType = {defs = defs,
                       tyDeps = tyDeps,
                       labelTyDeps = labelTyDeps,
                       sumTypeNames = sumTypeNames,
                       payloadNames = payloadNames}} in

    let expr = typeCheckExpr tcEnv expr in

    let expr = handleTypeOf expr in


    -- printLn (strJoin "\n" (dumpTypes [] expr));
    -- printLn (expr2str expr);

    let expr = monomorphiseExpr tcEnv.extRecordType expr in
    let expr = removeExtRecTypes_Expr tcEnv.extRecordType expr in

    -- printLn " === POST MONOMORPHISATION === ";
    -- printLn (expr2str expr);
    expr

  sem runIt =| filepath ->
    let expr = doIt filepath in
    let result = eval (evalCtxEmpty ()) expr in
    printLn (expr2str result);
    result

  sem pprintEnv =
  | env ->
    let pprintLabelMap = lam m.
      let seq = mapToSeq m in
      let seqStr = map (lam p. join [
        p.0,
        ": ",
        (type2str p.1)
      ]) seq in
      strJoin ", " seqStr
    in

    let pprintUpper = lam p.
      join [
        nameGetStr p.0,
        " :: {",
        pprintLabelMap p.1,
        "}"
      ]
    in

    strJoin "\n" (map pprintUpper (mapToSeq env))
end

mexpr
use BigPipeline in

if eqi (length argv) 2 then
  let expr = runIt (last argv) in
  printLn (expr2str expr)
else
  printLn "Usage: mlang <file>"