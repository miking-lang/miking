
include "bool.mc"
include "name.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "./ast.mc"
include "./ast-builder.mc"

-- Language fragment string parser translation
let pprintLangString = lam str.
  _parserStr str "#lang" _isValidIdentContents


lang MLangIdentifierPrettyPrint = IdentifierPrettyPrint
  sem pprintLangName (env: PprintEnv) =
  | name ->
    match pprintEnvGetStr env name with (env,str) in
    let s = pprintLangString str in
    (env, s)
end


lang UsePrettyPrint = PrettyPrint + UseAst + MLangIdentifierPrettyPrint
  sem isAtomic =
  | TmUse _ -> false

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmUse t ->
    match pprintLangName env t.ident with (env,ident) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    (env, join ["use ", ident, pprintNewline indent,
                "in", pprintNewline indent,
                inexpr])
end

lang IncludePrettyPrint = PrettyPrint + IncludeAst
  sem isAtomic =
  | TmInclude _ -> false

  sem pprintIncludeCode (indent : Int) (env : PprintEnv) =
  | {path = path} -> (env, join ["include \"", escapeString path, "\""])

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmInclude t ->
    match pprintIncludeCode indent env {path = t.path} with (env, inclStr) in
    match pprintCode indent env t.inexpr with (env,inexpr) in
    (env, join [inclStr, pprintNewline indent,
                "in", pprintNewline indent,
                inexpr])
end


lang DeclPrettyPrint = PrettyPrint + MLangIdentifierPrettyPrint
  sem pprintDeclCode : Int -> PprintEnv -> Decl -> (PprintEnv, String)
  -- Intentionally left blank

  sem pprintDeclSequenceCode : Int -> PprintEnv -> [Decl] -> (PprintEnv, String)
  sem pprintDeclSequenceCode (indent : Int) (env : PprintEnv) =
  | decls ->
    let declFoldResult = foldl (lam acc. lam decl.
      match acc with (env, accDecls) in
      match pprintDeclCode indent env decl with (env, declString) in
      (env, snoc accDecls declString)
    ) (env, []) decls in
    match declFoldResult with (env, declStrings) in
    (env, strJoin (pprintNewline indent) declStrings)
end


lang LangDeclPrettyPrint = DeclPrettyPrint + LangDeclAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclLang t ->
    match pprintLangName env t.ident with (env, langNameStr) in
    match
      mapAccumL pprintLangName env t.includes
    with (env, inclStrs) in
    match pprintDeclSequenceCode (pprintIncr indent) env t.decls
    with (env, declSeqStr) in
    let inclEqStr =
      if eqi (length inclStrs) 0 then
        ""
      else
        let nl = pprintNewline (pprintIncr indent) in
        concat (concat " =" nl)
               (strJoin (concat nl "+ ") inclStrs)
    in
    let langContents =
      if eqString declSeqStr "" then ""
      else join [pprintNewline (pprintIncr indent), declSeqStr]
    in
    (env, join ["lang ", langNameStr, inclEqStr, langContents,
                pprintNewline indent, "end"])
end


lang SynDeclPrettyPrint = DeclPrettyPrint + SynDeclAst + DataPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclSyn t ->
    match pprintTypeName env t.ident with (env, typeNameStr) in
    match
      mapAccumL (lam env. lam syndef.
        match pprintConName env syndef.ident with (env, str) in
        match getTypeStringCode (pprintIncr indent) env syndef.tyIdent
        with (env, ty) in
        (env, join ["| ", str, " ", ty])
      ) env t.defs
    with (env, defStrings) in
    (env, strJoin (pprintNewline indent)
                  (cons (join ["syn ", typeNameStr, " ="]) defStrings))
end


lang SemDeclPrettyPrint = DeclPrettyPrint + SemDeclAst + UnknownTypeAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclSem t ->
    match pprintEnvGetStr env t.ident with (env, baseStr) in
    if and (null t.args) (null t.cases) then
      -- sem typedecl
      match getTypeStringCode indent env t.tyAnnot with (env, tyStr) in
      (env, join ["sem ", baseStr, " : ", tyStr])
    else
      -- sem impl
      match
        mapAccumL (lam env. lam arg.
          match pprintEnvGetStr env arg.ident with (env, baseStr) in
          match arg.tyAnnot with TyUnknown _ then
            (env, baseStr)
          else
            match getTypeStringCode indent env arg.tyAnnot with (env, tyStr) in
            (env, join ["(", baseStr, " : ", tyStr, ")"])
        ) env t.args
      with (env, argStrs) in
      match
        mapAccumL (lam env. lam semcase.
          match getPatStringCode (pprintIncr indent) env semcase.pat
          with (env, patStr) in
          match pprintCode (pprintIncr indent) env semcase.thn
          with (env, exprStr) in
          (env, join ["| ", patStr, " ->", pprintNewline (pprintIncr indent), exprStr])
        ) env t.cases
      with (arg, caseStrs) in
      (env, strJoin (pprintNewline indent) (
              cons (join ["sem ", baseStr, strJoin " " (cons "" argStrs), " ="])
                   caseStrs))
end

lang LetDeclPrettyPrint = DeclPrettyPrint + LetDeclAst + LetPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclLet t ->
    pprintLetAssignmentCode indent env {
      ident = t.ident,
      body = t.body,
      tyAnnot = t.tyAnnot
    }
end


lang TypeDeclPrettyPrint = DeclPrettyPrint + TypeDeclAst + TypePrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclType t ->
    pprintTypeCode indent env {
      ident = t.ident,
      params = t.params,
      tyIdent = t.tyIdent
    }
end


lang RecLetsDeclPrettyPrint = DeclPrettyPrint + RecLetsDeclAst + RecLetsPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclRecLets t ->
    match t.bindings with [] then
      (env, "let #var\"\" = ()")
    else
      match pprintRecLetsCode indent env t.bindings with (env, recletStr) in
      (env, join [recletStr, pprintNewline indent, "end"])
end


lang DataDeclPrettyPrint = DeclPrettyPrint + DataDeclAst + DataPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclConDef t ->
    pprintConDefCode indent env {ident = t.ident, tyIdent = t.tyIdent}
end


lang UtestDeclPrettyPrint = DeclPrettyPrint + UtestDeclAst + UtestPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclUtest t ->
    pprintUtestCode indent env {
      test = t.test, expected = t.expected, tusing = t.tusing}
end


lang ExtDeclPrettyPrint = DeclPrettyPrint + ExtDeclAst + ExtPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclExt t ->
    pprintExtCode indent env {
      ident = t.ident, tyIdent = t.tyIdent, effect = t.effect}
end


lang IncludeDeclPrettyPrint = DeclPrettyPrint + IncludeDeclAst + IncludePrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclInclude t -> pprintIncludeCode indent env {path = t.path}
end


lang MLangTopLevelPrettyPrint = DeclPrettyPrint + MLangTopLevel
  sem pprintMLangProgram (indent : Int) (env : PprintEnv) =
  | {decls = decls, expr = expr} ->
    match mapAccumL (pprintDeclCode indent) env decls with (env, declStrs) in
    match pprintCode indent env expr with (env, exprStr) in
    (env, strJoin (pprintNewline indent) (concat declStrs ["mexpr", exprStr]))
end


lang MLangPrettyPrint = MExprPrettyPrint +

  -- Extended expressions
  UsePrettyPrint + IncludePrettyPrint +

  -- Declarations
  DeclPrettyPrint + LangDeclPrettyPrint + SynDeclPrettyPrint +
  SemDeclPrettyPrint + LetDeclPrettyPrint + TypeDeclPrettyPrint +
  RecLetsDeclPrettyPrint + DataDeclPrettyPrint + UtestDeclPrettyPrint +
  ExtDeclPrettyPrint + IncludeDeclPrettyPrint +

  -- Top-level pretty printer
  MLangTopLevelPrettyPrint
end


mexpr


use MLangPrettyPrint in

let prog: MLangProgram = {
  decls = [
    DeclInclude {path = "common.mc", info = NoInfo {}},
    DeclInclude {path = "string.mc", info = NoInfo {}},
    decl_langi_ "Test1" [] [],
    decl_langi_ "Test2" ["Test1"] [],
    decl_langi_ "Test3" ["Test1", "Test2"] [],
    decl_lang_ "Foo" [
      decl_syn_ "Bar" [
        ("Apple", tyint_),
        ("Pear", tyseq_ tyfloat_)
      ],
      decl_usem_ "getFruit" ["x"] [
        (pcon_ "Apple" (pvar_ "i"), appf1_ (var_ "int2string") (var_ "i")),
        (pcon_ "Pear" (pvar_ "fs"),
         appf2_ (var_ "strJoin")
                (var_ "x")
                (appf2_ (var_ "map") (var_ "float2string") (var_ "fs")))
      ]
    ],
    DeclLet {ident = nameNoSym "foo",
             tyAnnot = tyunknown_, tyBody = tyunknown_,
             body = ulams_ ["x", "y"] (
               concat_ (appf1_ (var_ "int2string") (var_ "x"))
                       (appf1_ (var_ "float2string") (var_ "y"))
             ),
             info = NoInfo {}}
  ],
  expr = appf1_ (var_ "printLn")
                (appf2_ (var_ "foo") (int_ 10) (float_ 0.5))
} in

match pprintMLangProgram 0 pprintEnvEmpty prog with (_, progStr) in
print progStr;
print "\n"
