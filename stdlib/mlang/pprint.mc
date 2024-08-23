-- Pretty Printing for MLang programs.

include "bool.mc"
include "name.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "ast.mc"
include "ast-builder.mc"

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

lang TyUsePrettyPrint = MExprPrettyPrint + TyUseAst + MLangIdentifierPrettyPrint
  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | TyUse t -> 
    match pprintLangName env t.ident with (env, ident) in
    match getTypeStringCode indent env t.inty with (env, inty) in
    (env, join ["use ", ident, pprintNewline indent,
                "in", pprintNewline indent,
                inty])
end


lang DeclPrettyPrint = PrettyPrint + MLangIdentifierPrettyPrint + DeclAst
  sem pprintDeclCode : Int -> PprintEnv -> Decl -> (PprintEnv, String)
  sem pprintDeclCode indent env =
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
    match mapAccumL pprintEnvGetStr env t.params with (env, params) in
    let params = join (map (concat " ") params) in
    match
      mapAccumL (lam env. lam syndef.
        match pprintConName env syndef.ident with (env, str) in
        match getTypeStringCode (pprintIncr indent) env syndef.tyIdent
        with (env, ty) in
        (env, join ["| ", str, " ", ty])
      ) env t.defs
    with (env, defStrings) in
    (env, strJoin (pprintNewline indent)
                  (cons (join ["syn ", typeNameStr, params, " ="]) defStrings))
end

lang SemDeclPrettyPrint = DeclPrettyPrint + SemDeclAst + UnknownTypeAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclSem t ->
    match pprintEnvGetStr env t.ident with (env, baseStr) in
    match
      match t.tyAnnot with !TyUnknown _ then
        -- sem typedecl
        match getTypeStringCode indent env t.tyAnnot with (env, tyStr) in
        (env, Some (join ["sem ", baseStr, " : ", tyStr]))
      else (env, None ())
    with (env, mDecl) in
    match
      match (t.args, t.cases) with !(None _, []) then
        -- sem impl
        match
          match t.args with Some args in 
          mapAccumL (lam env. lam arg.
            match pprintEnvGetStr env arg.ident with (env, baseStr) in
            match arg.tyAnnot with TyUnknown _ then
              (env, baseStr)
            else
              match getTypeStringCode indent env arg.tyAnnot with (env, tyStr) in
              (env, join ["(", baseStr, " : ", tyStr, ")"])
          ) env args
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
        let final = strJoin (pprintNewline indent) (
                cons (join ["sem ", baseStr, strJoin " " (cons "" argStrs), " ="])
                     caseStrs) in
        (env, Some final)
      else (env, None ())
    with (env, mImpl) in
    (env, strJoin "\n" (mapOption identity [mDecl, mImpl]))
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


lang IncludeDeclPrettyPrint = DeclPrettyPrint + IncludeDeclAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | DeclInclude t -> (env, join ["include \"", escapeString t.path, "\""])
end


lang MLangTopLevelPrettyPrint = DeclPrettyPrint + MLangTopLevel
  sem mlang2str : MLangProgram -> String
  sem mlang2str =
  | prog -> match pprintMLangProgram 0 pprintEnvEmpty prog with (_, s) in s

  sem pprintMLangProgram (indent : Int) (env : PprintEnv) =
  | {decls = decls, expr = expr} ->
    match mapAccumL (pprintDeclCode indent) env decls with (env, declStrs) in
    match pprintCode indent env expr with (env, exprStr) in
    (env, strJoin (pprintNewline indent) (concat declStrs ["mexpr", exprStr]))
end


lang MLangPrettyPrint = MExprPrettyPrint +

  -- Extended expressions and types
  UsePrettyPrint + TyUsePrettyPrint + 

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
    decl_include_ "common.mc",
    decl_include_ "string.mc",
    decl_langi_ "Test1" [] [],
    decl_langi_ "test2" ["Test1"] [],
    decl_langi_ "The 3rd Test" ["Test1", "test2"] [],
    decl_ext_ "my_external" false (tyarrow_ tyfloat_ tystr_),
    decl_ext_ "my_external2" true (tyarrow_ tyint_ tystr_),
    decl_lang_ "Foo" [
      decl_syn_ "Bar" [
        ("Apple", tyint_),
        ("Pear", tyseq_ tyfloat_)
      ],
      decl_usem_ "getFruit" ["x"] [
        (pcon_ "Apple" (pvar_ "i"), appf1_ (var_ "int2string") (var_ "i")),
        (pcon_ "Pear" (pvar_ "fs"),
         bindall_ [
           ulet_ "strJoin" (unit_),
           appf2_ (var_ "strJoin")
                  (var_ "x")
                  (appf2_ (var_ "map") (var_ "float2string") (var_ "fs"))
         ])
      ]
    ],
    decl_type_ "MyType" ["x"] tyunknown_,
    decl_condef_ "MyCon" (tyall_ "x" (tyarrows_ [tyseq_ (tyvar_ "x"), tyapp_ (tycon_ "MyType") (tyvar_ "x")])),
    decl_ureclets_ [
      ("rec_foo", ulams_ ["x"] (appf1_ (var_ "printLn") (var_ "x"))),
      ("rec_bar", ulams_ ["y"] (appf2_ (var_ "concat") (var_ "y") (var_ "y")))
    ],
    decl_ureclets_ [
      ("rec_babar", ulams_ ["z"] (seq_ [var_ "z"]))
    ],
    decl_ureclets_ [],
    decl_utest_ (appf1_ (var_ "rec_babar") (int_ 5)) (seq_ [int_ 5]),
    decl_ulet_ "foo" (
      ulams_ ["x", "y"] (bindall_ [
        use_ "Foo",
        concat_ (appf1_ (var_ "getFruit")
                        (conapp_ "Apple" (var_ "x")))
                (appf1_ (var_ "float2string") (var_ "y"))
      ])
    )
  ],
  expr = appf1_ (var_ "printLn")
                (appf2_ (var_ "foo") (int_ 10) (float_ 0.5))
} in

--print (mlang2str prog); print "\n";
utest length (mlang2str prog) with 0 using geqi in

let prog2: MLangProgram = {
  decls = [
    decl_include_ "common.mc",
    decl_include_ "string.mc",
    decl_langi_ "Test1" [] [],
    decl_langi_ "test2" ["Test1"] [],
    decl_langi_ "The 3rd Test" ["Test1", "test2"] [],
    decl_ext_ "my_external" false (tyarrow_ tyfloat_ tystr_),
    decl_ext_ "my_external2" true (tyarrow_ tyint_ tystr_),
    decl_lang_ "Foo" [
      decl_syn_ "Bar" [
        ("Apple", tyint_),
        ("Pear", tyseq_ tyfloat_)
      ],
      decl_usem_ "getFruit" ["x"] [
        (pcon_ "Apple" (pvar_ "i"), appf1_ (var_ "int2string") (var_ "i")),
        (pcon_ "Pear" (pvar_ "fs"),
         bindall_ [
           ulet_ "strJoin" (unit_),
           appf2_ (var_ "strJoin")
                  (var_ "x")
                  (appf2_ (var_ "map") (var_ "float2string") (var_ "fs"))
         ])
      ]
    ],
    decl_type_ "MyType" ["x"] tyunknown_,
    decl_condef_ "MyCon" (tyall_ "x" (tyarrows_ [tyseq_ (tyvar_ "x"), tyapp_ (tycon_ "MyType") (tyvar_ "x")])),
    decl_ureclets_ [
      ("rec_foo", ulams_ ["x"] (appf1_ (var_ "printLn") (var_ "x"))),
      ("rec_bar", ulams_ ["y"] (appf2_ (var_ "concat") (var_ "y") (var_ "y")))
    ],
    decl_ureclets_ [
      ("rec_babar", ulams_ ["z"] (seq_ [var_ "z"]))
    ],
    decl_ureclets_ [],
    decl_utest_ (appf1_ (var_ "rec_babar") (int_ 5)) (seq_ [int_ 5]),
    decl_ulet_ "foo" (
      ulams_ ["x", "y"] (bindall_ [
        use_ "Foo",
        concat_ (appf1_ (var_ "getFruit")
                        (conapp_ "Apple" (var_ "x")))
                (appf1_ (var_ "float2string") (var_ "y"))
      ])
    )
  ],
  expr = appf1_ (var_ "printLn")
                (appf2_ (var_ "foo") (int_ 10) (float_ 0.5))
} in

--print (mlang2str prog2); print "\n";

()
