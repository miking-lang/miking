-- Pretty Printing for MLang programs.

include "bool.mc"
include "name.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
include "mexpr/pprint.mc"
include "ast.mc"
include "ast-builder.mc"
include "seq.mc"
include "string.mc"
include "mexpr/ast.mc"
include "basic-types.mc"
include "common.mc"

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


lang UsePrettyPrint = PrettyPrint + UseDeclAst + MLangIdentifierPrettyPrint
  sem pprintDeclCode (indent : Int) (env: PprintEnv) +=
  | DeclUse t ->
    match pprintLangName env t.ident with (env,ident) in
    (env, join ["use ", ident])
end

lang TyUsePrettyPrint = MExprPrettyPrint + TyUseAst + MLangIdentifierPrettyPrint
  sem getTypeStringCode (indent : Int) (env : PprintEnv) +=
  | TyUse t ->
    match pprintLangName env t.ident with (env, ident) in
    match getTypeStringCode indent env t.inty with (env, inty) in
    (env, join ["use ", ident, pprintNewline indent,
                "in", pprintNewline indent,
                inty])
end

lang LangDeclPrettyPrint = PrettyPrint + LangDeclAst + MLangIdentifierPrettyPrint
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

  sem pprintDeclCode (indent : Int) (env : PprintEnv) +=
  | DeclLang t ->
    match pprintLangName env t.ident with (env, langNameStr) in
    match
      mapAccumL (lam acc. lam x. pprintLangName acc x.0) env t.includes
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


lang SynDeclPrettyPrint = PrettyPrint + SynDeclAst + DataPrettyPrint
  sem pprintDeclCode (indent : Int) (env : PprintEnv) +=
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

    let eqSym = switch t.kind
      case SynBase _ then " ="
      case SynSum _ then " +="
    end in

    (env, strJoin (pprintNewline indent)
                  (cons (join ["syn ", typeNameStr, params, eqSym]) defStrings))
end

lang SemDeclPrettyPrint = PrettyPrint + SemDeclAst + UnknownTypeAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) +=
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
      match t.impl with Some impl then
        -- sem impl
        match
          mapAccumL (lam env. lam param.
            match pprintEnvGetStr env param.ident with (env, baseStr) in
            match param.tyAnnot with TyUnknown _ then
              (env, baseStr)
            else
              match getTypeStringCode indent env param.tyAnnot with (env, tyStr) in
              (env, join ["(", baseStr, " : ", tyStr, ")"])
          ) env impl.params
        with (env, paramStrs) in
        match
          mapAccumL (lam env. lam semcase.
            match getPatStringCode (pprintIncr indent) env semcase.pat
            with (env, patStr) in
            match pprintCode (pprintIncr indent) env semcase.body
            with (env, exprStr) in
            (env, join ["| ", patStr, " ->", pprintNewline (pprintIncr indent), exprStr])
          ) env impl.cases
        with (param, caseStrs) in

        let eqSym = switch t.kind
          case SemBase _ then " ="
          case SemSum _ then " +="
          case _ then "?"
        end in

        let final = strJoin (pprintNewline indent) (
                cons (join ["sem ", baseStr, strJoin " " (cons "" paramStrs), eqSym])
                     caseStrs) in
        (env, Some final)
      else (env, None ())
    with (env, mImpl) in
    (env, strJoin "\n" (mapOption identity [mDecl, mImpl]))
end


lang IncludeDeclPrettyPrint = PrettyPrint + IncludeDeclAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) +=
  | DeclInclude t -> (env, join ["include \"", escapeString t.path, "\""])
end


lang MLangTopLevelPrettyPrint = PrettyPrint + MLangTopLevel
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
  UsePrettyPrint + TyUsePrettyPrint + -- QualifiedNamePrettyPrint +

  -- Declarations
  LangDeclPrettyPrint + SynDeclPrettyPrint + SemDeclPrettyPrint +
  IncludeDeclPrettyPrint +


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
    ext_ "my_external" false (tyarrow_ tyfloat_ tystr_),
    ext_ "my_external2" true (tyarrow_ tyint_ tystr_),
    decl_lang_ "Foo" [
      decl_syn_ "Bar" [
        ("Apple", tyint_),
        ("Pear", tyseq_ tyfloat_)
      ],
      decl_usem_ "getFruit" ["x"] [
        (pcon_ "Apple" (pvar_ "i"), appf1_ (var_ "int2string") (var_ "i")),
        (pcon_ "Pear" (pvar_ "fs"),
         bind_
           (ulet_ "strJoin" (unit_))
           (appf2_ (var_ "strJoin")
                  (var_ "x")
                  (appf2_ (var_ "map") (var_ "float2string") (var_ "fs")))
         )
      ]
    ],
    type_ "MyType" ["x"] tyunknown_,
    condef_ "MyCon" (tyall_ "x" (tyarrows_ [tyseq_ (tyvar_ "x"), tyapp_ (tycon_ "MyType") (tyvar_ "x")])),
    ureclets_ [
      ("rec_foo", ulams_ ["x"] (appf1_ (var_ "printLn") (var_ "x"))),
      ("rec_bar", ulams_ ["y"] (appf2_ (var_ "concat") (var_ "y") (var_ "y")))
    ],
    ureclets_ [
      ("rec_babar", ulams_ ["z"] (seq_ [var_ "z"]))
    ],
    ureclets_ [],
    utest_ (appf1_ (var_ "rec_babar") (int_ 5)) (seq_ [int_ 5]),
    ulet_ "foo" (
      ulams_ ["x", "y"] (bind_
        (use_ "Foo")
        (concat_ (appf1_ (var_ "getFruit")
                        (conapp_ "Apple" (var_ "x")))
                (appf1_ (var_ "float2string") (var_ "y")))
      )
    )
  ],
  expr = appf1_ (var_ "printLn")
                (appf2_ (var_ "foo") (int_ 10) (float_ 0.5))
} in

print (mlang2str prog); print "\n";
utest length (mlang2str prog) with 0 using geqi in

let prog2: MLangProgram = {
  decls = [
    decl_include_ "common.mc",
    decl_include_ "string.mc",
    decl_langi_ "Test1" [] [],
    decl_langi_ "test2" ["Test1"] [],
    decl_langi_ "The 3rd Test" ["Test1", "test2"] [],
    ext_ "my_external" false (tyarrow_ tyfloat_ tystr_),
    ext_ "my_external2" true (tyarrow_ tyint_ tystr_),
    decl_lang_ "Foo" [
      decl_syn_ "Bar" [
        ("Apple", tyint_),
        ("Pear", tyseq_ tyfloat_)
      ],
      decl_usem_ "getFruit" ["x"] [
        (pcon_ "Apple" (pvar_ "i"), appf1_ (var_ "int2string") (var_ "i")),
        (pcon_ "Pear" (pvar_ "fs"),
         bind_
           (ulet_ "strJoin" unit_)
           (appf2_ (var_ "strJoin")
                  (var_ "x")
                  (appf2_ (var_ "map") (var_ "float2string") (var_ "fs")))
         )
      ]
    ],
    type_ "MyType" ["x"] tyunknown_,
    condef_ "MyCon" (tyall_ "x" (tyarrows_ [tyseq_ (tyvar_ "x"), tyapp_ (tycon_ "MyType") (tyvar_ "x")])),
    ureclets_ [
      ("rec_foo", ulams_ ["x"] (appf1_ (var_ "printLn") (var_ "x"))),
      ("rec_bar", ulams_ ["y"] (appf2_ (var_ "concat") (var_ "y") (var_ "y")))
    ],
    ureclets_ [
      ("rec_babar", ulams_ ["z"] (seq_ [var_ "z"]))
    ],
    ureclets_ [],
    utest_ (appf1_ (var_ "rec_babar") (int_ 5)) (seq_ [int_ 5]),
    ulet_ "foo" (
      ulams_ ["x", "y"] (bind_
        (use_ "Foo")
        (concat_ (appf1_ (var_ "getFruit")
                        (conapp_ "Apple" (var_ "x")))
                (appf1_ (var_ "float2string") (var_ "y")))
      )
    )
  ],
  expr = appf1_ (var_ "printLn")
                (appf2_ (var_ "foo") (int_ 10) (float_ 0.5))
} in

print (mlang2str prog2); print "\n\n";

()
