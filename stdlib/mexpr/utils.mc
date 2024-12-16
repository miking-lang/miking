-- Simple utility functions defined on MExpr ASTs.

include "map.mc"
include "string.mc"
include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"

lang MExprSubstitute = MExprAst
  -- Applies the substitutions of the provided map to the identifiers of the
  -- given AST.
  sem substituteIdentifiers : Map Name Name -> Expr -> Expr
  sem substituteIdentifiers replacements =
  | ast -> substituteIdentifiersExpr replacements ast

  sem subIdent : Map Name Name -> Name -> Name
  sem subIdent replacements =
  | id -> optionGetOrElse (lam. id) (mapLookup id replacements)

  sem substituteIdentifiersExpr : Map Name Name -> Expr -> Expr
  sem substituteIdentifiersExpr replacements =
  | TmVar t -> TmVar {t with ident = subIdent replacements t.ident}
  | TmConApp t ->
    TmConApp {t with ident = subIdent replacements t.ident,
                     body = substituteIdentifiersExpr replacements t.body,
                     ty = substituteIdentifiersType replacements t.ty}
  | TmLet t ->
    TmLet {t with ident = subIdent replacements t.ident,
                  tyAnnot = substituteIdentifiersType replacements t.tyAnnot,
                  tyBody = substituteIdentifiersType replacements t.tyBody,
                  body = substituteIdentifiersExpr replacements t.body,
                  inexpr = substituteIdentifiersExpr replacements t.inexpr,
                  ty = substituteIdentifiersType replacements t.ty}
  | TmLam t ->
    TmLam {t with ident = subIdent replacements t.ident,
                  tyAnnot = substituteIdentifiersType replacements t.tyAnnot,
                  tyParam = substituteIdentifiersType replacements t.tyParam,
                  body = substituteIdentifiersExpr replacements t.body,
                  ty = substituteIdentifiersType replacements t.ty}
  | TmType t ->
    TmType {t with ident = subIdent replacements t.ident,
                   tyIdent = substituteIdentifiersType replacements t.tyIdent,
                   inexpr = substituteIdentifiersExpr replacements t.inexpr,
                   ty = substituteIdentifiersType replacements t.ty}
  | TmConDef t ->
    TmConDef {t with ident = subIdent replacements t.ident,
                     tyIdent = substituteIdentifiersType replacements t.tyIdent,
                     inexpr = substituteIdentifiersExpr replacements t.inexpr,
                     ty = substituteIdentifiersType replacements t.ty}
  | TmExt t ->
    TmExt {t with ident = subIdent replacements t.ident,
                  tyIdent = substituteIdentifiersType replacements t.tyIdent,
                  inexpr = substituteIdentifiersExpr replacements t.inexpr,
                  ty = substituteIdentifiersType replacements t.ty}
  | TmRecLets t ->
    let subBinding = lam bind.
      {bind with ident = subIdent replacements bind.ident,
                 body = substituteIdentifiersExpr replacements bind.body,
                 tyAnnot = substituteIdentifiersType replacements bind.tyAnnot,
                 tyBody = substituteIdentifiersType replacements bind.tyBody}
    in
    TmRecLets {t with bindings = map subBinding t.bindings,
                      inexpr = substituteIdentifiersExpr replacements t.inexpr,
                      ty = substituteIdentifiersType replacements t.ty}
  | ast ->
    let ast = smap_Expr_Expr (substituteIdentifiersExpr replacements) ast in
    let ast = smap_Expr_Type (substituteIdentifiersType replacements) ast in
    let ast = smap_Expr_TypeLabel (substituteIdentifiersType replacements) ast in
    let ast = smap_Expr_Pat (substituteIdentifiersPat replacements) ast in
    withType (substituteIdentifiersType replacements (tyTm ast)) ast

  sem substituteIdentifiersType : Map Name Name -> Type -> Type
  sem substituteIdentifiersType replacements =
  | TyCon t -> TyCon {t with ident = subIdent replacements t.ident}
  | TyVar t -> TyVar {t with ident = subIdent replacements t.ident}
  | TyAll t -> TyAll {t with ident = subIdent replacements t.ident, ty = substituteIdentifiersType replacements t.ty}
  | ty -> smap_Type_Type (substituteIdentifiersType replacements) ty

  sem substituteIdentifiersPat : Map Name Name -> Pat -> Pat
  sem substituteIdentifiersPat replacements =
  | PatCon t ->
    PatCon {t with ident = subIdent replacements t.ident,
                   subpat = substituteIdentifiersPat replacements t.subpat}
  | p ->
    let p = smap_Pat_Pat (substituteIdentifiersPat replacements) p in
    withTypePat (substituteIdentifiersType replacements (tyPat p)) p
end

lang MExprFindSym = MExprAst
  -- Finds the names corresponding to a provided sequence of strings in a given
  -- AST. If 'id' is the first bound name matching a provided string, then
  -- 'Some id' is the result corresponding to that input string. If no name is
  -- found for a provided string, 'None' is the corresponding result for that
  -- string.
  --
  -- The function assumes the provided sequence of strings are distinct.
  sem findNamesOfStrings : [String] -> Expr -> [Option Name]
  sem findNamesOfStrings strs =
  | t ->
    let result : Map Int Name =
      findNamesOfStringsExpr
        (mapFromSeq cmpString (mapi (lam i. lam x. (x, i)) strs))
        (mapEmpty subi) t in
    create (length strs) (lam i. mapLookup i result)

  sem findNamesOfStringsExn : [String] -> Expr -> [Name]
  sem findNamesOfStringsExn strs =
  | t ->
    let r = findNamesOfStrings strs t in
    map (lam n. match n with Some n then n else error (join ["Couldn't find name"])) r

  sem findName : String -> Expr -> Option Name
  sem findName str =
  | t ->
    match findNamesOfStrings [str] t with [Some id] then
      Some id
    else None ()

  sem findNamesOfStringsExpr : Map String Int -> Map Int Name -> Expr -> Map Int Name
  sem findNamesOfStringsExpr strs acc =
  | TmLet t ->
    let acc = checkIdentifier strs acc t.ident in
    let acc = findNamesOfStringsExpr strs acc t.body in
    findNamesOfStringsExpr strs acc t.inexpr
  | TmRecLets t ->
    let findNamesBinding = lam acc. lam binding.
      checkIdentifier strs acc binding.ident
    in
    let findNamesBindingBody = lam acc. lam binding.
      findNamesOfStringsExpr strs acc binding.body
    in
    let acc = foldl findNamesBinding acc t.bindings in
    let acc = foldl findNamesBindingBody acc t.bindings in
    findNamesOfStringsExpr strs acc t.inexpr
  | TmType {ident = ident, tyIdent = tyIdent, inexpr = inexpr}
  | TmConDef {ident = ident, tyIdent = tyIdent, inexpr = inexpr}
  | TmExt {ident = ident, tyIdent = tyIdent, inexpr = inexpr} ->
    let acc = checkIdentifier strs acc ident in
    let acc = findNamesOfStringsType strs acc tyIdent in
    findNamesOfStringsExpr strs acc inexpr
  | t -> sfold_Expr_Expr (findNamesOfStringsExpr strs) acc t

  sem findNamesOfStringsType : Map String Int -> Map Int Name -> Type -> Map Int Name
  sem findNamesOfStringsType strs acc =
  | TyCon {ident = ident} | TyVar {ident = ident} ->
    checkIdentifier strs acc ident
  | ty -> sfold_Type_Type (findNamesOfStringsType strs) acc ty

  sem checkIdentifier : Map String Int -> Map Int Name -> Name -> Map Int Name
  sem checkIdentifier strs acc =
  | id ->
    match mapLookup (nameGetStr id) strs with Some index then
      if mapMem index acc then acc
      else mapInsert index id acc
    else acc
end

lang TestLang =
  MExprFindSym + MExprSubstitute + BootParser + MExprSym + MExprPrettyPrint
end

mexpr

use TestLang in

let pp = lam e. mexprToString e in

let expr = lam id. bindall_ [
  ulet_ id (ulam_ id (var_ id)),
  ureclets_ [(id, var_ id)],
  type_ id [] (tyapp_ (tycon_ id) tyint_),
  condef_ id (tyarrow_ tyint_ (tycon_ id)),
  ext_ id false tyunknown_,
  conapp_ id (int_ 2)
] in
let replace = mapFromSeq nameCmp [(nameNoSym "x", nameNoSym "y")] in
utest pp (substituteIdentifiers replace (expr "x")) with pp (expr "y") using eqString in

let parseProgram : String -> Expr =
  lam str.
  let parseArgs = {defaultBootParserParseMExprStringArg with allowFree = true} in
  let ast = parseMExprStringExn parseArgs str in
  symbolizeAllowFree ast
in

let matchOpt : all a. all b. Option a -> Option b -> Bool =
  lam o1. lam o2.
  match (o1, o2) with (Some _, Some _) then true
  else match (o1, o2) with (None _, None _) then true
  else false
in
recursive let matchOpts : all a. all b. [Option a] -> [Option b] -> Bool =
  lam opts1. lam opts2.
  match (opts1, opts2) with ([o1] ++ opts1, [o2] ++ opts2) then
    and (matchOpt o1 o2) (matchOpts opts1 opts2)
  else match (opts1, opts2) with ([], []) then true
  else error "Inconsistent lengths of arguments"
in

let t = parseProgram "let foo = lam. 42 in ()" in
utest findNamesOfStrings ["foo"] t with [Some ()] using matchOpts in

let t = parseProgram "recursive let foo = lam. 42 in ()" in
utest findNamesOfStrings ["foo"] t with [Some ()] using matchOpts in

let t = parseProgram "external foo : () in ()" in
utest findNamesOfStrings ["foo"] t with [Some ()] using matchOpts in

-- NOTE(larshum, 2022-09-13): This program was constructed based on the current
-- shape of the utest runtime.
let s = "
type Option a in
con Some : all a. a -> Option a in
con None : all a. () -> Option a in

let numFailed = ref 0 in
let join = lam seqs.
  foldl concat [] seqs
in
let printLn = lam s.
  print (concat s \"\\n\")
in
recursive
  let strJoin = lam delim. lam strs.
    if eqi (length strs) 0
    then \"\"
    else if eqi (length strs) 1
         then head strs
         else concat (concat (head strs) delim) (strJoin delim (tail strs))
in
let utestTestPassed = lam.
  print \".\"
in
let utestRunner =
  lam info     : String.
  lam usingStr : String.
  lam lpprint  : Unknown -> String.
  lam rpprint  : Unknown -> String.
  lam eqfunc   : Unknown -> Unknown -> Bool.
  lam lhs      : Unknown.
  lam rhs      : Unknown.
  -- Comparison
  if eqfunc lhs rhs then
    utestTestPassed ()
  else
    utestTestFailed info (lpprint lhs) (rpprint rhs) usingStr
in
()" in
let prog = parseProgram s in

-- NOTE(larshum, 2022-09-13): We verify that the expected identifiers are found
-- in the program. However, we do not test the symbols themselves as we cannot
-- know these beforehand.
let strs = ["Option", "Error", "Some", "in", "utestRunner", "numFailed", "eqExpr"] in
let expected = [Some (), None (), Some (), None (), Some (), Some (), None ()] in
utest findNamesOfStrings strs prog with expected using matchOpts in

()
