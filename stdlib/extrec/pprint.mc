include "mexpr/pprint.mc"
include "mexpr/ast.mc"

include "mlang/pprint.mc"

include "ast.mc"
include "ast-builder.mc"

lang ExtRecTermPrettyPrint = TypePrettyPrint + PrettyPrint + ExtRecordAst
  sem isAtomic =
  | TmRecField _ | TmRecType _ -> false
  | TmExtRecord  _ -> true
  | TmExtExtend _ | TmExtExtend _ -> false


  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecType t ->
    match pprintTypeName env t.ident with (env, name) in
    match pprintCode indent env t.inexpr with (env, inexpr) in
    match mapAccumL pprintEnvGetStr env t.params with (env, paramsStr) in
    (env, join [
      "rectype ",
      name,
      " ",
      strJoin " " paramsStr,
      " in", pprintNewline indent,
      inexpr])
  | TmRecField t ->
    let ty =  typeToString env t.tyIdent in
    match pprintCode indent env t.inexpr with (env, inexpr) in
    (env, join [
      "recfield ",
      t.label,
      " : ",
      ty,
      " in ",
      pprintNewline indent,
      inexpr
    ])
  | TmExtRecord {bindings = bindings, ident = ident} ->
    let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [k, " = ", str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin ", " binds
      in
      (env,join ["{", nameGetStr ident, " of ", merged, "}"])
  | TmExtExtend {bindings = bindings, e = e} ->
    match pprintCode indent env e with (env, eStr) in
    let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [k, " = ", str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin ", " binds
      in
      (env, join [
        "{extend ",
        eStr,
        " with ",
        merged,
        "}"
      ])
end

lang DeclCosynPrettyPrint = DeclPrettyPrint + CosynDeclAst
  sem pprintDeclCode indent env =
  | DeclCosyn t ->
    match pprintTypeName env t.ident with (env, typeNameStr) in
    match mapAccumL pprintEnvGetStr env t.params with (env, params) in
    let params = join (map (concat " ") params) in

    match getTypeStringCode indent env t.ty with (env, typeStr) in
    let eqSym = if t.isBase then " = " else " *= " in

    (env, join ["cosyn ", typeNameStr, params, eqSym, typeStr])
end

lang CopatPrettyPrint = CopatAst
  sem getCopatStringCode indent env =
end

lang RecordCopatPrettyPrint = RecordCopatAst + CopatPrettyPrint + MExprIdentifierPrettyPrint
  sem getCopatStringCode indent env =
  | RecordCopat c ->
    (env, join ["{ ", strJoin ", " c.fields, " }"])
end

lang DeclCosemPrettyPrint = DeclPrettyPrint + CosemDeclAst + RecordCopatPrettyPrint
  sem pprintDeclCode indent env =
  | DeclCosem t ->
    match pprintVarName env t.ident with (env, ident) in

    let pair = match t.tyAnnot with !TyUnknown _ then
      match getTypeStringCode indent env t.tyAnnot with (env, tyStr) in
      (env, Some (join ["cosem ", ident, " : ", tyStr]))
    else
      (env, None ()) in

    match pair with (env, typeAnnotStr) in

    let eqSym = if t.isBase then " = " else " *= " in

    let pprintCase = lam env. lam cs.
      match cs with (copat, tm) in
      match getCopatStringCode indent env copat with (env, copat) in
      match pprintCode (pprintIncr indent) env tm with (env, tm) in
      (env, join [pprintSpacing indent, "| ", copat, " <- ", "\n",
                  pprintSpacing (pprintIncr indent), tm]) in
    match mapAccumL pprintCase env t.cases with (env, str) in
    let str = strJoin "\n" str in

    let bodyStr = join ["cosem ", ident, eqSym, "\n", str] in

    match typeAnnotStr with Some typeAnnotStr then
      (env, join [typeAnnotStr, pprintNewline indent, bodyStr])
    else
      (env, bodyStr)
end

lang TypeAbsPrettyPrint = PrettyPrint + TypeAbsAst
  sem getTypeStringCode indent env =
  | TyAbs t ->
    match pprintVarName env t.ident with (env, ident) in
    match getTypeStringCode indent env t.body with (env, body) in
    (env, join ["Lam ", ident, ". ", body])
end

lang TypeAbsAppAst = PrettyPrint + TypeAbsAppAst
  sem getTypeStringCode indent env =
  | TyAbsApp t ->
    match getTypeStringCode indent env t.lhs with (env, lhs) in
    match getTypeStringCode indent env t.rhs with (env, rhs) in
    (env, join [lhs, " @ ", rhs])
end

lang PatExtRecordPrettyPrint = PrettyPrint + ExtRecordPat
  sem getPatStringCode indent env =
  | PatExtRecord {ident = ident, bindings = bindings} ->
    match pprintTypeName env ident with (env, ident) in
    if mapIsEmpty bindings then (env, join ["{", ident, " of nothing}"])
    else match record2tuple bindings with Some pats then
      match mapAccumL (lam env. lam e. getPatStringCode indent env e) env pats
      with (env, tuplePats) in
      let merged =
        match tuplePats with [e]
        then concat e ","
        else strJoin ", " tuplePats in
      (env, join ["(", merged, ")"])
    else match
      mapMapAccum
        (lam env. lam k. lam v.
           match getPatStringCode indent env v with (env,str) in
           (env,join [pprintLabelString k, " = ", str]))
         env bindings
    with (env,bindMap) in
    (env,join ["{", ident, " of ", strJoin ", " (mapValues bindMap), "}"])
end

lang SynProdExtDeclPrettyPrint = DeclPrettyPrint + SynProdExtDeclAst
  sem pprintDeclCode (indent : Int) (env : PprintEnv) =
  | SynDeclProdExt t ->
    match pprintTypeName env t.ident with (env, typeNameStr) in
    match mapAccumL pprintEnvGetStr env t.params with (env, params) in
    let params = join (map (concat " ") params) in
    match
      mapAccumL (lam env. lam indivExt.
        match pprintConName env indivExt.ident with (env, str) in
        match getTypeStringCode (pprintIncr indent) env indivExt.tyIdent
        with (env, ty) in
        (env, join ["| ", str, " ", ty])
      ) env t.individualExts
    with (env, indivExtStr) in

    match
      match t.globalExt with Some ext then
        match getTypeStringCode (pprintIncr indent) env ext
        with (env, str) in (env, str)
      else
        (env, "")
    with (env, globExtStr) in

    (env, strJoin (pprintNewline indent)
                  (cons (join ["syn ", typeNameStr, params, " *= ", globExtStr]) indivExtStr))

end


lang ExtRecPrettyPrint = ExtRecTermPrettyPrint +
                         TypeAbsPrettyPrint + TypeAbsAppAst +
                         DeclCosemPrettyPrint +
                         DeclCosynPrettyPrint + PatExtRecordPrettyPrint +
                         MLangPrettyPrint + SynProdExtDeclPrettyPrint
end