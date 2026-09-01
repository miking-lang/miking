-- Alpha equivalence for the MLang-level extensions to the MExpr AST
-- (DeclUse, TyUse, and the MLangProgram wrapper). Builds on top of
-- MExprEq.

include "ast.mc"
include "mexpr/eq.mc"
include "name.mc"
include "basic-types.mc"
include "option.mc"
include "string.mc"
include "seq.mc"
include "mexpr/info.mc"

lang UseEq = Eq + UseDeclAst
  sem eqDeclH (env : EqEnv) (free : EqEnv) (lhs : Decl) +=
  | DeclUse {ident = i2} ->
    match lhs with DeclUse {ident = i1} then
      if nameEqStr i1 i2 then Some (env, free) else None ()
    else None ()
end

lang TyUseEq = Eq + TyUseAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) +=
  | TyUse {ident = i2, inty = ty2} ->
    match unwrapType lhs with TyUse {ident = i1, inty = ty1} then
      if nameEqStr i1 i2 then eqTypeH typeEnv free ty1 ty2 else None ()
    else None ()
end

lang IncludeEq = Eq + IncludeDeclAst
  sem eqDeclH (env : EqEnv) (free : EqEnv) (lhs : Decl) +=
  | DeclInclude {path = p2} ->
    match lhs with DeclInclude {path = p1} then
      if eqString p1 p2 then Some (env, free) else None ()
    else None ()
end

lang SynEq = Eq + SynDeclAst
  sem eqDeclH (env : EqEnv) (free : EqEnv) (lhs : Decl) +=
  | DeclSyn {ident = i2, params = p2, defs = d2} ->
    match lhs with DeclSyn {ident = i1, params = p1, defs = d1} then
      match env with {conEnv = conEnv} in
      let envWithIdent = {env with conEnv = biInsert (i1, i2) conEnv} in
      if eqi (length p1) (length p2) then
        if eqi (length d1) (length d2) then
          let tyVarEnv = foldl2 (lam e. lam a. lam b. biInsert (a, b) e) biEmpty p1 p2 in
          let typeEnv = {tyVarEnv = tyVarEnv} in
          let typeFree = {freeTyVars = biEmpty, freeTyFlex = biEmpty} in
          let defPairs = zip d1 d2 in
          let tysOk = optionFoldlM
            (lam typeFree. lam dd : ({ident : Name, tyIdent : Type, info : Info}, {ident : Name, tyIdent : Type, info : Info}).
              eqTypeH typeEnv typeFree (dd.0).tyIdent (dd.1).tyIdent)
            typeFree defPairs
          in
          match tysOk with Some _ then
            let conEnv = foldl
              (lam e. lam dd : ({ident : Name, tyIdent : Type, info : Info}, {ident : Name, tyIdent : Type, info : Info}).
                biInsert ((dd.0).ident, (dd.1).ident) e)
              envWithIdent.conEnv defPairs
            in
            Some ({envWithIdent with conEnv = conEnv}, free)
          else None ()
        else None ()
      else None ()
    else None ()
end

lang SemEq = Eq + SemDeclAst + MatchEq
  sem eqDeclH (env : EqEnv) (free : EqEnv) (lhs : Decl) +=
  | DeclSem {ident = i2, tyAnnot = ty2, impl = impl2} ->
    match lhs with DeclSem {ident = i1, tyAnnot = ty1, impl = impl1} then
      match env with {varEnv = varEnv} in
      let envWithIdent = {env with varEnv = biInsert (i1, i2) varEnv} in
      switch (impl1, impl2)
      case (None (), None ()) then
        let typeEnv = {tyVarEnv = biEmpty} in
        let typeFree = {freeTyVars = biEmpty, freeTyFlex = biEmpty} in
        match eqTypeH typeEnv typeFree ty1 ty2 with Some _ then
          Some (envWithIdent, free)
        else None ()
      case (Some im1, Some im2) then
        if eqi (length im1.params) (length im2.params) then
          if eqi (length im1.cases) (length im2.cases) then
            let paramVarEnv = foldl2
              (lam e. lam a : {ident : Name, tyAnnot : Type, tyParam : Type, info : Info}.
                      lam b : {ident : Name, tyAnnot : Type, tyParam : Type, info : Info}.
                biInsert (a.ident, b.ident) e)
              envWithIdent.varEnv im1.params im2.params
            in
            let envWithParams = {envWithIdent with varEnv = paramVarEnv} in
            let casesOk = optionFoldlM
              (lam free. lam cc : ({pat : Pat, body : Expr, info : Info}, {pat : Pat, body : Expr, info : Info}).
                match eqPat envWithParams free biEmpty (cc.0).pat (cc.1).pat with Some n then
                  match n with (free, patEnv) in
                  eqExprH {envWithParams with varEnv = biMergePreferRight envWithParams.varEnv patEnv}
                    free (cc.0).body (cc.1).body
                else None ())
              free (zip im1.cases im2.cases)
            in
            match casesOk with Some free then Some (envWithIdent, free) else None ()
          else None ()
        else None ()
      case _ then None ()
      end
    else None ()
end

lang LangEq = Eq + LangDeclAst
  sem eqDeclH (env : EqEnv) (free : EqEnv) (lhs : Decl) +=
  | DeclLang {ident = i2, includes = inc2, decls = d2} ->
    match lhs with DeclLang {ident = i1, includes = inc1, decls = d1} then
      match env with {conEnv = conEnv} in
      let envWithIdent = {env with conEnv = biInsert (i1, i2) conEnv} in
      if eqi (length inc1) (length inc2) then
        let incsOk = forAll
          (lam p : ((Name, Info), (Name, Info)). nameEqStr (p.0).0 (p.1).0)
          (zip inc1 inc2)
        in
        if incsOk then
          if eqi (length d1) (length d2) then
            optionFoldlM
              (lam envs : (EqEnv, EqEnv). lam dd : (Decl, Decl).
                match envs with (env, free) in
                eqDeclH env free dd.0 dd.1)
              (envWithIdent, free) (zip d1 d2)
          else None ()
        else None ()
      else None ()
    else None ()
end

lang MLangEq = MExprEq + MLangTopLevel + UseEq + TyUseEq + IncludeEq + SynEq + SemEq + LangEq
  sem eqProgram : MLangProgram -> MLangProgram -> Bool
  sem eqProgram p1 =
  | p2 ->
    if eqi (length p1.decls) (length p2.decls) then
      let empty = {varEnv = biEmpty, conEnv = biEmpty} in
      let envs =
        optionFoldlM
          (lam envs : (EqEnv, EqEnv). lam ds : (Decl, Decl).
            match envs with (env, free) in
            eqDeclH env free ds.0 ds.1)
          (empty, empty)
          (zip p1.decls p2.decls)
      in
      match envs with Some (env, free) then
        match eqExprH env free p1.expr p2.expr with Some _ then true
        else false
      else false
    else false
end
