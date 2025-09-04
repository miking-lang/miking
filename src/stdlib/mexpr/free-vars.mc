-- This file contains language fragments and functions related to free
-- variables.

include "set.mc"
include "name.mc"

include "mexpr/ast.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"

lang FreeVars = Ast
  -- Returns the set of free variables for a given expression. Assumes
  -- that the expression is symbolized (and no Names are defined more
  -- than once).
  sem freeVars : Expr -> Set Name
  sem freeVars =| t -> freeVarsExpr (setEmpty nameCmp) t

  sem freeVarsExpr : Set Name -> Expr -> Set Name
  sem freeVarsExpr acc =
  | t -> sfold_Expr_Expr freeVarsExpr acc t
end

lang FreeNames = Ast
  -- A broader form of freeVars that returns free occurrences of all
  -- Names, including variables, constructors, type constructors, and
  -- type variables. Same assumptions as for freeVars. Does not look
  -- at inferred types, only explicit annotations.
  sem freeNames : Expr -> Set Name
  sem freeNames = | tm ->
    freeNamesExpr (setEmpty nameCmp) tm
  sem freeNamesExpr : Set Name -> Expr -> Set Name
  sem freeNamesExpr free = | tm ->
    let free = sfold_Expr_Expr freeNamesExpr free tm in
    let free = sfold_Expr_Type freeNamesType free tm in
    free
  sem freeNamesType : Set Name -> Type -> Set Name
  sem freeNamesType free = | ty ->
    let free = sfold_Type_Type freeNamesType free ty in
    free
  sem freeNamesPat : Set Name -> Pat -> Set Name
  sem freeNamesPat free = | pat ->
    let free = sfold_Pat_Pat freeNamesPat free pat in
    let free = sfold_Pat_Type freeNamesType free pat in
    free
end

lang VarFreeVars = FreeVars + VarAst
  sem freeVarsExpr acc =
  | TmVar r -> setInsert r.ident acc
end

lang VarFreeNames = FreeNames + VarAst
  sem freeNamesExpr free =
  | TmVar x -> setInsert x.ident free
end

lang LamFreeVars = FreeVars + LamAst
  sem freeVarsExpr acc =
  | TmLam r ->
    setRemove r.ident (freeVarsExpr acc r.body)
end

lang LamFreeNames = FreeNames + LamAst
  sem freeNamesExpr free =
  | TmLam x ->
    let free = freeNamesExpr free x.body in
    let free = setRemove x.ident free in
    let free = freeNamesType free x.tyAnnot in
    free
end

lang LetFreeVars = FreeVars + LetDeclAst
  sem freeVarsExpr acc =
  | TmDecl {decl = DeclLet r, inexpr = inexpr} ->
    setRemove r.ident (freeVarsExpr (freeVarsExpr acc r.body) inexpr)
end

lang LetFreeNames = FreeNames + LetDeclAst + AllTypeAst
  sem freeNamesExpr free =
  | TmDecl {decl = DeclLet x, inexpr = inexpr} ->
    let free = freeNamesExpr free inexpr in
    let free = setRemove x.ident free in
    let free = freeNamesExpr free x.body in
    match stripTyAll x.tyAnnot with (tyalls, tyAnnot) in
    let free = freeNamesType free tyAnnot in
    -- NOTE(vipa, 2025-03-19): This also handles removing type
    -- variables from `.body`, not just `.tyAnnot`.
    let free = foldl (lam free. lam pair. setRemove pair.0 free) free tyalls in
    free
end

lang RecLetsFreeVars = FreeVars + RecLetsDeclAst
  sem freeVarsExpr acc =
  | TmDecl {decl = DeclRecLets r, inexpr = inexpr} ->
    let acc = foldl (lam acc. lam b.
      freeVarsExpr acc b.body) (freeVarsExpr acc inexpr) r.bindings in
    foldl (lam acc. lam b. setRemove b.ident acc) acc r.bindings
end

lang RecLetsFreeNames = FreeNames + RecLetsDeclAst + AllTypeAst
  sem freeNamesExpr free =
  | TmDecl {decl = DeclRecLets x, inexpr = inexpr} ->
    let free = freeNamesExpr free inexpr in
    let f = lam free. lam binding.
      let free = freeNamesExpr free binding.body in
      match stripTyAll binding.tyAnnot with (tyalls, tyAnnot) in
      let free = freeNamesType free tyAnnot in
      let free = foldl (lam free. lam pair. setRemove pair.0 free) free tyalls in
      free in
    let free = foldl f free x.bindings in
    let free = foldl (lam free. lam b. setRemove b.ident free) free x.bindings in
    free
end

lang TypeFreeNames = FreeNames + TypeDeclAst
  sem freeNamesExpr free =
  | TmDecl {decl = DeclType x, inexpr = inexpr} ->
    let free = freeNamesExpr free inexpr in
    let free = freeNamesType free x.tyIdent in
    let free = foldr setRemove free x.params in
    let free = setRemove x.ident free in
    free
end

lang DataFreeNames = FreeNames + DataAst + DataDeclAst
  sem freeNamesExpr free =
  | TmDecl {decl = DeclConDef x, inexpr = inexpr} ->
    let free = freeNamesExpr free inexpr in
    let free = setRemove x.ident free in
    let free = freeNamesType free x.tyIdent in
    free
  | TmConApp x ->
    let free = freeNamesExpr free x.body in
    let free = setInsert x.ident free in
    free
end

lang ExtFreeNames = FreeNames + ExtDeclAst
  sem freeNamesExpr free =
  | TmDecl {decl = DeclExt x, inexpr = inexpr} ->
    let free = freeNamesExpr free inexpr in
    let free = setRemove x.ident free in
    let free = freeNamesType free x.tyIdent in
    free
end

lang MatchFreeVars = FreeVars + MatchAst + NamedPat + SeqEdgePat
  sem freeVarsExpr acc =
  | TmMatch r ->
    freeVarsExpr
      (freeVarsExpr
         (bindVarsPat
            (freeVarsExpr acc r.thn)
            r.pat)
         r.els)
      r.target

  sem bindVarsPat : Set Name -> Pat -> Set Name
  sem bindVarsPat acc =
  | PatNamed {ident = PName ident} -> setRemove ident acc
  | pat & (PatSeqEdge {middle = PName ident}) ->
    let acc = setRemove ident acc in
    sfold_Pat_Pat bindVarsPat acc pat
  | pat -> sfold_Pat_Pat bindVarsPat acc pat
end

lang MatchFreeNames = FreeNames + MatchAst
  sem freeNamesExpr free =
  | TmMatch x ->
    let free = freeNamesExpr free x.thn in
    -- NOTE(vipa, 2025-03-19): This will remove whatever the pattern
    -- itself binds from free, hence the weird order
    let free = freeNamesPat free x.pat in
    let free = freeNamesExpr free x.target in
    let free = freeNamesExpr free x.els in
    free
end

lang NamedPatFreeNames = FreeNames + NamedPat
  sem freeNamesPat free =
  | PatNamed {ident = PName ident} -> setRemove ident free
end

lang SeqEdgePatFreeNames = FreeNames + SeqEdgePat
  sem freeNamesPat free =
  | PatSeqEdge (x & {middle = PName ident}) ->
    let free = setRemove ident free in
    let free = foldl freeNamesPat free x.prefix in
    let free = foldl freeNamesPat free x.postfix in
    free
end

lang DataPatFreeNames = FreeNames + DataPat
  sem freeNamesPat free =
  | PatCon x ->
    let free = freeNamesPat free x.subpat in
    let free = setInsert x.ident free in
    free
end

-- VariantTypeFreeNames?

lang ConTypeFreeNames = FreeNames + ConTypeAst
  sem freeNamesType free =
  | TyCon x -> setInsert x.ident free
end

-- TyData?

lang VarTypeFreeNames = FreeNames + VarTypeAst
  sem freeNamesType free =
  | TyVar x -> setInsert x.ident free
end

lang AllTypeFreeNames = FreeNames + AllTypeAst
  sem freeNamesType free =
  | TyAll x ->
    let free = freeNamesType free x.ty in
    let free = setRemove x.ident free in
    free
end

lang MExprFreeVars =
  VarFreeVars + LamFreeVars + LetFreeVars + RecLetsFreeVars + MatchFreeVars
end

lang MExprFreeNames =
  LamFreeNames + LetFreeNames + RecLetsFreeNames + TypeFreeNames + DataFreeNames +
  ExtFreeNames + MatchFreeNames + NamedPatFreeNames + SeqEdgePatFreeNames +
  DataPatFreeNames + ConTypeFreeNames + VarTypeFreeNames + AllTypeFreeNames + VarFreeNames
end

lang TestLang = MExprFreeVars + MExprSym + BootParser end

mexpr

use TestLang in

let parseProgram : String -> Expr =
  lam str.
    let parseArgs =
      {defaultBootParserParseMExprStringArg with allowFree = true}
    in
    let ast = parseMExprStringExn parseArgs str in
    symbolizeExpr {symEnvEmpty with allowFree = true} ast
in

-------------------
-- Test freeVars --
-------------------

let testFreeVars = lam prog.
  let fv = freeVars prog in
  sort cmpString (map nameGetStr (setToSeq fv))
in

let prog = parseProgram "
  lam x. x x y y y
  "
in

utest testFreeVars prog with ["y"] in

let prog = parseProgram "
  let x = z in x x y y y
  "
in

utest testFreeVars prog with ["y", "z"] in

let prog = parseProgram "
  recursive let f = lam x. w f (f x) in
  recursive let g = lam y. z f (g y) in
  w z (f (g u))
  "
in

utest testFreeVars prog with ["u", "w", "z"] in

let prog = parseProgram "
  match u with (x, (y, z)) in
  x y y z z z u w w
  "
in

utest testFreeVars prog with ["u", "w"] in

let prog = parseProgram "
  match t with [x] ++ xs in
    x xs t r
  "
in

utest testFreeVars prog with ["r", "t"] in

let prog = parseProgram "
  match t with [first] ++ mid ++ [last] in
    first mid f r last t
  "
in

utest testFreeVars prog with ["f", "r", "t"] in

()
