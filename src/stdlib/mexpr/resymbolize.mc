-- Provides functionality for replacing symbols of bound variables in a
-- provided expression with new symbols.
--
-- This pass can be used to construct copies of an AST where it is important
-- that all variables within are distinct (e.g., for monomorphization).

include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

lang Resymbolize = Ast
  sem resymbolizeBindings : Expr -> Expr
  sem resymbolizeBindings =
  | e -> resymbolizeExpr (mapEmpty nameCmp) e

  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizePat  : Map Name Name -> Pat -> (Map Name Name, Pat)
  sem resymbolizeType : Map Name Name -> Type -> Type
end

lang ResymbolizeOpaque = Resymbolize + OpaqueAst
  sem resymbolizeExpr nameMap =
  | TmOpaque x -> TmOpaque
    { x with body = resymbolizeExpr nameMap x.body
    , ty = resymbolizeType nameMap x.ty
    }
end

lang ResymbolizeVar = Resymbolize + VarAst
  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | TmVar t ->
    let newId =
      match mapLookup t.ident nameMap with Some newId then newId
      else t.ident
    in
    TmVar {t with ident = newId, ty = resymbolizeType nameMap t.ty}
end

lang ResymbolizeLam = Resymbolize + LamAst
  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | TmLam t ->
    let newId = nameSetNewSym t.ident in
    let nameMap = mapInsert t.ident newId nameMap in
    TmLam {t with ident = newId,
                  tyAnnot = resymbolizeType nameMap t.tyAnnot,
                  tyParam = resymbolizeType nameMap t.tyParam,
                  body = resymbolizeExpr nameMap t.body,
                  ty = resymbolizeType nameMap t.ty}
end

lang ResymbolizeConApp = Resymbolize + DataAst
  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | TmConApp t ->
    let newId =
      match mapLookup t.ident nameMap with Some newId then newId
      else t.ident
    in
    TmConApp {t with ident = newId,
                     body = resymbolizeExpr nameMap t.body,
                     ty = resymbolizeType nameMap t.ty}
end

lang ResymbolizeMatch = Resymbolize + MatchAst
  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | TmMatch t ->
    let target = resymbolizeExpr nameMap t.target in
    match resymbolizePat nameMap t.pat with (thnNameMap, pat) in
    TmMatch {t with target = target, pat = pat,
                    thn = resymbolizeExpr thnNameMap t.thn,
                    els = resymbolizeExpr nameMap t.els,
                    ty = resymbolizeType nameMap t.ty}
end

lang ResymbolizeDecl = Resymbolize + DeclAst
  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | TmDecl t ->
    match resymbolizeDecl nameMap t.decl with (nameMap, decl) in
    let inexpr = resymbolizeExpr nameMap t.inexpr in
    TmDecl {t with decl = decl, inexpr = inexpr}
end

lang ResymbolizeLetDecl = Resymbolize + LetDeclAst
  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizeDecl nameMap =
  | DeclLet t ->
    let body = resymbolizeExpr nameMap t.body in
    let newId = nameSetNewSym t.ident in
    let nameMap = mapInsert t.ident newId nameMap in
    ( nameMap
    , DeclLet
      { t with ident = newId
      , tyAnnot = resymbolizeType nameMap t.tyAnnot
      , tyBody = resymbolizeType nameMap t.tyBody
      , body = body
      }
    )
end

lang ResymbolizeRecLetsDecl = Resymbolize + RecLetsDeclAst
  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizeDecl nameMap =
  | DeclRecLets t ->
    let addNewIdBinding = lam nameMap. lam bind.
      let newId = nameSetNewSym bind.ident in
      (mapInsert bind.ident newId nameMap, {bind with ident = newId})
    in
    match mapAccumL addNewIdBinding nameMap t.bindings with (nameMap, bindings) in
    let resymbolizeBind = lam bind.
      {bind with tyAnnot = resymbolizeType nameMap bind.tyAnnot,
                 tyBody = resymbolizeType nameMap bind.tyBody,
                 body = resymbolizeExpr nameMap bind.body}
    in
    let bindings = map resymbolizeBind bindings in
    (nameMap, DeclRecLets {t with bindings = bindings})
end

lang ResymbolizeTypeDecl = Resymbolize + TypeDeclAst
  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizeDecl nameMap =
  | DeclType t ->
    let newId = nameSetNewSym t.ident in
    let nameMap = mapInsert t.ident newId nameMap in
    ( nameMap
    , DeclType
      { t with ident = newId
      , tyIdent = resymbolizeType nameMap t.tyIdent
      }
    )
end

lang ResymbolizeConDefDecl = Resymbolize + DataDeclAst
  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizeDecl nameMap =
  | DeclConDef t ->
    let newId = nameSetNewSym t.ident in
    let nameMap = mapInsert t.ident newId nameMap in
    (nameMap, DeclConDef {t with ident = newId, tyIdent = resymbolizeType nameMap t.tyIdent})
end

lang ResymbolizeNamedPat = Resymbolize + NamedPat
  sem resymbolizePat : Map Name Name -> Pat -> (Map Name Name, Pat)
  sem resymbolizePat nameMap =
  | PatNamed (t & {ident = PName id}) ->
    let newId = nameSetNewSym id in
    (mapInsert id newId nameMap, PatNamed {t with ident = PName newId})
end

lang ResymbolizeSeqEdgePat = Resymbolize + SeqEdgePat
  sem resymbolizePat : Map Name Name -> Pat -> (Map Name Name, Pat)
  sem resymbolizePat nameMap =
  | PatSeqEdge (t & {middle = PName id}) ->
    let newId = nameSetNewSym id in
    (mapInsert id newId nameMap, PatSeqEdge {t with middle = PName newId})
end

lang ResymbolizePatCon = Resymbolize + DataPat
  sem resymbolizePat : Map Name Name -> Pat -> (Map Name Name, Pat)
  sem resymbolizePat nameMap =
  | PatCon t ->
    match mapLookup t.ident nameMap with Some newId then
      (nameMap, PatCon {t with ident = newId})
    else (nameMap, PatCon t)
end

lang ResymbolizeConType = Resymbolize + ConTypeAst
  sem resymbolizeType : Map Name Name -> Type -> Type
  sem resymbolizeType nameMap =
  | TyCon t ->
    match mapLookup t.ident nameMap with Some newId then
      TyCon {t with ident = newId}
    else TyCon t
end

lang ResymbolizeVarType = Resymbolize + VarTypeAst
  sem resymbolizeType : Map Name Name -> Type -> Type
  sem resymbolizeType nameMap =
  | TyVar t ->
    match mapLookup t.ident nameMap with Some newId then
      TyVar {t with ident = newId}
    else TyVar t
end

lang ResymbolizeAllType = Resymbolize + AllTypeAst
  sem resymbolizeType : Map Name Name -> Type -> Type
  sem resymbolizeType nameMap =
  | TyAll t ->
    let newId = nameSetNewSym t.ident in
    let nameMap = mapInsert t.ident newId nameMap in
    TyAll {t with ident = newId,
                  ty = resymbolizeType nameMap t.ty}
end

lang MExprResymbolize =
  -- Expr
  ResymbolizeVar + ResymbolizeLam + ResymbolizeConApp + ResymbolizeMatch + ResymbolizeDecl +
  ResymbolizeOpaque +

  -- Decl
  ResymbolizeLetDecl + ResymbolizeRecLetsDecl + ResymbolizeTypeDecl + ResymbolizeConDefDecl +

  -- Pat
  ResymbolizeNamedPat + ResymbolizeSeqEdgePat + ResymbolizePatCon +

  -- Type
  ResymbolizeConType + ResymbolizeVarType + ResymbolizeAllType

  sem resymbolizeExpr : Map Name Name -> Expr -> Expr
  sem resymbolizeExpr nameMap =
  | t ->
    let t = smap_Expr_Expr (resymbolizeExpr nameMap) t in
    let t = smap_Expr_Type (resymbolizeType nameMap) t in
    let t = smap_Expr_TypeLabel (resymbolizeType nameMap) t in
    withType (resymbolizeType nameMap (tyTm t)) t

  sem resymbolizeDecl : Map Name Name -> Decl -> (Map Name Name, Decl)
  sem resymbolizeDecl nameMap =
  | d -> (nameMap, smap_Decl_Expr (resymbolizeExpr nameMap) d)

  sem resymbolizePat : Map Name Name -> Pat -> (Map Name Name, Pat)
  sem resymbolizePat nameMap =
  | p -> smapAccumL_Pat_Pat resymbolizePat nameMap p

  sem resymbolizeType : Map Name Name -> Type -> Type
  sem resymbolizeType nameMap =
  | ty -> smap_Type_Type (resymbolizeType nameMap) ty
end

lang TestLang = MExprResymbolize + MExprEq + MExprPrettyPrint + MExprSym
  sem collectSymVars : Expr -> Map String Name
  sem collectSymVars =
  | e -> collectSymVarsH (mapEmpty cmpString) e

  sem collectSymVarsH : Map String Name -> Expr -> Map String Name
  sem collectSymVarsH acc =
  | TmVar t ->
    if nameHasSym t.ident then mapInsert (nameGetStr t.ident) t.ident acc
    else acc
  | t -> sfold_Expr_Expr collectSymVarsH acc t
end

mexpr

use TestLang in

let optionGet = lam o. optionGetOrElse (lam. never) o in
let nameNotEq = lam l. lam r. not (nameEq l r) in

-- Unsymbolized variables in the AST are symbolized
let e = resymbolizeBindings (var_ "x") in
let syms = collectSymVars e in
utest mapMem "x" syms with false in

-- Variables bound in the AST are re-symbolized
let x = nameSym "x" in
let e = resymbolizeBindings (bind_ (nulet_ x (int_ 2)) (nvar_ x)) in
let syms = collectSymVars e in
utest mapMem "x" syms with true in
utest optionGet (mapLookup "x" syms) with x using nameNotEq in

-- Unsymbolized variables that are bound in the AST are symbolized
let e = resymbolizeBindings (bind_ (ulet_ "x" (int_ 2)) (var_ "x")) in
let syms = collectSymVars e in
utest mapMem "x" syms with true in

-- Symbolized free variables are not re-symbolized
let y = nameSym "y" in
let e = resymbolizeBindings
  (bind_
    (nulet_ x (int_ 2))
    (addi_ (nvar_ x) (nvar_ y)))
in
let syms = collectSymVars e in
utest mapMem "x" syms with true in
utest mapMem "y" syms with true in
utest optionGet (mapLookup "x" syms) with x using nameNotEq in
utest optionGet (mapLookup "y" syms) with y using nameEq in

()
