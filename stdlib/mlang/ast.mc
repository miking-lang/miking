-- Language fragments for MLang, extending those of MExpr

include "info.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "string.mc"
include "stringid.mc"
include "mexpr/ast.mc"


-- TmUse --
lang UseAst = Ast
  syn Expr =
  | TmUse {ident : Name,
           inexpr : Expr,
           ty : Type,
           info : Info}

  sem infoTm =
  | TmUse t -> t.info

  sem tyTm =
  | TmUse t -> t.ty

  sem withInfo (info : Info) =
  | TmUse t -> TmUse {t with info = info}

  sem withType (ty : Type) =
  | TmUse t -> TmUse {t with ty = ty}

  sem smapAccumL_Expr_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | TmUse t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmUse {t with inexpr = inexpr})
end

-- TmInclude --
lang IncludeAst = Ast
  syn Expr =
  | TmInclude {path : String,
               inexpr : Expr,
               ty : Type,
               info : Info}

  sem infoTm =
  | TmInclude t -> t.info

  sem tyTm =
  | TmInclude t -> t.ty

  sem withInfo (info : Info) =
  | TmInclude t -> TmInclude {t with info = info}

  sem withType (ty : Type) =
  | TmInclude t -> TmInclude {t with ty = ty}

  sem smapAccumL_Expr_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | TmInclude t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmInclude {t with inexpr = inexpr})
end

-- Base fragment for MLang declarations --
lang DeclAst = Ast
  syn Decl = -- intentionally left blank
end

-- DeclLang --
lang LangDeclAst = DeclAst
  syn Decl =
  | DeclLang {name : Name,
              includes : [Name],
              decls : [Decl],
              info : Info}
end

-- syn --
lang SynDeclAst = DeclAst
  syn Decl =
  | DeclSyn {name : Name,
             defs : [{ident : Name, tyIdent : Type}],
             info : Info}
end

-- sem --
lang SemDeclAst = DeclAst
  syn Decl =
  | DeclSem {name : Name,
             tyAnnot : Type,
             tyBody : Type,
             args : [{ident : Name, ty : Type}],
             cases : [{pat : Pat, thn : Expr}],
             info : Info}
end

-- DeclLet --
lang LetDeclAst = DeclAst
  syn Decl =
  | DeclLet {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             body : Expr,
             info : Info}
end

-- DeclType --
lang TypeDeclAst = DeclAst
  syn Decl =
  | DeclType {ident : Name,
              params : [Name],
              tyIdent : Type,
              info : Info}
end

-- DeclRecLets --
lang RecLetDeclAst = DeclAst + RecLetsAst
  syn Decl =
  | DeclRecLets {bindings : [RecLetBinding],
                 info : Info}
end

-- DeclConDef --
lang ConDeclAst = DeclAst
  syn Decl =
  | DeclConDef {ident : Name,
                tyIdent : Type,
                info : Info}
end

-- DeclUtest --
lang UtestDeclAst = DeclAst
  syn Decl =
  | DeclUtest {test : Expr,
               expected : Expr,
               tusing : Option Expr,
               info : Info}
end

-- DeclExt --
lang ExtDeclAst = DeclAst
  syn Decl =
  | DeclExt {ident : Name,
             tyIdent : Type,
             effect : Bool,
             info : Info}
end

-- DeclInclude --
lang IncludeDeclAst = DeclAst
  syn Decl =
  | DeclInclude {path : String,
                 info : Info}
end
