-- Language fragments for MLang, extending those of MExpr.
--
-- The Decl syntax fragment contains the top-level declarations in an
-- MCore file such as DeclInclude, DeclUtest, DeclLang, but also
-- declarations that must be inside language fragments (DeclSyn and DeclSem).
-- As such it is possible to create invalid MCore ASTs using this fragment by,
-- for example, putting a DeclInclude or DeclUtest inside of a DeclInclude or
-- by putting a DeclSyn or DeclSem at the top-level.
--
-- This fragement also extends the MExpr Expr and Type syntax fragments
-- by adding a TmUse and TyUse respectively. 
--
-- An MLang program consists of a list of Decls and the expression to be 
-- evaluated.

include "map.mc"
include "name.mc"
include "option.mc"
include "string.mc"
include "stringid.mc"

include "mexpr/ast.mc"
include "mexpr/info.mc"

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

  sem smapAccumL_Expr_Expr f acc =
  | TmUse t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmUse {t with inexpr = inexpr})
end

lang TyUseAst = Ast
  syn Type = 
  | TyUse {ident : Name,
           info : Info,
           inty : Type}

  sem infoTy =
  | TyUse {info = info} -> info

  sem tyWithInfo info = 
  | TyUse t -> TyUse {t with info = info}
end

-- Base fragment for MLang declarations --
lang DeclAst = Ast
  syn Decl = -- intentionally left blank

  sem infoDecl = 
end

-- DeclLang --
lang LangDeclAst = DeclAst
  syn Decl =
  | DeclLang {ident : Name,
              includes : [Name],
              decls : [Decl],
              info : Info}

  sem infoDecl = 
  | DeclLang d -> d.info
end

-- DeclSyn --
lang SynDeclAst = DeclAst
  syn Decl =
  | DeclSyn {ident : Name,
             params : [Name],
             defs : [{ident : Name, tyIdent : Type}],
             -- The list of syns whose constructors should be included.
             -- The first string identifies the langauge of the include
             -- and the second string identifies the name.
             includes : [(String, String)],
             info : Info}

  sem infoDecl = 
  | DeclSyn d -> d.info
end

-- DeclSem --
lang SemDeclAst = DeclAst
  syn Decl =
  | DeclSem {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             args : Option [{ident : Name, tyAnnot : Type}],
             cases : [{pat : Pat, thn : Expr}],
             -- The list of semantic function s whose cases should be included.
             -- The first string identifies the langauge of the include
             -- and the second string identifies the name.
             includes : [(String, String)],
             info : Info}

  sem infoDecl = 
  | DeclSem d -> d.info
end


-- DeclLet --
lang LetDeclAst = DeclAst
  syn Decl =
  | DeclLet {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             body : Expr,
             info: Info}

  sem infoDecl = 
  | DeclLet d -> d.info
end

-- DeclType --
lang TypeDeclAst = DeclAst
  syn Decl =
  | DeclType {ident : Name,
              params : [Name],
              tyIdent : Type,
              info : Info}

  sem infoDecl = 
  | DeclType d -> d.info
end

-- DeclRecLets --
lang RecLetsDeclAst = DeclAst + RecLetsAst
  syn Decl =
  | DeclRecLets {bindings : [RecLetBinding],
                 info : Info}

  sem infoDecl = 
  | DeclRecLets d -> d.info          
end

-- DeclConDef --
lang DataDeclAst = DeclAst
  syn Decl =
  | DeclConDef {ident : Name,
                tyIdent : Type,
                info : Info}

  sem infoDecl = 
  | DeclConDef d -> d.info
end

-- DeclUtest --
lang UtestDeclAst = DeclAst
  syn Decl =
  | DeclUtest {test : Expr,
               expected : Expr,
               tusing : Option Expr,
               info : Info}

  sem infoDecl =
  | DeclUtest d -> d.info
end

-- DeclExt --
lang ExtDeclAst = DeclAst
  syn Decl =
  | DeclExt {ident : Name,
             tyIdent : Type,
             effect : Bool,
             info : Info}

  sem infoDecl =
  | DeclExt d -> d.info             
end

-- DeclInclude --
lang IncludeDeclAst = DeclAst
  syn Decl =
  | DeclInclude {path : String,
                 info : Info}

  sem infoDecl =
  | DeclInclude d -> d.info         
end


lang MLangTopLevel = DeclAst
  type MLangProgram = {
    decls : [Decl],
    expr : Expr
  }
end


lang MLangAst =

  -- Top level program
  MLangTopLevel

  -- Additional expressions
  + UseAst

  -- Declarations
  + LangDeclAst + SynDeclAst + SemDeclAst + LetDeclAst + TypeDeclAst
  + RecLetsDeclAst + DataDeclAst + UtestDeclAst + ExtDeclAst + IncludeDeclAst 
  + TyUseAst

end
