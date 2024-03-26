-- Language fragments for MLang, extending those of MExpr

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

  sem smapAccumL_Expr_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | TmUse t ->
    match f acc t.inexpr with (acc, inexpr) in
    (acc, TmUse {t with inexpr = inexpr})
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
             includes : [{ident : Name, tyIdent : Type}],
             info : Info}

  sem infoDecl = 
  | DeclSyn d -> d.info
end

-- DeclSynProdExt
-- synIdent:    Name of the syntax to be extended
-- extIdent:    Name of this is extension
-- globalExt:   Extension to be added to every constructor
-- specificExt: Associated list of constructors and the specific
--              extension to be added to said constructor
lang SynProdExtDeclAst = DeclAst
  syn Decl = 
  | DeclSynProdExt {synIdent : Name,
                    extIdent : Name,
                    globalExt : Type,
                    specificExt : [{ident : Name, tyIdent : Type}],
                    info : Info}

  sem infoDecl = 
  | DeclSynProdExt d -> d.info
end
-- DeclSem --
lang SemDeclAst = DeclAst
  syn Decl =
  | DeclSem {ident : Name,
             tyAnnot : Type,
             tyBody : Type,
             args : [{ident : Name, tyAnnot : Type}],
             cases : [{pat : Pat, thn : Expr}],
             includes : [{pat : Pat, thn : Expr}],
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
  + SynProdExtDeclAst +RecLetsDeclAst + DataDeclAst + UtestDeclAst
  + ExtDeclAst + IncludeDeclAst

end
