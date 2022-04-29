-- Basics, always present
include "seq.mc"
include "option.mc"
include "parser/breakable.mc"
include "parser/ll1.mc"

/-
token Integer {
  include: "lexer.mc";
  lang: UIntTokenParser;
  type: "Int";
  unitConstructor: "IntRepr ()";
}
token String {
  include: "lexer.mc";
  lang: StringTokenParser;
  type: "String";
  unitConstructor: "StringRepr ()";
}
token Operator {
  include: "lexer.mc";
  lang: OperatorTokenParser;
  type: "String";
  unitConstructor: "OperatorRepr ()";
}
token HashString {
  include: "lexer.mc";
  lang: HashStringTokenParser;
  type: "String";
  constructor: "lam str. HashStringRepr {hash = str}"
}
token UIdent {
  include: "lexer.mc";
  lang: UIdentTokenParser;
  type: "String";
  unitConstructor: "UIdentRepr ()"
}
token LIdent {
  include: "lexer.mc";
  lang: LIdentTokenParser;
  type: "String";
  unitConstructor: "LIdentRepr ()"
}
token {
  include: "lexer.mc";
  lang: WhitespaceParser;
}
token {
  include: "lexer.mc";
  lang: LineCommentParser;
}
token {
  include: "lexer.mc";
  lang: MultilineCommentParser;
}
token {
  include: "lexer.mc";
  lang: BracketTokenParser;
}
token {
  include: "lexer.mc";
  lang: CommaTokenParser;
}
token {
  include: "lexer.mc";
  lang: SemiTokenParser;
}
-/
include "lexer.mc"

/-
token UName {
  base: UIdent;
  include: "name.mc";
  type: "Name";
  conversion: "nameNoSym";
}
token LName {
  base: LIdent;
  include: "name.mc";
  type: "Name";
  conversion: "nameNoSym";
}
-/
include "name.mc"

/-
start File
type File {
  suffix: false
}
type Decl
type Regex
type Expr
-/

lang SelfhostBaseAst
  syn File =
  syn Decl =
  syn Regex =
  syn Expr =

  sem get_File_info =
  sem get_Decl_info =
  sem get_Regex_info =
  sem get_Expr_info =

  sem smapAccumL_File_File (f : acc -> File -> (acc, File)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_File_Decl (f : acc -> Decl -> (acc, Decl)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_File_Regex (f : acc -> Regex -> (acc, Regex)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_File_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | x -> (acc, x)
  sem smap_File_File (f : File -> File) =
  | x -> match smapAccumL_File_File (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_File_Decl (f : Decl -> Decl) =
  | x -> match smapAccumL_File_Decl (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_File_Regex (f : Regex -> Regex) =
  | x -> match smapAccumL_File_Regex (lam. lam x. ((), f x)) () x with (_, x) in x
  sem sfold_File_File (f : acc -> File -> acc) (acc : acc) =
  | x -> match smapAccumL_File_File (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_File_Decl (f : acc -> Decl -> acc) (acc : acc) =
  | x -> match smapAccumL_File_Decl (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_File_Regex (f : acc -> Regex -> acc) (acc : acc) =
  | x -> match smapAccumL_File_Regex (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_File_Expr (f : acc -> Expr -> acc) (acc : acc) =
  | x -> match smapAccumL_File_Expr (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc

  sem smapAccumL_Decl_File (f : acc -> File -> (acc, File)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Decl_Decl (f : acc -> Decl -> (acc, Decl)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Decl_Regex (f : acc -> Regex -> (acc, Regex)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Decl_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | x -> (acc, x)
  sem smap_Decl_File (f : File -> File) =
  | x -> match smapAccumL_Decl_File (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Decl_Decl (f : Decl -> Decl) =
  | x -> match smapAccumL_Decl_Decl (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Decl_Regex (f : Regex -> Regex) =
  | x -> match smapAccumL_Decl_Regex (lam. lam x. ((), f x)) () x with (_, x) in x
  sem sfold_Decl_File (f : acc -> File -> acc) (acc : acc) =
  | x -> match smapAccumL_Decl_File (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Decl_Decl (f : acc -> Decl -> acc) (acc : acc) =
  | x -> match smapAccumL_Decl_Decl (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Decl_Regex (f : acc -> Regex -> acc) (acc : acc) =
  | x -> match smapAccumL_Decl_Regex (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Decl_Expr (f : acc -> Expr -> acc) (acc : acc) =
  | x -> match smapAccumL_Decl_Expr (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc

  sem smapAccumL_Regex_File (f : acc -> File -> (acc, File)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Regex_Decl (f : acc -> Decl -> (acc, Decl)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Regex_Regex (f : acc -> Regex -> (acc, Regex)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Regex_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | x -> (acc, x)
  sem smap_Regex_File (f : File -> File) =
  | x -> match smapAccumL_Regex_File (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Regex_Decl (f : Decl -> Decl) =
  | x -> match smapAccumL_Regex_Decl (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Regex_Regex (f : Regex -> Regex) =
  | x -> match smapAccumL_Regex_Regex (lam. lam x. ((), f x)) () x with (_, x) in x
  sem sfold_Regex_File (f : acc -> File -> acc) (acc : acc) =
  | x -> match smapAccumL_Regex_File (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Regex_Decl (f : acc -> Decl -> acc) (acc : acc) =
  | x -> match smapAccumL_Regex_Decl (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Regex_Regex (f : acc -> Regex -> acc) (acc : acc) =
  | x -> match smapAccumL_Regex_Regex (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Regex_Expr (f : acc -> Expr -> acc) (acc : acc) =
  | x -> match smapAccumL_Regex_Expr (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc

  sem smapAccumL_Expr_File (f : acc -> File -> (acc, File)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Expr_Decl (f : acc -> Decl -> (acc, Decl)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Expr_Regex (f : acc -> Regex -> (acc, Regex)) (acc : acc) =
  | x -> (acc, x)
  sem smapAccumL_Expr_Expr (f : acc -> Expr -> (acc, Expr)) (acc : acc) =
  | x -> (acc, x)
  sem smap_Expr_File (f : File -> File) =
  | x -> match smapAccumL_Expr_File (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Expr_Decl (f : Decl -> Decl) =
  | x -> match smapAccumL_Expr_Decl (lam. lam x. ((), f x)) () x with (_, x) in x
  sem smap_Expr_Regex (f : Regex -> Regex) =
  | x -> match smapAccumL_Expr_Regex (lam. lam x. ((), f x)) () x with (_, x) in x
  sem sfold_Expr_File (f : acc -> File -> acc) (acc : acc) =
  | x -> match smapAccumL_Expr_File (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Expr_Decl (f : acc -> Decl -> acc) (acc : acc) =
  | x -> match smapAccumL_Expr_Decl (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Expr_Regex (f : acc -> Regex -> acc) (acc : acc) =
  | x -> match smapAccumL_Expr_Regex (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
  sem sfold_Expr_Expr (f : acc -> Expr -> acc) (acc : acc) =
  | x -> match smapAccumL_Expr_Expr (lam acc. lam x. (f acc x, x)) acc x with (acc, _) in acc
end

lang FileOpBase
  syn FileOp =

  sem topAllowed_FileOp =
  | _ -> true
  sem leftAllowed_FileOp : {parent : FileOp LOpen rstyle1, child : FileOp lstyle rstyle2} -> Bool
  sem leftAllowed_FileOp =
  | {parent = _, child = c} -> topAllowed_FileOp c
  sem rightAllowed_FileOp : {parent : FileOp lstyle1 ROpen, child : FileOp lstyle2 rstyle} -> Bool
  sem rightAllowed_FileOp =
  | {parent = _, child = c} -> topAllowed_FileOp c
  sem groupingsAllowed_FileOp =
  | _ -> GEither ()
  sem parenAllowed_FileOp =
  | _ -> GEither ()
  sem get_FileOp_info =
  sem get_FileOp_terms =
  sem unsplit_FileOp =
end

lang DeclOpBase
  syn DeclOp =

  sem topAllowed_DeclOp =
  | _ -> true
  sem leftAllowed_DeclOp : {parent : DeclOp LOpen rstyle1, child : DeclOp lstyle rstyle2} -> Bool
  sem leftAllowed_DeclOp =
  | {parent = _, child = c} -> topAllowed_DeclOp c
  sem rightAllowed_DeclOp : {parent : DeclOp lstyle1 ROpen, child : DeclOp lstyle2 rstyle} -> Bool
  sem rightAllowed_DeclOp =
  | {parent = _, child = c} -> topAllowed_DeclOp c
  sem groupingsAllowed_DeclOp =
  | _ -> GEither ()
  sem parenAllowed_DeclOp =
  | _ -> GEither ()
  sem get_DeclOp_info =
  sem get_DeclOp_terms =
  sem unsplit_DeclOp =
end

lang RegexOpBase
  syn RegexOp =

  sem topAllowed_RegexOp =
  | _ -> true
  sem leftAllowed_RegexOp : {parent : RegexOp LOpen rstyle1, child : RegexOp lstyle rstyle2} -> Bool
  sem leftAllowed_RegexOp =
  | {parent = _, child = c} -> topAllowed_RegexOp c
  sem rightAllowed_RegexOp : {parent : RegexOp lstyle1 ROpen, child : RegexOp lstyle2 rstyle} -> Bool
  sem rightAllowed_RegexOp =
  | {parent = _, child = c} -> topAllowed_RegexOp c
  sem groupingsAllowed_RegexOp =
  | _ -> GEither ()
  sem parenAllowed_RegexOp =
  | _ -> GEither ()
  sem get_RegexOp_info =
  sem get_RegexOp_terms =
  sem unsplit_RegexOp =
end

lang ExprOpBase
  syn ExprOp =

  sem topAllowed_ExprOp =
  | _ -> true
  sem leftAllowed_ExprOp : {parent : ExprOp LOpen rstyle1, child : ExprOp lstyle rstyle2} -> Bool
  sem leftAllowed_ExprOp =
  | {parent = _, child = c} -> topAllowed_ExprOp c
  sem rightAllowed_ExprOp : {parent : ExprOp lstyle1 ROpen, child : ExprOp lstyle2 rstyle} -> Bool
  sem rightAllowed_ExprOp =
  | {parent = _, child = c} -> topAllowed_ExprOp c
  sem groupingsAllowed_ExprOp =
  | _ -> GEither ()
  sem parenAllowed_ExprOp =
  | _ -> GEither ()
  sem get_ExprOp_info =
  sem get_ExprOp_terms =
  sem unsplit_ExprOp =
end

/-
-- # File
prod File: File = decls:Decl+
-/

lang FileAst = SelfhostBaseAst
  syn File =
  | File { decls : [Decl], info : Info }

  sem get_File_info =
  | File x -> x.info

  sem smapAccumL_File_Decl f acc =
  | File x ->
    match mapAccumL f acc x.decls with (acc, decls) in
    (acc, File {x with decls = decls})
end

lang FileOp = FileOpBase + FileAst
  syn FileOp =
  | FileOp { decls : [Decl], info : Info, terms : [Info] }

  sem get_FileOp_terms =
  | FileOp x -> x.terms

  sem get_FileOp_info =
  | FileOp x -> x.info

  sem unsplit_FileOp =
  | AtomP { self = FileOp x } -> (x.info, File {decls = x.decls, info = x.info})
end

/-
-- # Decl
-/

/-
prod Start: Decl = "start" name:UName
-/

lang StartDeclAst = SelfhostBaseAst
  syn Decl =
  | StartDecl { name : {v: Name, i: Info}, info : Info }

  sem get_Decl_info =
  | StartDecl x -> x.info
end

lang StartDeclOp = DeclOpBase + StartDeclAst
  syn DeclOp =
  | StartDeclOp { name : {v: Name, i: Info}, info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | StartDeclOp x -> x.terms

  sem get_DeclOp_info =
  | StartDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = StartDeclOp x } -> (x.info, StartDecl {name = x.name, info = x.info})
end

/-
prod Type: Decl =
  "type" name:UName
  ( "{"
    properties:{name:LName "=" val:Expr ","}*
  "}"
  )?
-/

lang TypeDeclAst = SelfhostBaseAst
  syn Decl =
  | TypeDecl { name : {v: Name, i: Info}, properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info }

  sem get_Decl_info =
  | TypeDecl x -> x.info

  sem smapAccumL_Decl_Expr f acc =
  | TypeDecl x ->
    match mapAccumL (lam acc. lam x. match f acc x.val with (acc, val) in {x with val = val}) acc x.properties with (acc, properties) in
    (acc, TypeDecl {x with properties = properties})
end

lang TypeDeclOp = DeclOpBase + TypeDeclAst
  syn DeclOp =
  | TypeDeclOp { name : {v: Name, i: Info}, properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | TypeDeclOp x -> x.terms

  sem get_DeclOp_info =
  | TypeDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = TypeDeclOp x } -> (x.info, TypeDecl {name = x.name, properties = x.properties, info = x.info})
end

/-
prod Token: Decl =
  "token" name:UName?
  ( "{"
    properties:{name:LName "=" val:Expr ","}*
  "}"
  )?
-/

lang TokenDeclAst = SelfhostBaseAst
  syn Decl =
  | TokenDecl { name : Option {v: Name, i: Info}, properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info }

  sem get_Decl_info =
  | TokenDecl x -> x.info

  sem smapAccumL_Decl_Expr f acc =
  | TokenDecl x ->
    match mapAccumL (lam acc. lam x. match f acc x.val with (acc, val) in {x with val = val}) acc x.properties with (acc, properties) in
    (acc, TokenDecl {x with properties = properties})
end

lang TokenDeclOp = DeclOpBase + TokenDeclAst
  syn DeclOp =
  | TokenDeclOp { name : Option {v: Name, i: Info}, properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | TokenDeclOp x -> x.terms

  sem get_DeclOp_info =
  | TokenDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = TokenDeclOp x } -> (x.info, TokenDecl {name = x.name, properties = x.properties, info = x.info})
end

/-
prod PrecedenceTable: Decl =
  "precedence" "{"
    levels:{noeq:"~"? operators:UName+ ";"}*
  "}"
  ( "except" "{"
    exceptions:{lefts:UName+ "?" rights:UName+ ";"}*
  "}"
  )?
-/

lang PrecedenceTableDeclAst = SelfhostBaseAst
  syn Decl =
  | PrecedenceTableDecl
    { levels : [{noeq : Option {v: (), i: Info}, operators : [{v: Name, i: Info}]}]
    , exceptions : [{lefts : [{v: Name, i: Info}], rights : [{v: Name, i: Info}]}]
    , info : Info
    }

  sem get_Decl_info =
  | PrecedenceTableDecl x -> x.info
end

lang PrecedenceTableDeclOp = DeclOpBase + PrecedenceTableDeclAst
  syn DeclOp =
  | PrecedenceTableDeclOp
    { levels : [{noeq : Option (), operators : [{v: Name, i: Info}]}]
    , exceptions : [{lefts : [{v: Name, i: Info}], rights : [{v: Name, i: Info}]}]
    , info : Info
    , terms : [Info]
    }

  sem get_DeclOp_terms =
  | PrecedenceTableDeclOp x -> x.terms

  sem get_DeclOp_info =
  | PrecedenceTableDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = PrecedenceTableDeclOp x } -> (x.info, PrecedenceTableDecl {levels = x.levels, exceptions = x.exceptions, info = x.info})
end

/-
prod Production: Decl = ("prod" | "infix" | "prefix" | "postfix") assoc:LIdent? name:UName ":" nt:UName "=" regex:Regex
-/

lang ProductionDeclAst = SelfhostBaseAst
  syn Decl =
  | ProductionDecl { assoc : Option {v: String, i: Info}, name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info }

  sem get_Decl_info =
  | ProductionDecl x -> x.info

  sem smapAccumL_Decl_Regex f acc =
  | ProductionDecl x ->
    match f acc x.regex with (acc, regex) in
    (acc, ProductionDecl {x with regex = regex})
end

lang ProductionDeclOp = DeclOpBase + ProductionDeclAst
  syn DeclOp =
  | ProductionDeclOp { assoc : Option {v: Name, i: Info}, name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | ProductionDeclOp x -> x.terms

  sem get_DeclOp_info =
  | ProductionDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = ProductionDeclOp x } -> (x.info, ProductionDecl {assoc = x.assoc, name = x.name, nt = x.nt, regex = x.regex, info = x.info})
end

/-
prod Infix: Decl = "infix" assoc:LIdent? name:UName ":" nt:UName "=" regex:Regex
-/

lang InfixDeclAst = SelfhostBaseAst
  syn Decl =
  | InfixDecl { assoc : Option {v: Name, i: Info}, name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info }

  sem get_Decl_info =
  | InfixDecl x -> x.info

  sem smapAccumL_Decl_Regex f acc =
  | InfixDecl x ->
    match f acc x.regex with (acc, regex) in
    (acc, InfixDecl {x with regex = regex})
end

lang InfixDeclOp = DeclOpBase + InfixDeclAst
  syn DeclOp =
  | InfixDeclOp { assoc : Option {v: Name, i: Info}, name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | InfixDeclOp x -> x.terms

  sem get_DeclOp_info =
  | InfixDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = InfixDeclOp x } -> (x.info, InfixDecl {assoc = x.assoc, name = x.name, nt = x.nt, regex = x.regex, info = x.info})
end

/-
prod Prefix: Decl = "prefix" name:UName ":" nt:UName "=" regex:Regex
-/

lang PrefixDeclAst = SelfhostBaseAst
  syn Decl =
  | PrefixDecl { name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info }

  sem get_Decl_info =
  | PrefixDecl x -> x.info

  sem smapAccumL_Decl_Regex f acc =
  | PrefixDecl x ->
    match f acc x.regex with (acc, regex) in
    (acc, PrefixDecl {x with regex = regex})
end

lang PrefixDeclOp = DeclOpBase + PrefixDeclAst
  syn DeclOp =
  | PrefixDeclOp { name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | PrefixDeclOp x -> x.terms

  sem get_DeclOp_info =
  | PrefixDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = PrefixDeclOp x } -> (x.info, PrefixDecl {name = x.name, nt = x.nt, regex = x.regex, info = x.info})
end

/-
prod Postfix: Decl = "postfix" name:UName ":" nt:UName "=" regex:Regex
-/

lang PostfixDeclAst = SelfhostBaseAst
  syn Decl =
  | PostfixDecl { name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info }

  sem get_Decl_info =
  | PostfixDecl x -> x.info

  sem smapAccumL_Decl_Regex f acc =
  | PostfixDecl x ->
    match f acc x.regex with (acc, regex) in
    (acc, PostfixDecl {x with regex = regex})
end

lang PostfixDeclOp = DeclOpBase + PostfixDeclAst
  syn DeclOp =
  | PostfixDeclOp { name : {v: Name, i: Info}, nt : {v: Name, i: Info}, regex : Regex, info : Info, terms : [Info] }

  sem get_DeclOp_terms =
  | PostfixDeclOp x -> x.terms

  sem get_DeclOp_info =
  | PostfixDeclOp x -> x.info

  sem unsplit_DeclOp =
  | AtomP { self = PostfixDeclOp x } -> (x.info, PostfixDecl {name = x.name, nt = x.nt, regex = x.regex, info = x.info})
end

/-
-- # Regex
-/

/-
grouping "(" Regex ")"
-/

lang GroupingRegexOp = RegexOpBase
  syn RegexOp =
  | GroupingRegexOp { inner : Regex, info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | GroupingRegexOp x -> x.terms

  sem get_RegexOp_info =
  | GroupingRegexOp x -> x.info

  sem unsplit_RegexOp =
  | AtomP { self = GroupingRegexOp x } -> (x.info, x.inner)
end

/-
prod Record: Regex = "{" regex:Regex "}"
-/

lang RecordRegexAst = SelfhostBaseAst
  syn Regex =
  | RecordRegex { regex : Regex, info : Info }

  sem get_Regex_info =
  | RecordRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | RecordRegex x ->
    match f acc x.regex with (acc, regex) in
    (acc, RecordRegex {x with regex = regex})
end

lang RecordRegexOp = RegexOpBase + RecordRegexAst
  syn RegexOp =
  | RecordRegexOp { regex : Regex, info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | RecordRegexOp x -> x.terms

  sem get_RegexOp_info =
  | RecordRegexOp x -> x.info

  sem unsplit_RegexOp =
  | AtomP { self = RecordRegexOp x } -> (x.info, RecordRegex {regex = x.regex, info = x.info})
end

/-
prod Empty: Regex = "empty"
-/

lang EmptyRegexAst = SelfhostBaseAst
  syn Regex =
  | EmptyRegex { info : Info }

  sem get_Regex_info =
  | EmptyRegex x -> x.info
end

lang EmptyRegexOp = RegexOpBase + EmptyRegexAst
  syn RegexOp =
  | EmptyRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | EmptyRegexOp x -> x.terms

  sem get_RegexOp_info =
  | EmptyRegexOp x -> x.info

  sem unsplit_RegexOp =
  | AtomP { self = EmptyRegexOp x } -> (x.info, EmptyRegex {info = x.info})
end

/-
prod Literal: Regex = val:String
-/

lang LiteralRegexAst = SelfhostBaseAst
  syn Regex =
  | LiteralRegex { val : String, info : Info }

  sem get_Regex_info =
  | LiteralRegex x -> x.info
end

lang LiteralRegexOp = RegexOpBase + LiteralRegexAst
  syn RegexOp =
  | LiteralRegexOp { val : String, info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | LiteralRegexOp x -> x.terms

  sem get_RegexOp_info =
  | LiteralRegexOp x -> x.info

  sem unsplit_RegexOp =
  | AtomP { self = LiteralRegexOp x } -> (x.info, LiteralRegex {val = x.val, info = x.info})
end

/-
prod Token: Regex = name:UName ("[" arg:Expr "]")?
-/

lang TokenRegexAst = SelfhostBaseAst
  syn Regex =
  | TokenRegex { name : {v: Name, i: Info}, arg : Option Expr, info : Info }

  sem get_Regex_info =
  | TokenRegex x -> x.info

  sem smapAccumL_Regex_Expr f acc =
  | TokenRegex x ->
    match optionMapAccum f acc x.arg with (acc, arg) in
    (acc, TokenRegex {x with arg = arg })
end

lang TokenRegexOp = RegexOpBase + TokenRegexAst
  syn RegexOp =
  | TokenRegexOp { name : {v: Name, i: Info}, arg : Option Expr, info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | TokenRegexOp x -> x.terms

  sem get_RegexOp_info =
  | TokenRegexOp x -> x.info

  sem unsplit_RegexOp =
  | AtomP { self = TokenRegexOp x } -> (x.info, TokenRegex {name = x.name, arg = x.arg, info = x.info})
end

/-
postfix RepeatPlus: Regex = "+"
-/

lang RepeatPlusRegexAst = SelfhostBaseAst
  syn Regex =
  | RepeatPlusRegex { left : Regex, info : Info }

  sem get_Regex_info =
  | RepeatPlusRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | RepeatPlusRegex x ->
    match f acc x.left with (acc, left) in
    (acc, RepeatPlusRegex {x with left = left})
end

lang RepeatPlusRegexOp = RegexOpBase + RepeatPlusRegexAst
  syn RegexOp =
  | RepeatPlusRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | RepeatPlusRegexOp x -> x.terms

  sem get_RegexOp_info =
  | RepeatPlusRegexOp x -> x.info

  sem unsplit_RegexOp =
  | PostfixP { self = RepeatPlusRegexOp x, leftChildAlts = [left] ++ _ } ->
    match unsplit_RegexOp left with (linfo, left) in
    let info = mergeInfo linfo x.info in
    (info, RepeatPlusRegex { left = left, info = info })
end

/-
postfix RepeatStar: Regex = "*"
-/

lang RepeatStarRegexAst = SelfhostBaseAst
  syn Regex =
  | RepeatStarRegex { left : Regex, info : Info }

  sem get_Regex_info =
  | RepeatStarRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | RepeatStarRegex x ->
    match f acc x.left with (acc, left) in
    (acc, RepeatStarRegex {x with left = left})
end

lang RepeatStarRegexOp = RegexOpBase + RepeatStarRegexAst
  syn RegexOp =
  | RepeatStarRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | RepeatStarRegexOp x -> x.terms

  sem get_RegexOp_info =
  | RepeatStarRegexOp x -> x.info

  sem unsplit_RegexOp =
  | PostfixP { self = RepeatStarRegexOp x, leftChildAlts = [left] ++ _ } ->
    match unsplit_RegexOp left with (linfo, left) in
    let info = mergeInfo linfo x.info in
    (info, RepeatStarRegex { left = left, info = info })
end

/-
postfix RepeatQuestion: Regex = "?"
-/

lang RepeatQuestionRegexAst = SelfhostBaseAst
  syn Regex =
  | RepeatQuestionRegex { left : Regex, info : Info }

  sem get_Regex_info =
  | RepeatQuestionRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | RepeatQuestionRegex x ->
    match f acc x.left with (acc, left) in
    (acc, RepeatQuestionRegex {x with left = left})
end

lang RepeatQuestionRegexOp = RegexOpBase + RepeatQuestionRegexAst
  syn RegexOp =
  | RepeatQuestionRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | RepeatQuestionRegexOp x -> x.terms

  sem get_RegexOp_info =
  | RepeatQuestionRegexOp x -> x.info

  sem unsplit_RegexOp =
  | PostfixP { self = RepeatQuestionRegexOp x, leftChildAlts = [left] ++ _ } ->
    match unsplit_RegexOp left with (linfo, left) in
    let info = mergeInfo linfo x.info in
    (info, RepeatQuestionRegex { left = left, info = info })
end

/-
prefix Named: Regex = name:LIdent ":"
-/

lang NamedRegexAst = SelfhostBaseAst
  syn Regex =
  | NamedRegex { name : {v: String, i: Info}, right : Regex, info : Info }

  sem get_Regex_info =
  | NamedRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | NamedRegex x ->
    match f acc x.right with (acc, right) in
    (acc, NamedRegex {x with right = right})
end

lang NamedRegexOp = RegexOpBase + NamedRegexAst
  syn RegexOp =
  | NamedRegexOp { name : {v: String, i: Info}, info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | NamedRegexOp x -> x.terms

  sem get_RegexOp_info =
  | NamedRegexOp x -> x.info

  sem unsplit_RegexOp =
  | PrefixP { self = NamedRegexOp x, rightChildAlts = [right] ++ _ } ->
    match unsplit_RegexOp right with (rinfo, right) in
    let info = mergeInfo x.info rinfo in
    (info, NamedRegex { name = x.name, right = right, info = info })
end

/-
infix left Alternative: Regex = "|"
-/

lang AlternativeRegexAst = SelfhostBaseAst
  syn Regex =
  | AlternativeRegex { left : Regex, right : Regex, info : Info }

  sem get_Regex_info =
  | AlternativeRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | AlternativeRegex x ->
    match f acc x.left with (acc, left) in
    match f acc x.right with (acc, right) in
    (acc, AlternativeRegex {{x with left = left} with right = right})
end

lang AlternativeRegexOp = RegexOpBase + AlternativeRegexAst
  syn RegexOp =
  | AlternativeRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | AlternativeRegexOp x -> x.terms

  sem get_RegexOp_info =
  | AlternativeRegexOp x -> x.info

  sem groupingsAllowed_RegexOp =
  | (AlternativeRegexOp _, AlternativeRegexOp _) -> GLeft ()

  sem unsplit_RegexOp =
  | InfixP { self = AlternativeRegexOp x, leftChildAlts = [left] ++ _, rightChildAlts = [right] ++ _ } ->
    match unsplit_RegexOp left with (linfo, left) in
    match unsplit_RegexOp right with (rinfo, right) in
    let info = mergeInfo linfo rinfo in
    (info, AlternativeRegex { left = left, right = right, info = info })
end

/-
infix left Concat: Regex = empty
-/

lang ConcatRegexAst = SelfhostBaseAst
  syn Regex =
  | ConcatRegex { left : Regex, right : Regex, info : Info }

  sem get_Regex_info =
  | ConcatRegex x -> x.info

  sem smapAccumL_Regex_Regex f acc =
  | ConcatRegex x ->
    match f acc x.left with (acc, left) in
    match f acc x.right with (acc, right) in
    (acc, ConcatRegex {{x with left = left} with right = right})
end

lang ConcatRegexOp = RegexOpBase + ConcatRegexAst
  syn RegexOp =
  | ConcatRegexOp { info : Info, terms : [Info] }

  sem get_RegexOp_terms =
  | ConcatRegexOp x -> x.terms

  sem get_RegexOp_info =
  | ConcatRegexOp x -> x.info

  sem groupingsAllowed_RegexOp =
  | (ConcatRegexOp _, ConcatRegexOp _) -> GLeft ()

  sem unsplit_RegexOp =
  | InfixP { self = ConcatRegexOp x, leftChildAlts = [left] ++ _, rightChildAlts = [right] ++ _ } ->
    match unsplit_RegexOp left with (linfo, left) in
    match unsplit_RegexOp right with (rinfo, right) in
    let info = mergeInfo linfo rinfo in
    (info, ConcatRegex { left = left, right = right, info = info })
end

/-
precedence {
  Named;
  RepeatPlus RepeatStar RepeatQuestion;
  Concat;
  Alternative;
}
-/

lang SelfhostPrecedence1
  = NamedRegexOp + RepeatPlusRegexOp + RepeatStarRegexOp + RepeatQuestionRegexOp
  + ConcatRegexOp + AlternativeRegexOp

  sem groupingsAllowed_RegexOp =
  | (NamedRegexOp _, RepeatPlusRegexOp _) -> GLeft ()
  | (NamedRegexOp _, RepeatStarRegexOp _) -> GLeft ()
  | (NamedRegexOp _, RepeatQuestionRegexOp _) -> GLeft ()
  | (NamedRegexOp _, ConcatRegexOp _) -> GLeft ()
  | (NamedRegexOp _, AlternativeRegexOp _) -> GLeft ()
  | (ConcatRegexOp _, RepeatPlusRegexOp _) -> GRight ()
  | (ConcatRegexOp _, RepeatStarRegexOp _) -> GRight ()
  | (ConcatRegexOp _, RepeatQuestionRegexOp _) -> GRight ()
  | (AlternativeRegexOp _, RepeatPlusRegexOp _) -> GRight ()
  | (AlternativeRegexOp _, RepeatStarRegexOp _) -> GRight ()
  | (AlternativeRegexOp _, RepeatQuestionRegexOp _) -> GRight ()
  | (ConcatRegexOp _, AlternativeRegexOp _) -> GLeft ()
  | (AlternativeRegexOp _, ConcatRegexOp _) -> GRight ()
end

lang SelfhostAst
  = FileAst
  + StartDeclAst + TypeDeclAst + TokenDeclAst + PrecedenceTableDeclAst + ProductionDeclAst
  + InfixDeclAst + PrefixDeclAst + PostfixDeclAst
  + RecordRegexAst + EmptyRegexAst + LiteralRegexAst + TokenRegexAst
  + RepeatPlusRegexAst + RepeatStarRegexAst + RepeatQuestionRegexAst
  + NamedRegexAst + AlternativeRegexAst + ConcatRegexAst
end

lang ParseSelfhost = SelfhostAst + TokenParser
  + UIntTokenParser + StringTokenParser + HashStringTokenParser + UIdentTokenParser + LIdentTokenParser + OperatorTokenParser
  + WhitespaceParser + LineCommentParser + MultilineCommentParser + BracketTokenParser + CommaTokenParser + SemiTokenParser
  + FileOpBase + DeclOpBase + RegexOpBase + ExprOpBase
  + FileOp
  + StartDeclOp + TypeDeclOp + TokenDeclOp + PrecedenceTableDeclOp + ProductionDeclOp + InfixDeclOp + PrefixDeclOp + PostfixDeclOp
  + GroupingRegexOp + RecordRegexOp + EmptyRegexOp + LiteralRegexOp + TokenRegexOp + RepeatPlusRegexOp + RepeatStarRegexOp + RepeatQuestionRegexOp + NamedRegexOp + AlternativeRegexOp + ConcatRegexOp
  + SelfhostPrecedence1
  + LL1Parser

  syn File =
  | BadFile { info : Info }

  sem get_File_info =
  | BadFile x -> x.info

  syn Decl =
  | BadDecl { info : Info }

  sem get_Decl_info =
  | BadDecl x -> x.info

  syn Regex =
  | BadRegex { info : Info }

  sem get_Regex_info =
  | BadRegex x -> x.info

  syn Expr =
  | BadExpr { info : Info }

  sem get_Expr_info =
  | BadExpr x -> x.info
end

let _table =
  type State = {errors : Ref [(Info, String)], content : String} in
  use ParseSelfhost in
  let brFile =
    let config =
      { topAllowed = topAllowed_FileOp
      , leftAllowed = leftAllowed_FileOp
      , rightAllowed = rightAllowed_FileOp
      , parenAllowed = parenAllowed_FileOp
      , groupingsAllowed = groupingsAllowed_FileOp
      } in
    let mkOptInputFunction = lam addF.
      lam p : State. lam x. lam st.
      match st with Some st then
        let st = addF config x st in
        (match st with None _ then
          let err = (get_FileOp_info x, "Invalid input") in
          modref p.errors (snoc (deref p.errors) err)
         else ());
        st
      else st in
    let mkInputFunction =
      lam addF. lam p. lam x. lam st. optionMap (addF config x) st in
    { atom = mkInputFunction breakableAddAtom
    , infix = mkOptInputFunction breakableAddInfix
    , prefix = mkInputFunction breakableAddPrefix
    , postfix = mkOptInputFunction breakableAddPostfix
    , finalize = lam p : State. lam st.
      let res = optionBind st
        (lam st. match breakableFinalizeParse config st with Some [top] ++ _
          then Some (unsplit_FileOp top)
          else modref p.errors (snoc (deref p.errors) (NoInfo (), "Unfinished File"));-- TODO(vipa, 2022-03-11): Figure out how to get a good info field here
            None ()) in
      -- TODO(vipa, 2022-03-11): Also here
      optionGetOr (NoInfo (), BadFile {info = NoInfo ()}) res
    } in
  let brDecl =
    let config =
      { topAllowed = topAllowed_DeclOp
      , leftAllowed = leftAllowed_DeclOp
      , rightAllowed = rightAllowed_DeclOp
      , parenAllowed = parenAllowed_DeclOp
      , groupingsAllowed = groupingsAllowed_DeclOp
      } in
    let mkOptInputFunction = lam addF.
      lam p : State. lam x. lam st.
      match st with Some st then
        let st = addF config x st in
        (match st with None _ then
          let err = (get_DeclOp_info x, "Invalid input") in
          modref p.errors (snoc (deref p.errors) err)
         else ());
        st
      else st in
    let mkInputFunction =
      lam addF. lam p. lam x. lam st. optionMap (addF config x) st in
    { atom = mkInputFunction breakableAddAtom
    , infix = mkOptInputFunction breakableAddInfix
    , prefix = mkInputFunction breakableAddPrefix
    , postfix = mkOptInputFunction breakableAddPostfix
    , finalize = lam p : State. lam st.
      let res = optionBind st
        (lam st. match breakableFinalizeParse config st with Some [top] ++ _
          then Some (unsplit_DeclOp top)
          else modref p.errors (snoc (deref p.errors) (NoInfo (), "Unfinished Decl"));-- TODO(vipa, 2022-03-11): Figure out how to get a good info field here
            None ()) in
      -- TODO(vipa, 2022-03-11): Also here
      optionGetOr (NoInfo (), BadDecl {info = NoInfo ()}) res
    } in
  let brRegex =
    let config =
      { topAllowed = topAllowed_RegexOp
      , leftAllowed = leftAllowed_RegexOp
      , rightAllowed = rightAllowed_RegexOp
      , parenAllowed = parenAllowed_RegexOp
      , groupingsAllowed = groupingsAllowed_RegexOp
      } in
    let reportConfig =
      { parenAllowed = parenAllowed_RegexOp
      , topAllowed = topAllowed_RegexOp
      , terminalInfos = get_RegexOp_terms
      , getInfo = get_RegexOp_info
      , lpar = "("
      , rpar = ")"
      } in
    let mkOptInputFunction = lam addF.
      lam p : State. lam x. lam st.
      match st with Some st then
        let st = addF config x st in
        (match st with None _ then
          let err = (get_RegexOp_info x, "Invalid input") in
          modref p.errors (snoc (deref p.errors) err)
         else ());
        st
      else st in
    let mkInputFunction =
      lam addF. lam p. lam x. lam st. optionMap (addF config x) st in
    { atom = mkInputFunction breakableAddAtom
    , infix = mkOptInputFunction breakableAddInfix
    , prefix = mkInputFunction breakableAddPrefix
    , postfix = mkOptInputFunction breakableAddPostfix
    , finalize = lam p : State. lam st.
      let res = optionBind st
        (lam st. match breakableFinalizeParse config st with Some (tops & [top] ++ _)
          then
            let errs = breakableDefaultHighlight reportConfig p.content tops in
            let res: (Info, Regex) = unsplit_RegexOp top in
            if null errs then Some res else
            modref p.errors (concat (deref p.errors) errs);
            Some (res.0, BadRegex { info = res.0 })
          else
            modref p.errors (snoc (deref p.errors) (NoInfo (), "Unfinished Regex"));-- TODO(vipa, 2022-03-11): Figure out how to get a good info field here
            None ()) in
      -- TODO(vipa, 2022-03-11): Also here
      optionGetOr (NoInfo (), BadRegex {info = NoInfo ()}) res
    } in
  let brExpr =
    let config =
      { topAllowed = topAllowed_ExprOp
      , leftAllowed = leftAllowed_ExprOp
      , rightAllowed = rightAllowed_ExprOp
      , parenAllowed = parenAllowed_ExprOp
      , groupingsAllowed = groupingsAllowed_ExprOp
      } in
    let reportConfig =
      { parenAllowed = parenAllowed_ExprOp
      , topAllowed = topAllowed_ExprOp
      , terminalInfos = get_ExprOp_terms
      , getInfo = get_ExprOp_info
      , lpar = "("
      , rpar = ")"
      } in
    let mkOptInputFunction = lam addF.
      lam p : State. lam x. lam st.
      match st with Some st then
        let st = addF config x st in
        (match st with None _ then
          let err = (get_ExprOp_info x, "Invalid input") in
          modref p.errors (snoc (deref p.errors) err)
         else ());
        st
      else st in
    let mkInputFunction =
      lam addF. lam p : State. lam x. lam st. optionMap (addF config x) st in
    { atom = mkInputFunction breakableAddAtom
    , infix = mkOptInputFunction breakableAddInfix
    , prefix = mkInputFunction breakableAddPrefix
    , postfix = mkOptInputFunction breakableAddPostfix
    , finalize = lam p : State. lam st.
      let res = optionBind st
        (lam st. match breakableFinalizeParse config st with Some (tops & [top] ++ _)
          then
            let errs = breakableDefaultHighlight reportConfig p.content tops in
            let res: (Info, Expr) = unsplit_ExprOp top in
            if null errs then Some res else
            modref p.errors (concat (deref p.errors) errs);
            Some (res.0, BadExpr { info = res.0 })
          else
            modref p.errors (snoc (deref p.errors) (NoInfo (), "Unfinished Expr"));-- TODO(vipa, 2022-03-11): Figure out how to get a good info field here
            None ()) in
      -- TODO(vipa, 2022-03-11): Also here
      optionGetOr (NoInfo (), BadExpr {info = NoInfo ()}) res
    } in
  let brState = lam. Some (breakableInitState ()) in

  let file_top = string2NonTerminal "File_Top" in
  let file_lclosed = string2NonTerminal "File_LClosed" in
  let file_lopen = string2NonTerminal "File_LOpen" in
  let file_atom = string2NonTerminal "File_Atom" in
  let file_File_cont = string2NonTerminal "File_File_Cont" in

  let decl_top = string2NonTerminal "Decl_Top" in
  let decl_lclosed = string2NonTerminal "Decl_LClosed" in
  let decl_lopen = string2NonTerminal "Decl_LOpen" in
  let decl_atom = string2NonTerminal "Decl_Atom" in
  let decl_Production_1 = string2NonTerminal "Decl_Production_1" in
  let decl_Production_2 = string2NonTerminal "Decl_Production_2" in
  let decl_Type_1 = string2NonTerminal "Decl_Type_1" in
  let decl_Type_2 = string2NonTerminal "Decl_Type_2" in
  let decl_PrecedenceTable_1 = string2NonTerminal "Decl_PrecedenceTable_1" in
  let decl_PrecedenceTable_2 = string2NonTerminal "Decl_PrecedenceTable_2" in

  let regex_top = string2NonTerminal "Regex_Top" in
  let regex_lclosed = string2NonTerminal "Regex_LClosed" in
  let regex_lopen = string2NonTerminal "Regex_LOpen" in
  let regex_atom = string2NonTerminal "Regex_Atom" in
  let regex_prefix = string2NonTerminal "Regex_Prefix" in
  let regex_postfix = string2NonTerminal "Regex_Postfix" in
  let regex_infix = string2NonTerminal "Regex_Infix" in
  let regex_Token_1 = string2NonTerminal "Regex_Token_1" in

  let expr_top = string2NonTerminal "Expr_Top" in
  let expr_lclosed = string2NonTerminal "Expr_LClosed" in
  let expr_lopen = string2NonTerminal "Expr_LOpen" in
  let expr_atom = string2NonTerminal "Expr_Atom" in
  let expr_prefix = string2NonTerminal "Expr_Prefix" in
  let expr_postfix = string2NonTerminal "Expr_Postfix" in
  let expr_infix = string2NonTerminal "Expr_Infix" in

  let grammar =
    { start = file_top
    , productions =
      [ { nt = file_top
        , label = "File_Top"
        , rhs = [ntSym file_lclosed]
        , action = lam p. lam seq.
          match seq with [UserSym cont] in
          cont (brState ())
        }
      , { nt = file_lclosed
        , label = "File_LClosed"
        , rhs = [ntSym file_atom, ntSym file_lopen]
        , action = lam p. lam seq.
          match seq with [UserSym atom, UserSym cont] in
          lam st. cont (brFile.atom p atom st)
        }
      , { nt = file_lopen
        , label = "File_End"
        , rhs = []
        , action = lam p. lam.
          brFile.finalize p
        }

      , { nt = file_atom
        , label = "File_File"
        , rhs = [ntSym decl_top, ntSym file_File_cont]
        , action = lam. lam seq.
          match seq with [UserSym (info, decl), UserSym cont] in
          cont {info = info, decls = [decl], terms = []}
        }
      , { nt = file_File_cont
        , label = "File_File_Cont"
        , rhs = [ntSym decl_top, ntSym file_File_cont]
        , action = lam. lam seq.
          match seq with [UserSym (info, decl), UserSym cont] in
          lam x: {info : Info, decls : [Decl], terms : [Info]}.
            cont {{x with info = mergeInfo x.info info} with decls = snoc x.decls decl}
        }
      , { nt = file_File_cont
        , label = "File_File_End"
        , rhs = []
        , action = lam. lam.
          lam x: {info : Info, decls : [Decl], terms : [Info]}.
            FileOp {decls = x.decls, terms = x.terms, info = x.info}
        }

      , { nt = decl_top
        , label = "Decl_Top"
        , rhs = [ntSym decl_lclosed]
        , action = lam p. lam seq.
          match seq with [UserSym cont] in
          cont (brState ())
        }
      , { nt = decl_lclosed
        , label = "Decl_LClosed"
        , rhs = [ntSym decl_atom, ntSym decl_lopen]
        , action = lam p. lam seq.
          match seq with [UserSym atom, UserSym cont] in
          lam st. cont (brDecl.atom p atom st)
        }
      , { nt = decl_lopen
        , label = "Decl_End"
        , rhs = []
        , action = lam p. lam.
          brDecl.finalize p
        }

      , { nt = decl_atom
        , label = "Decl_Production"
        , rhs = [litSym "prod", ntSym decl_Production_1]
        , action = lam. lam seq.
          match seq with [LitParsed prod, UserSym prev] in
          let prev: {info : Info, terms : [Info], assoc : [{v: String, i: Info}], name : [{v: Name, i: Info}], nt : [{v: Name, i: Info}], regex : [Regex]} = prev in
          let prev = {{prev with info = mergeInfo prod.info prev.info} with terms = cons prod.info prev.terms} in
          ProductionDeclOp
            { assoc = match prev.assoc with [x] ++ _ then Some x else None ()
            , name = match prev.name with [x] ++ _ in x
            , nt = match prev.nt with [x] ++ _ in x
            , regex = match prev.regex with [x] ++ _ in x
            , info = prev.info
            , terms = prev.terms
            }
        }
      , { nt = decl_Production_1
        , label = "Decl_Production_1"
        , rhs = [ntSym decl_Production_2]
        , action = lam. lam seq.
          match seq with [UserSym prev] in prev
        }
      , { nt = decl_Production_1
        , label = "Decl_Production_2"
        , rhs = [tokSym (LIdentRepr ()), ntSym decl_Production_2]
        , action = lam. lam seq.
          match seq with [TokParsed (LIdentTok tok), UserSym prev] in
          let prev: {info : Info, terms : [Info], assoc : [{v: String, i: Info}], name : [{v: Name, i: Info}], nt : [{v: Name, i: Info}], regex : [Regex]} = prev in
          let prev = {{{prev with info = mergeInfo tok.info prev.info} with terms = cons tok.info prev.terms} with assoc = cons {v = tok.val, i = tok.info} prev.assoc} in
          prev
        }
      , { nt = decl_Production_2
        , label = "Decl_Production_3"
        , rhs = [tokSym (UIdentRepr ()), litSym ":", tokSym (UIdentRepr ()), litSym "=", ntSym regex_top]
        , action = lam. lam seq.
          match seq with [TokParsed (UIdentTok name), LitParsed x1, TokParsed (UIdentTok nt), LitParsed x2, UserSym (regexInfo, regex)] in
          { info = mergeInfo name.info regexInfo
          , terms = [name.info, x1.info, nt.info, x2.info]
          , assoc = []
          , name = [{v = (nameNoSym) name.val, i = name.info}]
          , nt = [{v = (nameNoSym) nt.val, i = nt.info}]
          , regex = [regex]
          }
        }
      , { nt = decl_atom
        , label = "Decl_Start_1"
        , rhs = [litSym "start", tokSym (UIdentRepr ())]
        , action = lam p. lam seq.
          match seq with [LitParsed l, TokParsed (UIdentTok name)] in
          StartDeclOp
            { name = {v = nameNoSym name.val, i = name.info}
            , info = mergeInfo l.info name.info
            , terms = [l.info, name.info]
            }
        }
      , { nt = decl_atom
        , label = "Decl_Type_1"
        , rhs = [litSym "type", tokSym (UIdentRepr ()), ntSym decl_Type_1]
        , action = lam p. lam seq.
          match seq with [LitParsed l, TokParsed (UIdentTok name), UserSym prev] in
          let prev : {name : [{v: Name, i: Info}], properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info, terms : [Info]} = prev in
          let prev = {{{prev
            with name = cons {v = (nameNoSym name.val), i = name.info} prev.name}
            with info = mergeInfo l.info (mergeInfo name.info prev.info)}
            with terms = concat [l.info, name.info] prev.terms} in
          TypeDeclOp
            { name = match prev.name with [name] ++ _ in name
            , properties = prev.properties
            , info = prev.info
            , terms = prev.terms
            }
        }
      , { nt = decl_Type_1
        , label = "Decl_Type_2"
        , rhs = []
        , action = lam p. lam seq.
          { info = NoInfo ()
          , name = []
          , properties = []
          , terms = []
          }
        }
      , { nt = decl_Type_1
        , label = "Decl_Type_3"
        , rhs = [litSym "{", ntSym decl_Type_2, litSym "}"]
        , action = lam p. lam seq.
          match seq with [LitParsed l, UserSym prev, LitParsed r] in
          let prev : {properties : [{name : {v: Name, i: Info}, val : Expr}], terms : [Info]} = prev in
          { info = mergeInfo l.info r.info
          , name = []
          , properties = prev.properties
          , terms = cons l.info (snoc prev.terms r.info)
          }
        }
      , { nt = decl_Type_2
        , label = "Decl_Type_4"
        , rhs = []
        , action = lam p. lam seq.
          { properties = []
          , terms = []
          }
        }
      , { nt = decl_Type_2
        , label = "Decl_Type_5"
        , rhs = [tokSym (LIdentRepr ()), litSym "=", ntSym expr_top, litSym ",", ntSym decl_Type_2]
        , action = lam p. lam seq.
          match seq with [TokParsed (LIdentTok name), LitParsed eq, UserSym (_, expr), LitParsed comma, UserSym prev] in
          let prev: {properties : [{name : {v: Name, i: Info}, val : Expr}], terms : [Info]} = prev in
          let prev = {{prev with properties = cons {name = {v = nameNoSym name.val, i = name.info}, val = expr} prev.properties} with terms = concat [name.info, eq.info, comma.info] prev.terms} in
          prev
        }
      , { nt = decl_atom
        , label = "Decl_Token_1"
        -- NOTE(vipa, 2022-03-21): I'm' reusing decl_Type_1 here,
        -- since the syntax is identical. This would presumably not be
        -- done for the actually generated code.
        , rhs = [litSym "token", tokSym (UIdentRepr ()), ntSym decl_Type_1]
        , action = lam p. lam seq.
          match seq with [LitParsed l, TokParsed (UIdentTok name), UserSym prev] in
          let prev : {name : [{v: Name, i: Info}], properties : [{name : {v: Name, i: Info}, val : Expr}], info : Info, terms : [Info]} = prev in
          let prev = {{{prev
            with name = cons {v = (nameNoSym name.val), i = name.info} prev.name}
            with info = mergeInfo l.info (mergeInfo name.info prev.info)}
            with terms = concat [l.info, name.info] prev.terms} in
          TokenDeclOp
            { name = match prev.name with [name] ++ _ then Some name else None ()
            , properties = prev.properties
            , info = prev.info
            , terms = prev.terms
            }
        }
      , { nt = decl_atom
        , label = "decl_PrecedenceTable"
        -- NOTE(vipa, 2022-03-17): I'm not supporting the except list
        -- here, since I won't use it in the early bootstrapping
        -- process
        , rhs = [litSym "precedence", litSym "{", ntSym decl_PrecedenceTable_1, litSym "}"]
        , action = lam p. lam seq.
          match seq with [LitParsed prec, LitParsed l, UserSym levels, LitParsed r] in
          let levels: {levels : [{noeq : Option {v: (), i: Info}, operators : [{v: Name, i: Info}]}], terms : [Info]} = levels in
          PrecedenceTableDeclOp
            { info = mergeInfo prec.info r.info
            , terms = snoc (concat [prec.info, l.info] levels.terms) r.info
            , levels = levels.levels
            , exceptions = []
            }
        }
      , { nt = decl_PrecedenceTable_1
        , label = "decl_PrecedenceTable_1"
        , rhs = [tokSym (UIdentRepr ()), ntSym decl_PrecedenceTable_2, litSym ";", ntSym decl_PrecedenceTable_1]
        , action = lam p. lam seq.
          match seq with [TokParsed (UIdentTok first), UserSym level, LitParsed semi, UserSym prev] in
          let level: {terms : [Info], operators : [{v: Name, i: Info}]} = level in
          let level = {{level
            with terms = snoc (cons first.info level.terms) semi.info}
            with operators = cons {v = nameNoSym first.val, i = first.info} level.operators} in
          let prev: {terms : [Info], levels : [{noeq : Option {v: (), i: Info}, operators : [{v: Name, i: Info}]}]} = prev in
          let prev = {{prev
            with terms = concat level.terms prev.terms}
            with levels = cons {noeq = None (), operators = level.operators} prev.levels} in
          prev
        }
      , { nt = decl_PrecedenceTable_1
        , label = "decl_PrecedenceTable_2"
        , rhs = []
        , action = lam p. lam seq.
          {terms = [], levels = []}
        }
      , { nt = decl_PrecedenceTable_2
        , label = "decl_PrecedenceTable_3"
        , rhs = [tokSym (UIdentRepr ()), ntSym (decl_PrecedenceTable_2)]
        , action = lam p. lam seq.
          match seq with [TokParsed (UIdentTok name), UserSym prev] in
          let prev: {terms : [Info], operators : [{v: Name, i: Info}]} = prev in
          let prev = {{prev
            with terms = cons name.info prev.terms}
            with operators = cons {v = nameNoSym name.val, i = name.info} prev.operators} in
          prev
        }
      , { nt = decl_PrecedenceTable_2
        , label = "decl_PrecedenceTable_4"
        , rhs = []
        , action = lam p. lam seq.
          {terms = [], operators = []}
        }

      , { nt = regex_top
        , label = "Regex_Top"
        , rhs = [ntSym regex_lclosed]
        , action = lam. lam seq.
          match seq with [UserSym cont] in
          cont (brState ())
        }
      , { nt = regex_lclosed
        , label = "Regex_LClosed_Atom"
        , rhs = [ntSym regex_atom, ntSym regex_lopen]
        , action = lam p. lam seq.
          match seq with [UserSym atom, UserSym cont] in
          lam st. cont (brRegex.atom p atom st)
        }
      , { nt = regex_lclosed
        , label = "Regex_LClosed_Prefix"
        , rhs = [ntSym regex_prefix, ntSym regex_lclosed]
        , action = lam p. lam seq.
          match seq with [UserSym prefix, UserSym cont] in
          lam st. cont (brRegex.prefix p prefix st)
        }
      , { nt = regex_lopen
        , label = "Regex_LOpen_Infix"
        , rhs = [ntSym regex_infix, ntSym regex_lclosed]
        , action = lam p. lam seq.
          match seq with [UserSym infix, UserSym cont] in
          lam st. cont (brRegex.infix p infix st)
        }
      , { nt = regex_lopen
        , label = "Regex_LOpen_Postfix"
        , rhs = [ntSym regex_postfix, ntSym regex_lopen]
        , action = lam p. lam seq.
          match seq with [UserSym postfix, UserSym cont] in
          lam st. cont (brRegex.postfix p postfix st)
        }
      , { nt = regex_lopen
        , label = "Regex_End"
        , rhs = []
        , action = lam p. lam.
          brRegex.finalize p
        }

      , { nt = regex_atom
        , label = "Regex_Grouping"
        , rhs = [litSym "(", ntSym regex_top, litSym ")"]
        , action = lam p. lam seq.
          match seq with [LitParsed l, UserSym (_, inner), LitParsed r] in
          GroupingRegexOp { inner = inner, info = mergeInfo l.info r.info, terms = [l.info, r.info] }
        }
      , { nt = regex_atom
        , label = "Regex_Record"
        , rhs = [litSym "{", ntSym regex_top, litSym "}"]
        , action = lam p. lam seq.
          match seq with [LitParsed l, UserSym (_, regex), LitParsed r] in
          RecordRegexOp { regex = regex, info = mergeInfo l.info r.info, terms = [l.info, r.info] }
        }
      , { nt = regex_atom
        , label = "Regex_Empty"
        , rhs = [litSym "empty"]
        , action = lam. lam seq.
          match seq with [LitParsed x] in
          EmptyRegexOp {info = x.info, terms = [x.info]}
        }
      , { nt = regex_atom
        , label = "Regex_Literal"
        , rhs = [TokSpec (StringRepr ())]
        , action = lam. lam seq.
          match seq with [TokParsed (StringTok x)] in
          LiteralRegexOp {info = x.info, val = x.val, terms = [x.info]}
        }
      , { nt = regex_atom
        , label = "Regex_Token"
        , rhs = [TokSpec (UIdentRepr ()), ntSym regex_Token_1]
        , action = lam p. lam seq.
          match seq with [TokParsed (UIdentTok x), UserSym prev] in
          let prev: {info : Info, terms : [Info], name : [{v: Name, i: Info}], arg : [Expr]} = prev in
          let prev = {{{prev with info = mergeInfo x.info prev.info} with terms = cons x.info prev.terms} with name = cons {v = nameNoSym x.val, i = x.info} prev.name} in
          TokenRegexOp
            { info = prev.info
            , terms = prev.terms
            , name = match prev.name with [name] ++ _ in name
            , arg = match prev.arg with [arg] ++ _ then Some arg else None ()
            }
        }
      , { nt = regex_Token_1
        , label = "Regex_Token_1_1"
        , rhs = []
        , action = lam p. lam.
          { info = NoInfo (), terms = [], name = [], arg = [] }
        }
      , { nt = regex_Token_1
        , label = "Regex_Token_1_2"
        , rhs = [litSym "[", ntSym expr_top, litSym "]"]
        , action = lam p. lam seq.
          match seq with [LitParsed l, UserSym (_, expr), LitParsed r] in
          { info = mergeInfo l.info r.info, terms = [l.info, r.info], name = [], arg = [expr] }
        }
      , { nt = regex_postfix
        , label = "Regex_RepeatPlus"
        , rhs = [litSym "+"]
        , action = lam p. lam seq.
          match seq with [LitParsed x] in
          RepeatPlusRegexOp { info = x.info, terms = [x.info] }
        }
      , { nt = regex_postfix
        , label = "Regex_RepeatStar"
        , rhs = [litSym "*"]
        , action = lam p. lam seq.
          match seq with [LitParsed x] in
          RepeatStarRegexOp { info = x.info, terms = [x.info] }
        }
      , { nt = regex_postfix
        , label = "Regex_RepeatQuestion"
        , rhs = [litSym "?"]
        , action = lam p. lam seq.
          match seq with [LitParsed x] in
          RepeatQuestionRegexOp { info = x.info, terms = [x.info] }
        }
      , { nt = regex_prefix
        , label = "Regex_Named"
        , rhs = [TokSpec (LIdentRepr ()), litSym ":"]
        , action = lam p. lam seq.
          match seq with [TokParsed (LIdentTok name), LitParsed x] in
          NamedRegexOp { name = {v = name.val, i = name.info}, info = mergeInfo name.info x.info, terms = [name.info, x.info] }
        }
      , { nt = regex_infix
        , label = "Regex_Alternative"
        , rhs = [litSym "|"]
        , action = lam p. lam seq.
          match seq with [LitParsed x] in
          AlternativeRegexOp { info = x.info, terms = [x.info] }
        }
      , { nt = regex_infix
        , label = "Regex_Concat"
        , rhs = []
        , action = lam p. lam seq.
          ConcatRegexOp { info = NoInfo (), terms = [] }
        }
      ]
    } in
  switch genParsingTable grammar
  case Right table then table
  case Left err then dprintLn err; never
  end

let parseSelfhost
  : String -> String -> Either [(Info, String)] File
  = lam filename. lam content.
    use ParseSelfhost in
    let config = {errors = ref [], content = content} in
    let res = parseWithTable _table filename config content in
    let errors = deref config.errors in
    let errors =
      match res with Left err then
        let err = ll1DefaultHighlight content (ll1ToErrorHighlightSpec err) in
        snoc errors err
      else errors in
    if null errors then eitherMapRight (lam x. match x with (_, x) in x) res else Left errors

let parseSelfhostExn
  : String -> String -> File
  = lam filename. lam content.
    switch parseSelfhost filename content
    case Left errors then
      for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
      exit 1
    case Right file then file
    end

mexpr

let filename = "blub" in
let content = join
  [ "prod X: Y = A B | C*\n"
  , "prod Z: Stuff = { empty } \n"
  , "type Expr\n"
  , "precedence { X Y; A; } \n"
  ] in

-- dprintLn (parseSelfhostExn filename content);
()
