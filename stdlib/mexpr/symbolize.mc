-- Symbolization of the MExpr ast.

include "name.mc"
include "string.mc"
include "assoc.mc"

include "mexpr/ast.mc"

---------------------------
-- SYMBOLIZE ENVIRONMENT --
---------------------------
-- TODO The environment differs from boot, since we do not have access to the
-- unique string identifiers from ustring.ml. Instead, we use strings directly.

type Ident
con IdVar   : String -> Ident
con IdCon   : String -> Ident
con IdType  : String -> Ident
con IdLabel : String -> Ident
let identEq : Ident -> Ident -> Bool =
  lam i1. i2. match (i1,i2) with
      IdVar   s1, IdVar   s2
    | IdCon   s1, IdCon   s2
    | IdType  s1, IdType  s2
    | IdLabel s1, IdLabel s2
    then eqstr s1 s2
    else false

type Env = AssocMapIdentSymbol -- i.e., [(Ident, Symbol)]

let lookup : Ident -> Env -> OptionSymbol = assocLookup {eq = identEq}
let insert : Ident -> Env -> OptionSymbol = assocInsert {eq = identEq}

-----------
-- TERMS --
-----------

lang VarSym
  sem symbolize (env : Env) =
  | TmVar {ident = (str, _)} ->
    match findsym (IdVar str) env
    with Some sym then TmVar {ident = (str, sym)}
    else error (concat "Unknown variable in symbolize: " str)
end

lang AppSym
  syn Expr =
  | TmApp {lhs : Expr,
           rhs : Expr}
end

lang FunSym
  sem symbolize (env : Env) =
  | TmLam {ident = (str, _), tpe = tpe, body = body} ->
    let s = gensym () in
    let env = insert env str s in
    TmLam {ident = (str,s), tpe = tpe, body = symbolize env body}
end

lang RecordSym
  syn Expr =
  | TmRecord {bindings : AssocMap} -- AssocMap String Expr
  | TmRecordUpdate {rec   : Expr,
                    key   : String,
                    value : Expr}
end

lang LetSym
  syn Expr =
  | TmLet {ident  : Name,
           tpe    : Option,
           body   : Expr,
           inexpr : Expr}
end

lang RecLetsSym
  syn Expr =
  | TmRecLets {bindings : [{ident : Name,
                            tpe   : Option,
                            body  : Expr}],
               inexpr   : Expr}
end

lang ConstSym
  syn Const =

  syn Expr =
  | TmConst {val : Const}
end

lang DataSym
  syn Expr =
  | TmConDef {ident  : Name,
              tpe    : Option,
              inexpr : Expr}
  | TmConApp {ident : Name,
              body : Expr}
end

lang MatchSym
  syn Expr =
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr}

  syn Pat =
end

lang UtestSym
  syn Expr =
  | TmUtest {test     : Expr,
             expected : Expr,
             next     : Expr}
end

lang SeqSym
  syn Expr =
  | TmSeq {tms : [Expr]}
end

lang NeverSym
  syn Expr =
  | TmNever {}
end

