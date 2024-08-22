-- This transformation converts the `Name`s of semantic functions to `Name`s 
-- with the same symbol, but also have a unique string in the shape of 
-- <LangName>_<SemName>. 
-- 
-- This transformation is added because some parts of the exising MExpr
-- transformations to OCaml do not respect the symbols fully and also require
-- the strings of names to be unique. 

include "name.mc"
include "map.mc"
include "tuple.mc"
include "option.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

let foobla : Map (String, String) Name -> (Name -> Name) = lam m.
  let pairs : [((String, String), Name)] = mapToSeq m in 
  let reversedPairs = map (lam p. (p.1, p.0)) pairs in 
  let reversedMap = mapFromSeq nameCmp reversedPairs in 

  lam n.
    match mapLookup n reversedMap with Some ((origLang, semName)) then 
      nameSetStr n (join [origLang, "_", semName])
    else 
      n

lang PostProcess = MExprAst 
  sem postprocess : Map (String, String) Name -> Expr -> Expr
  sem postprocess m =| e ->
    let sub = foobla m in 
    worker sub e

  sem worker : (Name -> Name) -> Expr -> Expr
  sem worker sub = 
  | TmVar t -> TmVar {t with ident = sub t.ident}
  | TmLet t -> TmLet {t with ident = sub t.ident,
                             inexpr = worker sub t.inexpr}
  | TmRecLets t -> 
    let work = lam binding. 
      {binding with ident = sub binding.ident,
                    body = worker sub binding.body}
    in
    TmRecLets {t with bindings = map work t.bindings,
                      inexpr = worker sub t.inexpr}
  | other -> smap_Expr_Expr (worker sub) other
end

mexpr
use PostProcess in 
use MExprPrettyPrint in
let sym = nameSym "f" in 
let m = mapEmpty (tupleCmp2 cmpString cmpString) in 
let m = mapInsert ("LangName", "f") sym m in 

let e = nvar_ sym in 
let e = postprocess m e in 
match e with TmVar {ident = ident} in 
utest nameHasSym ident with true in 
()