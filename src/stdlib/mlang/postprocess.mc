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
include "mexpr/utils.mc"

lang PostProcess = MExprAst + MExprSubstitute
  sem buildMap : Map (String, String) Name -> Map Name Name
  sem buildMap =
  | m ->
    let pairs = mapToSeq m in
    let pairs = map (lam p. 
      match p with ((langStr, semStr), n) in (n, join [langStr, "_", semStr]))
      pairs in
    let pairs = map (lam p. match p with (n, str) in (n, nameSetStr n str)) pairs in
    mapFromSeq nameCmp pairs


  sem postprocess : Map (String, String) Name -> Expr -> Expr
  sem postprocess m =| e ->
    let m = buildMap m in 
    substituteIdentifiersExpr m e
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