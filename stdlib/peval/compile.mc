include "peval/ast.mc"
include "peval/lift.mc"
include "peval/extract.mc"
include "peval/include.mc"

include "map.mc"
include "name.mc"
include "list.mc" -- listToSeq
include "seq.mc"
include "error.mc"

include "mexpr/ast.mc"
include "mexpr/lamlift.mc"


lang SpecializeCompile = SpecializeAst + MExprPEval + SpecializeExtract + MExprLambdaLift + 
                    ClosAst + MExprAst + SpecializeInclude + SpecializeLiftMExpr

  -- Creates a library of the expressions that the element of specialization depends on
  sem createLib (lib : Map Name Expr) (pevalIds : Map Name SpecializeData) = 
  | TmLet t -> 
    let lib2 = match mapLookup t.ident pevalIds with Some _ then lib 
               else mapInsert t.ident t.body lib in
    createLib lib2 pevalIds t.inexpr
  | TmRecLets t -> 
    foldl (lam lib. lam rl. mapInsert rl.ident rl.body lib) lib (t.bindings)
  | t -> lib

  sem compileSpecialize =
  | origAst -> 
    match addIdentifierToSpecializeTerms origAst with (pevalData, ast) in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    let pevalIds = mapMap (lam. ()) pevalData in
    let pevalAst = extractAccelerateTerms pevalIds ast in

    match eliminateDummyParameter solutions pevalData pevalAst
    with (pevalData, pevalAst) in

    let lib = createLib (mapEmpty nameCmp) pevalData pevalAst in

    match includeSpecialize origAst with (ast, pevalNames) in 
    match includeConstructors ast with ast in

    -- Find the names of the functions and constructors needed later
    let names = createNames ast pevalNames in

    let ast = expandSpecialize names lib origAst in

    printLn (mexprToString ast);
    ast

end 


lang TestLang = SpecializeCompile + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint
end


mexpr 
use TestLang in


let preprocess = lam t.
  typeCheck (symbolize t)
in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  ulet_ "g" (ulam_ "y" (ulam_ "x" (addf_ (var_ "x") (var_ "y")))),
--  ulet_ "p" (specialize_ (app_ (var_ "g") (float_ 0.0))),
  specialize_ (app_ (var_ "f") (int_ 1))
]) in


match compileSpecialize distinctCalls with ast in

() 
