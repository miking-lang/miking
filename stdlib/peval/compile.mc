include "peval/ast.mc"
include "peval/lift.mc"
include "peval/extract.mc"
include "peval/include.mc"

include "map.mc"
include "name.mc"
include "list.mc" -- listToSeq
include "seq.mc"
include "error.mc"
include "set.mc"

include "mexpr/ast.mc"
include "mexpr/type-annot.mc"
include "mexpr/boot-parser.mc"


lang SpecializeCompile = SpecializeAst + MExprPEval + ClosAst + MExprAst
                    + SpecializeInclude + SpecializeLiftMExpr

  -- Creates a library of the expressions that the element of specialization depends on
  sem createLib (lib : Map Name Expr) (pevalIds : Map Name SpecializeData) =
  | TmLet t ->
    let lib2 = match mapLookup t.ident pevalIds with Some _ then lib
               else mapInsert t.ident t.body lib in
    createLib lib2 pevalIds t.inexpr
  | TmRecLets t ->
    foldl (lam lib. lam rl. mapInsert rl.ident rl.body lib) lib (t.bindings)
  | t -> lib

  sem insertToLib : Map Name Expr -> Name -> Expr -> Map Name Expr
  sem insertToLib lib name =
  | TmLam t & lm -> mapInsert name lm lib
  | _ -> lib

  sem pevalPass : SpecializeNames -> Map Name Expr -> Expr -> Expr
  sem pevalPass pnames lib =
  -- TODO recLet
  | TmLet ({ident=id, body=body, inexpr=inexpr, ty=ty, info=info} & t) ->
    let b = pevalPass pnames lib body in
    let lib = insertToLib lib id b in
    let inx = pevalPass pnames lib inexpr in
    TmLet {t with body=b,
                  inexpr=inx}
  | TmRecLets ({bindings=bindings, inexpr=inexpr, ty=ty, info=info} & t) ->
    let bindings = map (lam rl:RecLetBinding.
                    {rl with body=pevalPass pnames lib rl.body}) bindings in
    let lib = foldl (lam lib. lam rl.
                    mapInsert rl.ident rl.body lib) lib bindings in
    let inx = pevalPass pnames lib inexpr in
    TmRecLets {t with inexpr=inx, bindings=bindings}
  | TmSpecialize {e=e, info=info} & pe ->
    let arg = liftExpr pnames lib false e in
    let liftedEnv = getLiftedEnv pnames lib [] e in
    let lhs = nvar_ (pevalName pnames) in
    let f = appf2_ lhs liftedEnv arg in
    let p = nvar_ (mexprStringName pnames) in
    let ff = app_ p f in
    let fff = print_ ff in
    semi_ fff never_
  | t -> smap_Expr_Expr (pevalPass pnames lib) t

  sem compileSpecialize =
  | origAst ->
    -- TODO(adamssonj, 2023-03-22): For now just always include
    match includeSpecialize origAst with (ast, pevalNames) in
    match includeConstructors ast with ast in
    -- Find the names of the functions and constructors needed later
    let names = createNames ast pevalNames in
    let ast = pevalPass names (mapEmpty nameCmp) ast in
    --let ast = typeCheck ast in -- TODO: temporary fix
    --printLn (mexprToString ast);
    ast
end


lang TestLang = SpecializeCompile + MExprEq + MExprSym + MExprTypeCheck
                + MExprPrettyPrint + MExprTypeAnnot
end

mexpr
use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in


--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  specialize_ (app_ (var_ "f") (int_ 1))
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
--  ulam_ "x" (bindall_ [
--    ulet_ "k" (addi_ (var_ "x") (var_ "x")),
--    ulet_ "q" (specialize_ (var_ "k")),
--    var_ "k"
--    ])
--]) in
--
--let distinctCalls = preprocess (bindall_ [
--    ulet_ "f" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
--    ulet_ "p" (ulam_ "x" (specialize_ (app_ (var_ "f") (var_ "x")))),
--    app_ (var_ "p") (int_ 4)
--]) in


let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" tyint_ (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (int_ 4)),
    unit_
]) in

let intseq = tyseq_ tyint_ in

let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" intseq (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (seq_ [int_ 1, int_ 2])),
    unit_
]) in

let t = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in

let distinctCalls = preprocess (bindall_ [
    ulet_ "p" (lam_ "x" t (specialize_ (var_ "x"))),
    ulet_ "k" (app_ (var_ "p") (urecord_ [("a",int_ 1), ("b", float_ 1.0)]))
]) in

let distinctCalls = preprocess (bindall_ [
  ulet_ "bar" (ulam_ "x" (ulam_ "y" (subi_ (var_ "x") (var_ "y")))),
--  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (appf2_ (var_ "bar") (var_ "x") (var_ "y")) 
--    (var_ "y")))),
  specialize_ (app_ (var_ "bar") (int_ 1))
]) in

match compileSpecialize distinctCalls with ast in

let ast = typeAnnot ast in

()
