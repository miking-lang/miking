-- This language fragment BootParserMLang allows you to parse
-- files or strings into MLang programs.
--
-- The parsing is done by calling the instrinsic functions
-- `bootParserParseMLangFile` and `bootParserMlangString` whose functionality
-- is provided in boot. The result of a call to these intrinsics is the
-- opaque type CBootParserTree. We use various intrinsics, such as
-- `bootParserGetDecl` or `bootParserGetInt`, to inspect terms of this type.
--
-- BootParserMLang is built on top of the boot parser defined in
-- `stdlib/mexpr/boot-parser.mc`.

include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "compile.mc"

include "mexpr/eval.mc"
include "mexpr/boot-parser.mc"

include "name.mc"
include "seq.mc"
include "option.mc"
include "result.mc"

lang BootParserMLang = BootParser + MLangAst
  sem parseMLangFile : all a. String -> Result a (Info, String) MLangProgram
  sem parseMLangFile =| filepath ->
    let p = bootParserParseMLangFile filepath in
    if eqi (bootParserGetId p) 600 /- Error -/ then
      let n = glistlen p 0 in
      let infos = create n (lam i. ginfo p i) in
      let msgs = create n (lam i. gstr p i) in
      foldl1 result.withAnnotations (zipWith (curry result.err) infos msgs)
    else
      result.ok (matchProgram p (bootParserGetId p))

  sem parseMLangString : all a. String -> Result a (Info, String) MLangProgram
  sem parseMLangString =| str ->
    let p = bootParserParseMLangString str in
    if eqi (bootParserGetId p) 600 /- Error -/ then
      let n = glistlen p 0 in
      let infos = create n (lam i. ginfo p i) in
      let msgs = create n (lam i. gstr p i) in
      foldl1 result.withAnnotations (zipWith (curry result.err) infos msgs)
    else
      result.ok (matchProgram p (bootParserGetId p))

  sem matchProgram : Unknown -> Int -> MLangProgram
  sem matchProgram p =
  | 700 ->
    let nIncludes = bootParserGetListLength p 0 in
    let nTops = bootParserGetListLength p 1 in

    let parseInclude = lam i.
      let inf = bootParserGetInfo p i in
      DeclInclude {path = bootParserGetString p i,
                   info = matchInfo inf (bootParserGetId inf)}
    in
    let includes = map parseInclude (range 0 nIncludes 1) in

    let parseDecl = lam i.
      let d = bootParserGetTop p i in
      matchTop d (bootParserGetId d)
    in
    let decls = map parseDecl (range 0 nTops 1) in

    let unparsedExpr = bootParserGetTerm p 0 in

    {decls = concat includes decls,
     expr = matchTerm unparsedExpr (bootParserGetId unparsedExpr)}

  -- Semantic function declaration can be split into a type annotation and args
  -- + cases. This function merges sems into a single declaration.
  sem mergeSems : [Decl] -> [Decl]
  sem mergeSems =| decls ->
    let work = lam acc : ([Decl], Map String Decl). lam decl : Decl.
      match acc with (res, m) in
      match decl with DeclSem s1 then
        let str = nameGetStr s1.ident in
        match mapLookup str m with Some (DeclSem s2) then
          match s1.tyAnnot with TyUnknown _ then
            let m = mapRemove str m in
            (res, mapInsert str (DeclSem {s1 with tyAnnot = s2.tyAnnot}) m)
          else
            let m = mapRemove str m in
            (res, mapInsert str (DeclSem {s1 with args = s2.args, cases = s2.cases}) m)
        else
          (res, mapInsert str decl m)
      else
        (cons decl res, m)
    in
    match foldl work ([], mapEmpty cmpString) decls with (res, m) in
    concat res (mapValues m)


  sem matchDecl : Unknown -> Int -> Decl
  sem matchDecl d =
  | 702 ->
    let nCons = glistlen d 0 in
    let nParams = if eqi nCons 0 then 0 else glistlen d 1 in

    let parseCon = lam i.
      let ident = gname d (addi i 1) in
      let ty = gtype d i in
      {ident = ident, tyIdent = ty}
    in

    DeclSyn {ident = gname d 0,
             includes = [],
             defs = map parseCon (range 0 nCons 1),
             params = map (lam i. gname d (addi (addi 1 nCons) i)) (range 0 nParams 1),
             info = ginfo d 0}
  | 703 ->
    let nCases = glistlen d 0 in
    let nArgs = glistlen d 1 in
    let parseCase = lam i.
      {pat = gpat d i, thn = gterm d i}
    in
    let parseArg = (lam i. {ident = gname d i, tyAnnot = gtype d i}) in

    let args = if eqi nArgs -1 then
      None ()
    else
      Some (map (lam i. {ident = gname d i, tyAnnot = gtype d i}) (range 1 (addi 1 nArgs) 1))
    in

    DeclSem {ident = gname d 0,
             tyAnnot = gtype d 0,
             tyBody = tyunknown_,
             args = args,
             cases = map parseCase (range 0 nCases 1),
             includes = [],
             info = ginfo d 0}
  | 705 ->
    DeclType {ident = gname d 0,
              params = map (gname d) (range 1 (addi 1 (glistlen d 0)) 1),
              tyIdent = gtype d 0,
              info = ginfo d 0}

  sem matchTop : Unknown -> Int -> Decl
  sem matchTop d =
  | 701 ->
    let nIncludes = glistlen d 0 in
    let nDecls = glistlen d 1 in

    let includes = map (gname d) (range 1 (addi nIncludes 1) 1) in

    let parseDecl = lam i.
      let a = bootParserGetDecl d i in
      matchDecl a (bootParserGetId a)
    in

    let decls = map parseDecl (range 0 nDecls 1) in
    let decls = reverse (mergeSems decls) in


    DeclLang {ident = gname d 0,
              info = ginfo d 0,
              includes = includes,
              decls = decls}
  | 704 ->
    DeclLet {ident = gname d 0,
             tyAnnot = gtype d 0,
             tyBody = tyunknown_,
             body = gterm d 0,
             info = ginfo d 0}
  | 705 /-TmType-/ ->
    DeclType {ident = gname d 0,
              params = map (gname d) (range 1 (addi 1 (glistlen d 0)) 1),
              tyIdent = gtype d 0,
              info = ginfo d 0}
  | 706 ->
    DeclRecLets {bindings =
                 create (glistlen d 0)
                        (lam n. {ident = gname d n,
                                 tyAnnot = gtype d n,
                                 tyBody = TyUnknown { info = ginfo d (addi n 1)},
                                 body = gterm d n,
                                 info = ginfo d (addi n 1)}),
                 info = ginfo d 0}
  | 707 ->
    DeclConDef {ident = gname d 0,
                tyIdent = gtype d 0,
                info = ginfo d 0}
  | 708 ->
    DeclUtest {test = gterm d 0,
               expected = gterm d 1,
               tusing = if geqi (glistlen d 0) 3 then Some (gterm d 2) else None (),
               tonfail = if geqi (glistlen d 0) 4 then Some (gterm d 3) else None (),
               info = ginfo d 0}
  | 709 ->
    DeclExt {ident = gname d 0,
             tyIdent = gtype d 0,
             effect = neqi (gint d 0) 0,
             info = ginfo d 0}

  sem matchTerm t =
  | 116 ->
    TmUse {info = ginfo t 0,
           inexpr = gterm t 0,
           ty = tyunknown_,
           ident = gname t 0}

  sem matchType t =
  | 214 ->
    TyUse {ident = gname t 0,
           info = ginfo t 0,
           inty = gtype t 0}
end

mexpr
use BootParserMLang in
use MLangPrettyPrint in
use MExprEq in

let parseProgram = lam str.
  match result.consume (parseMLangString str) with (_, Right p) in p
in

let getIncludeStrings : MLangProgram -> [String] = lam p.
  let decls = p.decls in
  mapOption
    (lam d. match d with DeclInclude r then Some r.path else None ())
    decls
in

let str = "include \"foo.mc\"\ninclude \"bar.mc\"\ninclude \"baz.mc\"\ninclude \"bar.mc\"\nlet x = 10\nmexpr\nx" in
let p = parseProgram str in

-- printLn (mlang2str p) ;

-- Test includes are parsed
utest getIncludeStrings p with ["foo.mc", "bar.mc", "baz.mc", "bar.mc"] using eqSeq eqString in

-- Test expression is parsed
utest match p.expr with TmVar {ident = ident} in ident with nameNoSym "x" using nameEqStr in

-- Test TypeDecl
let str = "type Pair = (Int, Char)\nmexpr\n1" in
let p = parseProgram str in
utest match head p.decls with DeclType {ident = ident} in ident with nameNoSym "Pair" using nameEqStr in

-- Test Reclets
let str = strJoin "\n" [
  "recursive",
  "  let isOdd  = lam n. match n with 0 then false else isEven (subi n 1)",
  "  let isEven = lam n. match n with 0 then true  else isOdd  (subi n 1)",
  "end",
  "mexpr",
  "isOdd 43"
] in
let p = parseProgram str in
match head p.decls with DeclRecLets d in
utest map (lam b. nameGetStr b.ident) d.bindings with ["isOdd", "isEven"] using eqSeq eqString in
-- printLn (mlang2str p) ;

-- Test ConDef
let str = strJoin "\n" [
  "type Tree",
  "con Leaf: Int -> Tree",
  "con Node: (Tree, Tree) -> Tree",
  "recursive",
  "  let sum = lam tree.",
  "    match tree with Node (l, r) then",
  "    addi (sum l) (sum r)",
  "    else (match tree with Leaf val in val)",
  "end",
  "mexpr",
  "sum (Node (Leaf 10) (Leaf 20))"
] in
let p = parseProgram str in
-- printLn (mlang2str p);
match head p.decls with DeclType d in
utest d.ident with nameNoSym "Tree" using nameEqStr in
match get p.decls 1 with DeclConDef d in
utest d.ident with nameNoSym "Leaf" using nameEqStr in
match get p.decls 2 with DeclConDef d in
utest d.ident with nameNoSym "Node" using nameEqStr in
-- printLn (mlang2str p) ;

-- Test Utest
let str = strJoin "\n" [
  "utest 10 with addi 7 3",
  "utest 12 with addi 7 3 using neqi",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclUtest d in
utest d.test with int_ 10 using eqExpr in
utest optionIsNone d.tusing with true in
match get p.decls 1 with DeclUtest d in
utest d.test with int_ 12 using eqExpr in
utest optionIsSome d.tusing with true in
-- printLn (mlang2str p) ;

-- Test empty language
let str = strJoin "\n" [
  "lang L1",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "L1" in
utest length d.decls with 0 in
-- printLn (mlang2str p) ;

-- Test language with syn definition
let str = strJoin "\n" [
  "lang IntArith",
  "  syn Expr =",
  "  | IntExpr Int",
  "  | AddExpr (Expr, Expr)",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "IntArith" in
match head d.decls with DeclSyn s in
utest nameGetStr s.ident with "Expr" in
utest nameGetStr (head s.defs).ident with "IntExpr" in
utest nameGetStr (get s.defs 1).ident with "AddExpr" in
-- printLn (mlang2str p) ;

-- Test syn with type parameters
let str = strJoin "\n" [
  "lang AVLTreeImpl",
  "  syn AVL k v =",
  "  | Leaf ()",
  "  | Node {key : k, value : v, l : AVL k v, r : AVL k v, h : Int}",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "AVLTreeImpl" in
match head d.decls with DeclSyn s in
utest nameGetStr s.ident with "AVL" in
utest map nameGetStr s.params with ["k", "v"] using eqSeq eqString in


-- Test syn with type parameters without constructors
let str = strJoin "\n" [
  "lang AVLTreeImpl",
  "  syn AVL k v =",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "AVLTreeImpl" in
match head d.decls with DeclSyn s in
utest nameGetStr s.ident with "AVL" in
-- TODO(voorberg, 08/05/2024): Figure out what the params are supposed to be
-- in this case

-- Test language with semantic function
let str = strJoin "\n" [
  "lang IntArith",
  "  sem f =",
  "  | 0 -> 0",
  "  | _ -> 1",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "IntArith" in
match head d.decls with DeclSem s in
utest nameGetStr s.ident with "f" in
utest (head s.cases).thn with int_ 0 using eqExpr in
utest (get s.cases 1).thn with int_ 1 using eqExpr in
-- printLn (mlang2str p) ;

-- Test language with semantic function
let str = strJoin "\n" [
  "lang Base",
  "  sem f =",
  "end",
  "lang L1 = Base",
  "  sem f =",
  "  | 0 -> 0",
  "end",
  "lang L2 = Base",
  "  sem f =",
  "  | _ -> 1",
  "end",
  "lang L12 = L1 + L2",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match get p.decls 3 with DeclLang d in
utest nameGetStr d.ident with "L12" in
utest d.includes with [nameNoSym "L1", nameNoSym "L2"] using eqSeq nameEqStr in
-- printLn (mlang2str p) ;

-- Test semantic function with multiple args
let str = strJoin "\n" [
  "lang IntArith",
  "  sem f x y =",
  "  | _ -> addi x y",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "IntArith" in
match head d.decls with DeclSem s in
utest nameGetStr s.ident with "f" in
utest optionMap (map (lam a. nameGetStr a.ident)) s.args with Some (["x", "y"]) using optionEq (eqSeq eqString) in
-- printLn (mlang2str p) ;

-- Test semantic function with type params
-- Test semantic function with multiple args
let str = strJoin "\n" [
  "lang IdLang",
  "  sem id : all a. a -> a",
  "  sem id =",
  "  | x -> x",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "IdLang" in
match head d.decls with DeclSem s in
utest nameGetStr s.ident with "id" in
match s.tyAnnot with TyAll tyall in
utest nameGetStr tyall.ident with "a" in
match tyall.ty with TyArrow tyarrow in
match tyarrow.from with TyVar tyvar in
utest nameGetStr tyvar.ident with "a" in
match tyarrow.to with TyVar tyvar in
utest nameGetStr tyvar.ident with "a" in
-- Test type declaratin in langauge
let str = strJoin "\n" [
  "lang MyLang",
  "  type Point = {x : Int, y : Int}",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "MyLang" in
match head d.decls with DeclType s in
utest nameGetStr s.ident with "Point" in
-- printLn (mlang2str p) ;

-- Test type declaration with params
let str = strJoin "\n" [
  "lang MyLang",
  "  type Point a b = {x : Int, y : Int}",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang d in
utest nameGetStr d.ident with "MyLang" in
match head d.decls with DeclType s in
utest nameGetStr s.ident with "Point" in
utest map nameGetStr s.params with ["a", "b"] using eqSeq eqString in

let str = strJoin "\n" [
  "type Point a b = {x : Int, y : Int}",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclType s in
utest nameGetStr s.ident with "Point" in
utest map nameGetStr s.params with ["a", "b"] using eqSeq eqString in

-- Test TmUse parsing
let str = strJoin "\n" [
  "lang L end",
  "mexpr",
  "use L in",
  "()"
] in
let p = parseProgram str in
match p.expr with TmUse u in
utest nameGetStr u.ident with "L" in

-- Test TyUse parsing
let str = strJoin "\n" [
  "lang L",
  "  type Foo = Int",
  "end",
  "type Bar = use L in Foo",
  "mexpr",
  "use L in",
  "()"
] in
let p = parseProgram str in

let str = strJoin "\n" [
  "lang L",
  "  sem f : all a. a -> Int",
  "  sem f a b =| x -> x",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in

let str = strJoin "\n" [
  "lang L",
  "  sem f : Int -> Int",
  "end",
  "mexpr",
  "()"
] in
let p = parseProgram str in
match head p.decls with DeclLang l in
match head l.decls with DeclSem f in
match optionIsNone f.args with true in

()
