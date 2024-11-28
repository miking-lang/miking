include "pprint.mc"
include "ast.mc"

include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"

include "mlang/boot-parser.mc"
include "mlang/pprint.mc"

include "name.mc"
include "ast.mc"
include "ast-builder.mc"

let gcopat = lam tree. lam i. bootParserGetCopat tree i 

lang ExtRecBootParser = BootParserMLang + ExtRecordAst
  sem matchTerm t = 
  | 117 -> 
    let n = glistlen t 0 in 
    let params = map (lam i. gname t (addi i 1)) (range 0 n 1) in 

    TmRecType {ident = gname t 0,
               params = params,
               ty = tyunknown_,
               inexpr = gterm t 0,
               info = ginfo t 0}
  | 118 -> 
    TmRecField {label = gstr t 0,
                tyIdent = gtype t 0,
                inexpr = gterm t 0,
                ty = tyunknown_,
                info = ginfo t 0}
  | 119 ->
    let n = glistlen t 0 in 
    let ident = gname t 0 in 
    let bindingPairs = map (lam i. (gstr t (addi 1 i), gterm t i)) (range 0 n 1) in 
    TmExtRecord {bindings = mapFromSeq cmpString bindingPairs, 
                 ident = ident,
                 ty = tyunknown_, 
                 info = ginfo t 0}
  | 120 -> 
    TmExtProject {e = gterm t 0, 
                  ident = gname t 0,
                  label = gstr t 1, 
                  ty = tyunknown_,
                  info = ginfo t 0}
  | 122 ->
    let n = glistlen t 0 in 
    let ident = gname t 0 in 
    let e = gterm t 0 in 
    let bindingPairs = map (lam i. (gstr t i, gterm t (addi 1 i))) (range 0 n 1) in 
    TmExtExtend {bindings = mapFromSeq cmpString bindingPairs, 
                 e = e,
                 ty = tyunknown_, 
                 info = ginfo t 0}
end

lang RecDeclBootParser = BootParserMLang + RecTypeDeclAst + 
                         RecFieldDeclAst
  sem matchTop d = 
  | 711 ->
    let n = glistlen d 0 in 
    let params = map (lam i. gname d (addi i 1)) (range 0 n 1) in 
    RecTypeDecl {info = ginfo d 0,
                 ident = gname d 0,
                 params = params}
  | 712 ->
    RecFieldDecl {info = ginfo d 0,
                  label = gstr d 0,
                  tyLabel = gtype d 0}
end

lang CosynBootParser = BootParserMLang + CosynDeclAst
  sem matchDecl d =
  | 714 ->
    let n = glistlen d 0 in 
    let isBase = eqi (glistlen d 1) 0 in
    let params = map (lam i. gname d (addi i 1)) (range 0 n 1) in 

    -- Insert implicit parameter
    -- let params = cons (nameNoSym "m") params in 
    DeclCosyn {info = ginfo d 0,
               ident = gname d 0, 
               ty = gtype d 0,
               isBase = isBase,
               params = params,
               includes = []}
end

lang CosemBootParser = BootParserMLang + RecordCopatAst + CosemDeclAst
  sem matchDecl d =
  | 715 ->
    let nArgs = glistlen d 0 in 
    let nCases = glistlen d 1 in 
    let isBase = eqi (glistlen d 2) 0 in 

    let parseArg = lam i.
      let i = addi 1 i in 
      {ident = gname d i, tyAnnot = gtype d i} in 
    let args = map parseArg (range 0 nArgs 1) in 

    let parseCase = lam i. (gcopat d i, gterm d i) in 
    let cases = map parseCase (range 0 nCases 1) in 

    DeclCosem {info = ginfo d 0,
               ident = gname d 0,
               args = args,
               cases = cases,
               isBase = isBase,
               includes = [],
               tyAnnot = gtype d 0,
               targetTyIdent = nameSym ""}

  sem gcopat c =
  | n -> let c2 = bootParserGetCopat c n in
         matchCopat c2 (bootParserGetId c2)

  sem matchCopat c = 
  | 800 -> 
    let n = glistlen c 0 in 
    RecordCopat {info = ginfo c 0,
                 fields = map (gstr c) (range 0 n 1)}
end 

lang MyPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint + DeclCosynPrettyPrint + DeclCosemPrettyPrint
end

lang MyBigBootParserForTesting = ExtRecBootParser + CosynBootParser + CosemBootParser end

mexpr
use MyBigBootParserForTesting in 
use MyPrettyPrint in 
let parseProgram = lam str.
  match result.consume (parseMLangString str) with (_, Right p) in p
in

-- Test syn product extension
let str = strJoin "\n" [
  "mexpr",
  "rectype Foo in",
  "recfield x : Foo -> Int in",
  "let r = {Foo of x = 1} in ",
  "r.x"
] in
let p = parseProgram str in 
printLn (mlang2str p) ;

-- Test syn product extension
let str = strJoin "\n" [
  "lang L1",
  "  cosyn Env a = {x : a}",
  "end",
  "lang L2 = L1",
  "  cosyn Env a *= {y : a}",
  "end"
] in
let p = parseProgram str in 
printLn (mlang2str p) ;

-- Test cosem with type annotation
let str = strJoin "\n" [
  "lang L1",
  "  cosyn Env = {x : Int}",
  "  cosem makeEnv : Int -> Env",
  "  cosem makeEnv param =",
  "  | {x} <- {x = 10}",
  "end"
] in
let p = parseProgram str in
printLn (mlang2str p) ;

let str = strJoin "\n" [
  "lang L0",
  "  sem eval1 : atmost (BaseArith::Expr - Expr::TmIncr) -> Int",
  "  sem eval2 : atmost (BaseArith::Expr + Expr::TmIncr) -> Int",
  "  sem eval3 : atmost (BaseArith::Expr + Expr::TmIncr - Expr::TmIncr) -> Int",
  "end"
] in 
let p = parseProgram str in
printLn (mlang2str p) ;

()