include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "mexpr/boot-parser.mc"

include "name.mc"
include "seq.mc"
include "result.mc"

lang BootParserMLang = BootParser + MLangAst
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

    let unparsedExpr = bootParserGetTerm p 0 in 

    {decls = includes,
     expr = matchTerm unparsedExpr (bootParserGetId unparsedExpr)}

end

mexpr
use BootParserMLang in 
use MLangPrettyPrint in 

let parseProgram = lam str.
  match _consume (parseMLangString str) with (_, Right p) in p
in

let getIncludeStrings : MLangProgram -> [String] = lam p.
  let decls = p.decls in 
  mapOption 
    (lam d. match d with DeclInclude r then Some r.path else None ()) 
    decls
in

let str = "include \"foo.mc\"\ninclude \"bar.mc\"\ninclude \"baz.mc\"\ninclude \"bar.mc\"\nlet x = 10\nmexpr\nx" in
let p = parseProgram str in

-- Test includes are parsed
utest getIncludeStrings p with ["foo.mc", "bar.mc", "baz.mc", "bar.mc"] using eqSeq eqString in

-- Test expression is parsed
utest match p.expr with TmVar {ident = ident} in ident with nameNoSym "x" using nameEqStr in 

-- printLn "before!" ;
-- let t = bootParserParseMLangString str in 
-- printLn (int2string (bootParserGetId t)) ;
-- let len = bootParserGetListLength t 0 in
-- printLn (int2string (len)) ;
-- let len = bootParserGetListLength t 1 in
-- printLn (int2string (len)) ;

-- printLn (bootParserGetString t 0) ;
-- printLn (bootParserGetString t 1) ;
-- printLn "after!" ;

-- utest 1 with 1 in 

()