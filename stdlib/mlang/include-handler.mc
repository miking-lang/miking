include "ast.mc"
include "boot-parser.mc"
include "pprint.mc"

include "error.mc"
include "stdlib.mc"
include "set.mc"
include "fileutils.mc"
include "sys.mc"

lang MLangIncludeHandler = MLangAst + BootParserMLang
  sem parseAndHandleIncludes : String -> MLangProgram
  sem parseAndHandleIncludes =| path -> 
    let dir = filepathConcat (sysGetCwd ()) (eraseFile path) in 
    let libs = addCWDtoLibs (parseMCoreLibsEnv ()) in
    let included = ref (setEmpty cmpString) in 
    handleIncludesFile included dir libs path

  sem handleIncludesProgram : Ref (Set String) -> String -> Map String String -> MLangProgram -> MLangProgram 
  sem handleIncludesProgram included dir libs =| prog ->
    let f = lam decls. lam decl. 
      concat decls (flattenIncludes included dir libs decl) in 
    {prog with decls = foldl f [] prog.decls}

  sem handleIncludesFile : Ref (Set String) -> String -> Map String String -> String -> MLangProgram
  sem handleIncludesFile included dir libs =| path ->
    let s = deref included in 

    if setMem path s then 
      {decls = [], expr = uunit_}
    else 
      match _consume (parseMLangFile path) with (_, errOrProg) in
      switch errOrProg
        case Left err then error (join [
          "File '",
          path,
          "' could not be parsed!"
        ])
        case Right prog then 
          modref included (setInsert path s);
          handleIncludesProgram included dir libs prog
      end

  sem flattenIncludes : Ref (Set String) -> String -> Map String String -> Decl -> [Decl]
  sem flattenIncludes included dir libs =
  | DeclInclude {path = path, info = info} ->
    let path = findPath dir libs info path in 
    let prog = handleIncludesFile included (eraseFile path) libs path in 
    prog.decls
  | other -> [other]

  sem findPath : String -> Map String String -> Info -> String -> String
  sem findPath dir libs info =| path ->
    let libs = mapInsert "current" dir libs in 
    let prefixes = mapValues libs in 
    let paths = map (lam prefix. filepathConcat prefix path) prefixes in 

    let existingFiles = filter sysFileExists paths in 
    let existingFilesAsSet = setOfSeq cmpString existingFiles in 

    switch (setSize existingFilesAsSet)
      case 0 then 
        errorSingle [info] "File not found!"
      case 1 then 
        head (setToSeq existingFilesAsSet)
      case _ then 
        warnSingle [info] "Multiple files found" ;
        head (setToSeq existingFilesAsSet)
    end
end

mexpr
use MLangPrettyPrint in 
use MLangIncludeHandler in 

let dir = sysGetCwd () in 
let libs = addCWDtoLibs (parseMCoreLibsEnv ()) in
let included = ref (setEmpty cmpString) in 

let p = handleIncludesFile included "stdlib/mexpr" libs "stdlib/mexpr/ast.mc" in 

printLn (mlang2str (p));
()