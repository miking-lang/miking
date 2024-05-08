include "ast.mc"
include "boot-parser.mc"
include "pprint.mc"

include "stdlib.mc"
include "fileutils.mc"
include "sys.mc"

-- OPT(voorberg, 06/05/2024): This naively copy includes into the 
-- MLang program, even if they have already been included. There 
-- is obviously a lot of potential for improvement here.
lang MLangIncludeHandler = MLangAst + BootParserMLang
  sem handleIncludesProgram : String -> Map String String -> MLangProgram -> MLangProgram 
  sem handleIncludesProgram dir libs =| prog ->
    let f = lam decls. lam decl. 
      concat decls (flattenIncludes dir libs decl) in 
    {prog with decls = foldl f [] prog.decls}

  sem handleIncludesFile : String -> Map String String -> String -> MLangProgram
  sem handleIncludesFile dir libs =| path ->
    match _consume (parseMLangFile path) with (_, errOrProg) in
    switch errOrProg
      case Left err then error (join [
        "File '",
        path,
        "' could not be parsed!"
      ])
      case Right prog then 
        handleIncludesProgram dir libs prog
    end

  sem flattenIncludes : String -> Map String String -> Decl -> [Decl]
  sem flattenIncludes dir libs =
  | DeclInclude {path = path} ->
    let path = findPath dir libs path in 
    let prog = handleIncludesFile (eraseFile path) libs path in 
    prog.decls
  | other -> [other]

  sem findPath : String -> Map String String -> String -> String
  sem findPath dir libs =| path ->
    let libs = mapInsert "current" dir libs in 
    let prefixes = mapValues libs in 
    let paths = map (lam prefix. filepathConcat prefix path) prefixes in 

    let existingFiles = filter sysFileExists paths in 
    let existingFilesAsSet = setOfSeq cmpString existingFiles in 

    switch (setSize existingFilesAsSet)
      case 0 then 
        printLn path;
        printLn dir;
        error "File not found!"
      case 1 then head (setToSeq existingFilesAsSet)
      case _ then 
        printLn path;
        iter printLn existingFiles;
        printLn dir;
        error "Multiple files were found!"
    end
end

mexpr
use MLangPrettyPrint in 
use MLangIncludeHandler in 

let dir = sysGetCwd () in 
let libs = addCWDtoLibs (parseMCoreLibsEnv ()) in

printLn (mlang2str (handleIncludesFile dir libs "stdlib/seq.mc"))