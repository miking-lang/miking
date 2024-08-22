-- Parse an MLang program and handle insert the included declarations.
--
-- The semantic function `parseAndHandleIncludes` parses a MLang file
-- at a specific filepath using the boot-parser. It then traverses it looks
-- for any `DeclInclude`s in that program. When a `DeclInclude`, we first
-- normalize the filepath. Then based on the normalized file path, one of 
-- two things happen:
-- (1) If this filepath has not yet been included, then we parse the program
--     at this path and replace the DeclInclude with the top-level declarations
--     in the included program. In this case, we also transitively include
--     any files included by the included file in the same way.
-- (2) If this filepath has already been included, then we get rid of it without
--     adding any declarations. 
-- 
-- Note that this is a rather crude way of handling includes that can lead
-- undesirable behavior in which the order of includes can cause significant
-- changes to the behaviour of the program. 
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
      match result.consume (parseMLangFile path) with (_, errOrProg) in
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
        -- TODO(voorberg, 09/05/2024): This happens because we dont properly
        -- deal with libraries yet. The code does not yet realise that 
        -- some absolute path is equal to some relative path.
        warnSingle [info] "Multiple files found" ;
        head (setToSeq existingFilesAsSet)
    end
end