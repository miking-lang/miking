include "ast.mc"
include "boot-parser.mc"

-- OPT(voorberg, 06/05/2024): This naively copy includes into the 
-- MLang program, even if they have already been included. There 
-- is obviously a lot of potential for improvement here.
lang MLangIncludeHandler = MLangAst + BootParserMLang
  sem handleIncludesProgram : MLangProgram -> MLangProgram 
  sem handleIncludesProgram =| prog ->
    let f = lam decls. lam decl. 
      concat decls (flattenIncludes decl) in 
    {prog with decls = foldl f [] prog.decls}

  sem handleIncludesFile : String -> MLangProgram
  sem handleIncludesFile =| path ->
    match _consume (parseMLangFile path) with (_, errOrProg) in
    switch errOrProg
      case Left err then error (join [
        "File '",
        path,
        "' could not be parsed!"
      ])
      case Right prog then 
        handleIncludesProgram prog
    end

  sem flattenIncludes : Decl -> [Decl]
  sem flattenIncludes =
  | DeclInclude {path = path} ->
    match _consume (parseMLangFile path) with (_, errOrProg) in
    switch errOrProg 
      case Left err then error (join [
        "Include '",
        path,
        "' could not be parsed!"
      ])
      case Right prog then prog.decls
    end
  | other -> [other]
end