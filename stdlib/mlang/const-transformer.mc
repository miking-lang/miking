include "ast.mc"

include "string.mc"
include "name.mc"
include "map.mc"
include "option.mc"

include "mexpr/const-transformer.mc"

lang MLangConstTransformer = MLangAst + ConstTransformer 
  sem constTransformProgram : [(String, Const)] -> MLangProgram -> MLangProgram
  sem constTransformProgram builtins =
  | prog ->
    {decls = map (constTransformDecl builtins) prog.decls,
     expr = constTransform builtins prog.expr}

  sem constTransformDecl : [(String, Const)] -> Decl -> Decl
  sem constTransformDecl builtins = 
  | DeclLang d -> 
    DeclLang {d with decls = map (constTransformDecl builtins) d.decls}
  | DeclSem d ->
    let transformCase = lam c. {c with thn = constTransform builtins c.thn} in
    DeclSem {d with cases = map transformCase d.cases}
  | DeclLet d -> 
    DeclLet {d with body = constTransform builtins d.body}
  | DeclRecLets d ->
    let transformBinding = lam b. 
      {b with body = constTransform builtins b.body} in 
    DeclRecLets {d with bindings = map transformBinding d.bindings}
  | DeclUtest d ->
    DeclUtest {d with test = constTransform builtins d.test,
                      expected = constTransform builtins d.test,
                      tusing = optionMap (constTransform builtins) d.tusing}
  | d -> d
  
end

mexpr

()