include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang OCamlAst = FunAst + LetAst + RecLetsAst + ArithIntAst + ArithFloatAst
                + BoolAst + CmpIntAst + CmpFloatAst + CharAst
end

mexpr
()
