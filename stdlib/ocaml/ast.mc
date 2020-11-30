include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang OCamlMatch
  syn Expr =
  | OTmMatch
    { target : Expr
    , arms : [(Pat, Expr)]
    }

  syn Pat =
end

lang OCamlAst = FunAst + LetAst + RecLetsAst + ArithIntAst
                + ArithFloatAst + BoolAst + CmpIntAst + CmpFloatAst
                + CharAst + OCamlMatch + NamedPat + IntPat + CharPat
                + BoolPat
end

mexpr
()
