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

lang OCamlTuple
  syn Expr =
  | OTmTuple { values : [Expr] }

  syn Pat =
  | OPTuple { pats : [Pat] }
end

lang OCamlData
  syn Expr =
  | OTmConApp { ident : Name, args : [Expr] }

  syn Pat =
  | OPCon { ident : Name, args : [Pat] }
end

lang OCamlAst = LamAst + LetAst + RecLetsAst + ArithIntAst + ShiftIntAst
                + ArithFloatAst + BoolAst + CmpIntAst + CmpFloatAst
                + CharAst + OCamlMatch + NamedPat + IntPat + CharPat
                + BoolPat + OCamlTuple + OCamlData
                + CharAst + FloatIntConversionAst
end

mexpr
()
