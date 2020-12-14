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
  | OPatCon { ident : Name, args : [Pat] }
end

lang OCamlAst = LamAst + LetAst + RecLetsAst + ArithIntAst + ShiftIntAst
                + ArithFloatAst + BoolAst + CmpIntAst + CmpFloatAst
                + CharAst + CmpCharAst + OCamlMatch + NamedPat + IntPat
                + CharPat + BoolPat + OCamlTuple + OCamlData
                + IntCharConversionAst + FloatIntConversionAst
                + FileOpAst + RandomNumberGeneratorAst + TimeAst
                + FloatStringConversionAst + SeqOpAst + IOAst + SysAst + SymbAst
                + CmpSymbAst
end

mexpr
()
