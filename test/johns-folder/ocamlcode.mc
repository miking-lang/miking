-- OCaml code generator

-- Has: 
-- let int2string = lam i. ... in
-- recursive let factorial = lam n.
--     if eqi n 0 then 1 else factorial (subi n 1)
-- in
-- print (int2string (factorial 5))
--
--
-- Want:
-- open Printf
-- let int2string i = ...
-- in
-- let rec factorial n = if n == 0 then 1 else factorial (n - 1) in
-- printf (int2string (factorial 5))
--
-- What needs to happen:
--  The lambdas need to appear on the left side of the equals sign

include "ast.mc"
include "string.mc"

let spacing = lam indent. makeseq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

let incr = lam indent. addi incr 4 in



"nth <lista> <pos>"

"List.nth <pos> <list>"





lang VarOCamlCode = VarAst
    sem ocamlcodegen (indent : Int) =
    | TmVar x -> x
end

lang AppOCamlCode = AppAst
    sem ocamlcodegen (indent : Int) =
    | TmApp t ->
      let lhs = t.0 in
      let rhs = t.1 in
      strJoin "" [ocamlcodegen indent lhs, " ", "(", ocamlcodegen indent rhs, ")"]
end

lang FunOCamlCode = FunAst
    sem ocamlcodegen (indent : Int) =
    | TmLam t -> let _ = dprint t in error "Encountered an isolated lambda"
end

lang LetOCamlCode = LetAst
    sem ocamlcodegen (indent : Int) =
    | TmLet t ->
      -- Find all the chained lambdas
      --   acc.0: The variable names
      --   acc.1: The trailing expression
      recursive let chainlambdas = lam acc. lam expr.
        match expr with TmLam t1 then
          chainlambdas (concat acc [t1.0]) t1.2
        else
          (acc.0, expr)
      in
      let argres = chainlambdas [] t.2 in
      let name = t.0 in
      let args = argres.0 in
      let letexpr = argres.1 in
      let inexpr = t.3 in
      strJoin "" ["let ", name, " ", strJoin " " args, " =", newline (incr indent),
                  ocamlcodegen (incr indent) letexpr, newline indent,
                  "in", newline indent,
                  ocamlcodegen indent inexpr]
end

lang RecLetsOCamlCode = RecLetsAst
    sem ocamlcodegen (indent : Int) =
    | TmRecLets t ->
      -- Initiate a list with the code generated code
      let list = ["let "] in
      recursive let generatelets = lam genacc. lam l.
        if null l then
          genacc
        else
          recursive let chainlambdas = lam acc. lam expr.
            match expr with TmLam t1 then
              chainlambdas (concat acc [t1.0]) t1.2
            else
              (acc.0, expr)
          in
          let argres = chainlambdas [] (head l).2 in
          let name = (head l).0
          let args = argres.0 in
          let letexpr = argres.1 in
          let prefix = if null genacc then "let rec " else "    and " in
          let updatedgenacc = concat genacc [
            prefix, name, " ", strJoin " " args, " =", newline (addi 4 (incr indent)),
            ocamlcodegen (addi 4 (incr indent)) letexpr, newline indent
          ]
          in
          generatelets updatedgenacc (tail l)
      in
      let recexprs = t.0 in
      let inexpr = t.1 in
      let list = concat (generatelets [] recexprs) [
        "in", newline indent,
        ocamlcodegen indent inexpr
      ]
      in
      strJoin "" list
end

lang ConstOCamlCode = ConstAst
    sem ocamlconstgen (indent : Int) =
    -- intentionally left blank

    sem ocamlcodegen (indent : Int) =
    | TmConst c -> ocamlconstgen indent c
end

lang UnitOCamlCode = UnitAst
    sem ocamlconstgen (indent : Int) =
    | CUnit -> "()"
end

lang IntOCamlCode = IntAst
    sem ocamlconstgen (indent : Int) =
    | CInt i -> int2string i
end

lang ArithIntOCamlCode = ArithIntAst
    sem ocamlconstgen (indent : Int) =
    | CAddi _ -> "( + )"
    | CSubi _ -> "( - )"
    | CMuli _ -> "( * )"
end

lang BoolOCamlCode = BoolAst
    sem ocamlconstgen (indent : Int) =
    | CBool b -> if b then "true" else "false"
    | CNot _ -> "not"
    | CAnd _ -> "( && )"
    | COr _ -> "( || )"

    sem ocamlcodegen (indent : Int) =
    | TmIf t ->
      let cond = t.0 in
      let thn = t.1 in
      let els = t.2 in
      strJoin "" [
        "if ", ocamlcodegen indent cond, " then", newline (incr indent),
        ocamlcodegen (incr indent) thn, newline indent,
        "else", newline (incr indent),
        ocamlcodegen (incr indent) els
      ]
end

lang CmpOCamlCode = CmpAst
    sem ocamlconstgen (indent : Int) =
    | CEqi _ -> "( = )"
    | CLti _ -> "( < )"
end

lang SeqOCamlCode = SeqAst
    sem ocamlconstgen (indent : Int) =
    | CNth _ -> "(fun l n -> List.nth n l)"
    | CSeq tms -> strJoin "" ["[", strJoin "; " (map (ocamlcodegen indent) tms), "]"]

    sem ocamlcodegen (indent : Int) =
    | TmSeq tms -> strJoin "" ["[", strJoin "; " (map (ocamlcodegen indent) tms), "]"]
end

lang TupleOCamlCode = TupleAst
    sem ocamlcodegen (indent : Int) =
    | TmTuple tms -> strJoin "" ["(", strJoin ", " (map (ocamlcodegen indent) tms), ")"]
    | TmProj t ->
      let tup = t.0 in
      let n = t.1 in
      recursive let mkproj = lam acc. lam idx.
        if eqi idx (length tms) then
          acc
        else if eqi idx n then
          concat acc ["x"]
        else
          concat acc ["_"]
      in
      let projfun = strJoin "" ["(fun t -> let (", strJoin "," (mkproj [] 0), ") = t in x)"] in
      strJoin "" [projfun, " (",ocamlcodegen indent tup , ")"]
end

mexpr
let example_factorial =
  TmRecLets ([
      ("factorial", None,
        TmLam ("n", None,
          TmIf (
            TmApp (
              TmApp (
                TmVar "eqi",
                TmVar "n"
              ),
              TmConst (CInt 0)
            ),
            TmConst (CInt 1),
            TmApp (
              TmVar "factorial",
              TmApp (
                TmApp (
                  TmVar "subi",
                  TmVar "n"
                ),
                TmConst (CInt 1)
              )
            )
          )
        )
      )
    ],
    TmConst CUnit
  )
in
()
