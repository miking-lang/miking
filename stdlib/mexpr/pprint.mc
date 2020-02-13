include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

include "mexpr/ast.mc"

let spacing = lam indent. makeseq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

-- Set spacing on increment
let incr = lam indent. addi indent 4

lang VarPrettyPrint = VarAst
    sem pprintCode (indent : Int) =
    | TmVar t ->
      -- Not clear: Is an empty identifier valid syntax?
      if eqi (length t.ident) 0 then
        "#var\"\""
      else if is_lower_alpha (head t.ident) then
        t.ident
      else
        strJoin "" ["#var\"", t.ident, "\""]
end

lang AppPrettyPrint = AppAst
    sem pprintCode (indent : Int) =
    | TmApp t ->
      let l = pprintCode indent t.lhs in
      let r = pprintCode indent t.rhs in
      strJoin "" [l, " (", r, ")"]
end

lang FunPrettyPrint = FunAst
    sem pprintCode (indent : Int) =
    | TmLam t ->
      let ident = t.ident in
      let body = pprintCode indent t.body in
      strJoin "" ["lam ", ident, ".", newline indent, body]
end

lang LetPrettyPrint = LetAst
    sem pprintCode (indent : Int) =
    | TmLet t ->
      let ident = t.ident in
      let body = pprintCode (incr indent) t.body in
      let inexpr = pprintCode indent t.inexpr in
      strJoin "" ["let ", ident, " =", newline (incr indent),
                  body, newline indent,
                  "in", newline indent,
                  inexpr]
end

lang RecLetsPrettyPrint = RecLetsAst
    sem pprintCode (indent : Int) =
    | TmRecLets t ->
      let lets = t.bindings in
      let inexpr = pprintCode indent t.inexpr in
      let pprintLets = lam acc. lam l.
        let ident = l.ident in
        let body = pprintCode (incr (incr indent)) l.body in
        strJoin "" [acc, newline (incr indent),
                    "let ", ident, " =", newline (incr (incr indent)),
                    body]
      in
      strJoin "" [foldl pprintLets "recursive" lets, newline indent,
                  "in", newline indent, inexpr]
end

lang ConstPrettyPrint = ConstAst
    sem getConstStringCode (indent : Int) =
    -- intentionally left blank

    sem pprintCode (indent : Int) =
    | TmConst t -> getConstStringCode indent t.val
end

lang UnitPrettyPrint = UnitAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CUnit _ -> "()"
end

lang IntPrettyPrint = IntAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CInt t -> int2string t.val
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CAddi _ -> "addi"
    | CSubi _ -> "subi"
    | CMuli _ -> "muli"
end

lang BoolPrettyPrint = BoolAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CBool b -> if b.val then "true" else "false"
    | CNot _ -> "not"
    | CAnd _ -> "and"
    | COr _ -> "or"

    sem pprintCode (indent : Int) =
    | TmIf t ->
      let cond = pprintCode indent t.cond in
      let thn = pprintCode (incr indent) t.thn in
      let els = pprintCode (incr indent) t.els in
      strJoin "" ["if ", cond, " then", newline (incr indent), thn, newline indent,
                                "else", newline (incr indent), els]
end

lang CmpPrettyPrint = CmpAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CEqi _ -> "eqi"
    | CLti _ -> "lti"
end

lang CharPrettyPrint = CharAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CChar c -> strJoin "" [head "'", c.val, head "'"]
end

lang SeqPrettyPrint = SeqAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CNth _ -> "nth"
    | CSeq t -> pprintCode indent (TmSeq {tms = t.tms})

    sem pprintCode (indent : Int) =
    | TmSeq t -> strJoin "" ["[", strJoin ", " (map (pprintCode indent) t.tms), "]"]
end

lang TuplePrettyPrint = TupleAst
    sem pprintCode (indent : Int) =
    | TmTuple t -> strJoin "" ["(", strJoin ", " (map (pprintCode indent) t.tms), ")"]
    | TmProj t -> strJoin "" [pprintCode indent t.tup, ".", int2string t.idx]
end

lang DataPrettyPrint = DataAst + DataPat
    sem pprintCode (indent : Int) =
    | TmConDef t ->
      let name = t.ident in
      let inexpr = pprintCode indent t.inexpr in
      strJoin "" ["con ", name, " in", newline indent, inexpr]

    sem getPatStringCode (indent : Int) =
    | PCon t -> strJoin "" [t.ident, " (", t.subpat, ")"]
end

lang MatchPrettyPrint = MatchAst
    sem pprintCode (indent : Int) =
    | TmMatch t ->
      let target = pprintCode indent t.target in
      let pat = getPatStringCode indent t.pat in
      let thn = pprintCode (incr indent) t.thn in
      let els = pprintCode (incr indent) t.els in
      strJoin "" ["match ", target, " with ", pat, " then",
                  newline (incr indent), thn, newline indent, "else",
                  newline (incr indent), els]
end

lang UtestPrettyPrint = UtestAst
    sem pprintCode (indent : Int) =
    | TmUtest t ->
      let test = pprintCode indent t.test in
      let expected = pprintCode indent t.expected in
      let next = pprintCode indent t.next in
      strJoin "" ["utest ", test, " with ", expected, " in", newline indent, next]
end

lang MExprPrettyPrint = VarPrettyPrint + AppPrettyPrint + FunPrettyPrint +
                        LetPrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint +
                        UnitPrettyPrint + IntPrettyPrint + ArithIntPrettyPrint +
                        BoolPrettyPrint + CmpPrettyPrint + CharPrettyPrint +
                        SeqPrettyPrint + TuplePrettyPrint + DataPrettyPrint +
                        MatchPrettyPrint + UtestPrettyPrint

mexpr
use MExprPrettyPrint in
-- The letappend function is used for append let expressions together without
-- having to manually do so in the AST. The provided expr argument is inserted
-- as the inexpr of the last nested Let-expression.
recursive let letappend = lam letexpr. lam expr.
    match letexpr with TmLet t then
        TmLet {t with inexpr = letappend t.inexpr expr}
    else match letexpr with TmRecLets t then
        TmRecLets {t with inexpr = letappend t.inexpr expr}
    else
        expr
in

-- Convenience functions for manually constructing an AST.
let unit_ = TmConst {val = CUnit ()} in
let int_ = lam i. TmConst {val = CInt {val = i}} in
let true_ = TmConst {val = CBool {val = true}} in
let false_ = TmConst {val = CBool {val = false}} in
let char_ = lam c. TmConst {val = CChar {val = c}} in
let str_ = lam s. TmConst {val = CSeq {tms = map char_ s}} in
let var_ = lam s. TmVar {ident = s} in
let let_ = lam ident. lam tpe. lam body.
    TmLet {ident = ident,
           tpe = tpe,
           body = body,
           inexpr = unit_}
in
let reclets_empty = TmRecLets {bindings = [], inexpr = unit_} in
let reclets_add = lam ident. lam tpe. lam body. lam reclets.
    match reclets with TmRecLets t then
        let newbind = {ident = ident,
                       tpe = tpe,
                       body = body} in
        TmRecLets {t with bindings = concat [newbind] t.bindings}
    else
        error "reclets is not a TmRecLets construct"
in
let lam_ = lam ident. lam tpe. lam body.
    TmLam {ident = ident,
           tpe = tpe,
           body = body}
in
let if_ = lam cond. lam thn. lam els.
    TmIf {cond = cond, thn = thn, els = els}
in
let seq_ = lam tms. TmSeq {tms = tms} in
let tuple_ = lam tms. TmTuple {tms = tms} in
let proj_ = lam tup. lam idx. TmProj {tup = tup, idx = idx} in
let app_ = lam lhs. lam rhs. TmApp {lhs = lhs, rhs = rhs} in
let appf1_ = lam f. lam a1. app_ f a1 in
let appf2_ = lam f. lam a1. lam a2. app_ (appf1_ f a1) a2 in
let appf3_ = lam f. lam a1. lam a2. lam a3. app_ (appf2_ f a1 a2) a3 in
let addi_ = appf2_ (TmConst {val = CAddi ()}) in
let subi_ = appf2_ (TmConst {val = CSubi ()}) in
let muli_ = appf2_ (TmConst {val = CMuli ()}) in
let lti_ = appf2_ (TmConst {val = CLti ()}) in
let eqi_ = appf2_ (TmConst {val = CEqi ()}) in
let and_ = appf2_ (TmConst {val = CAnd ()}) in
let or_ = appf2_ (TmConst {val = COr ()}) in
let not_ = appf1_ (TmConst {val = CNot ()}) in

-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in
let func_foo =
    let_ "foo" (None ()) (lam_ "a" (None ()) (lam_ "b" (None ()) (
        let bar = let_ "bar" (None ()) (lam_ "x" (None ())
                       (addi_ (var_ "b") (var_ "x"))) in
        let babar = let_ "babar" (None ()) (int_ 3) in
        letappend bar (
        letappend babar (
            addi_ (app_ (var_ "bar")
                        (var_ "babar"))
                  (var_ "a"))))))
in

-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
let func_factorial =
    reclets_add "factorial" (None ())
        (lam_ "n" (None ())
            (if_ (eqi_ (var_ "n") (int_ 0))
                 (int_ 1)
                 (muli_ (var_ "n")
                        (app_ (var_ "factorial")
                              (subi_ (var_ "n")
                                     (int_ 1))))))
    reclets_empty
in

-- recursive
--     let even = lam x.
--         if eqi x 0
--         then true
--         else not (odd (subi x 1))
--     let odd = lam x.
--         if eqi x 1
--         then true
--         else not (even (subi x 1))
-- in
let funcs_evenodd =
    reclets_add "even" (None ())
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 0))
                 (true_)
                 (not_ (app_ (var_ "odd")
                             (subi_ (var_ "x") (int_ 1))))))
    (reclets_add "odd" (None ())
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 1))
                 (true_)
                 (not_ (app_ (var_ "even")
                             (subi_ (var_ "x") (int_ 1))))))
    reclets_empty)
in

let sample_ast = unit_ in
let sample_ast = letappend sample_ast func_foo in
let sample_ast = letappend sample_ast func_factorial in
let sample_ast = letappend sample_ast funcs_evenodd in

--let _ = print "\n\n" in
--let _ = print (pprintCode 0 sample_ast) in
--let _ = print "\n\n" in

utest geqi (length (pprintCode 0 sample_ast)) 0 with true in
()
