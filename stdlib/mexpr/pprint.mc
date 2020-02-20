include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

include "mexpr/ast.mc"

let spacing = lam indent. makeseq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

-- Set spacing on increment
let incr = lam indent. addi indent 4

lang VarPrettyPrint = VarAst + VarPat
    sem pprintCode (indent : Int) =
    | TmVar t ->
      if eqi (length t.ident) 0 then
        "#var\"\""
      else if is_lower_alpha (head t.ident) then
        t.ident
      else
        strJoin "" ["#var\"", t.ident, "\""]

    sem getPatStringCode (indent : Int) =
    | PVar t -> pprintCode indent (TmVar {ident = t.ident})
end

lang AppPrettyPrint = AppAst
    sem pprintCode (indent : Int) =
    | TmApp t ->
      let l = pprintCode indent t.lhs in
      let r = pprintCode indent t.rhs in
      strJoin "" [l, " (", r, ")"]
end

lang FunPrettyPrint = FunAst
    sem getTypeStringCode (indent : Int) =
    -- Intentionally left blank

    sem pprintCode (indent : Int) =
    | TmLam t ->
      let ident = t.ident in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      let body = pprintCode indent t.body in
      strJoin "" ["lam ", ident, tpe, ".", newline indent, body]
end

lang LetPrettyPrint = LetAst
    sem getTypeStringCode (indent : Int) =
    -- Intentionally left blank

    sem pprintCode (indent : Int) =
    | TmLet t ->
      let ident = t.ident in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      let body = pprintCode (incr indent) t.body in
      let inexpr = pprintCode indent t.inexpr in
      strJoin "" ["let ", ident, tpe, " =", newline (incr indent),
                  body, newline indent,
                  "in", newline indent,
                  inexpr]
end

lang RecLetsPrettyPrint = RecLetsAst
    sem getTypeStringCode (indent : Int) =
    -- Intentionally left blank

    sem pprintCode (indent : Int) =
    | TmRecLets t ->
      let lets = t.bindings in
      let inexpr = pprintCode indent t.inexpr in
      let pprintLets = lam acc. lam l.
        let ident = l.ident in
        let tpe =
          match l.tpe with Some l1 then
            concat " : " (getTypeStringCode indent l1)
          else ""
        in
        let body = pprintCode (incr (incr indent)) l.body in
        strJoin "" [acc, newline (incr indent),
                    "let ", ident, tpe, " =", newline (incr (incr indent)),
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

lang UnitPrettyPrint = UnitAst + UnitPat + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CUnit _ -> "()"

    sem getPatStringCode (indent : Int) =
    | PUnit _ -> "()"
end

lang IntPrettyPrint = IntAst + IntPat + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CInt t -> int2string t.val

    sem getPatStringCode (indent : Int) =
    | PInt t -> int2string t.val
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CAddi _ -> "addi"
    | CSubi _ -> "subi"
    | CMuli _ -> "muli"
end

lang BoolPrettyPrint = BoolAst + BoolPat + ConstPrettyPrint
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

    sem getPatStringCode (indent : Int) =
    | PBool b -> getConstStringCode indent (CBool {val = b.val})
end

lang CmpPrettyPrint = CmpAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CEqi _ -> "eqi"
    | CLti _ -> "lti"
end

lang CharPrettyPrint = CharAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CChar c -> [head "'", c.val, head "'"]
end

lang SeqPrettyPrint = SeqAst + ConstPrettyPrint
    sem getConstStringCode (indent : Int) =
    | CNth _ -> "nth"
    | CSeq t -> pprintCode indent (TmSeq {tms = t.tms})

    sem pprintCode (indent : Int) =
    | TmSeq t -> strJoin "" ["[", strJoin ", " (map (pprintCode indent) t.tms), "]"]
end

lang TuplePrettyPrint = TupleAst + TuplePat
    sem pprintCode (indent : Int) =
    | TmTuple t -> strJoin "" ["(", strJoin ", " (map (pprintCode indent) t.tms), ")"]
    | TmProj t -> strJoin "" [pprintCode indent t.tup, ".", int2string t.idx]

    sem getPatStringCode (indent : Int) =
    | PTuple t -> strJoin "" ["(", strJoin ", " (map (getPatStringCode indent) t.pats), ")"]
end

lang RecordPrettyPrint = RecordAst
    sem pprintCode (indent : Int) =
    | TmRecord t ->
      let binds = map (lam r. strJoin "" [r.key, " = ", pprintCode indent r.value]) t.bindings in
      strJoin "" ["{", strJoin ", " binds, "}"]
    | TmRecordProj t -> strJoin "" [pprintCode indent t.rec, ".", t.key]
    | TmRecordUpdate t ->
      strJoin "" ["{", pprintCode indent t.rec, " with ", t.key,
                  " = ", pprintCode indent t.value, "}"]
end

lang DataPrettyPrint = DataAst + DataPat
    sem getTypeStringCode (indent : Int) =
    -- Intentionally left blank

    sem pprintCode (indent : Int) =
    | TmConDef t ->
      let name = pprintCode indent (TmConFun {ident = t.ident}) in
      let tpe =
        match t.tpe with Some t1 then
          concat " : " (getTypeStringCode indent t1)
        else ""
      in
      let inexpr = pprintCode indent t.inexpr in
      strJoin "" ["con ", name, tpe, " in", newline indent, inexpr]
    | TmConFun t ->
      if eqi (length t.ident) 0 then
        "#con\"\""
      else if is_upper_alpha (head t.ident) then
        t.ident
      else
        strJoin "" ["#con\"", t.ident, "\""]

    sem getPatStringCode (indent : Int) =
    | PCon t ->
      let name = pprintCode indent (TmConFun {ident = t.ident}) in
      let subpat = getPatStringCode indent t.subpat in
      strJoin "" [name, " (", subpat, ")"]
end

lang MatchPrettyPrint = MatchAst
    sem getPatStringCode (indent : Int) =
    -- intentionally left blank

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

lang TypePrettyPrint = DynTypeAst + UnitTypeAst + CharTypeAst + SeqTypeAst +
                       TupleTypeAst + RecordTypeAst + DataTypeAst + ArithTypeAst +
                       BoolTypeAst + AppTypeAst + FunAst + DataPrettyPrint
    sem getTypeStringCode (indent : Int) =
    | TyArrow t -> strJoin "" ["(", getTypeStringCode indent t.from, ") -> (",
                               getTypeStringCode indent t.to, ")"]
    | TyDyn _ -> "Dyn"
    | TyUnit _ -> "()"
    | TyChar _ -> "Char"
    | TyString _ -> "String"
    | TySeq t -> strJoin "" ["[", getTypeStringCode indent t.tpe, "]"]
    | TyProd t ->
      let tpes = map (lam x. getTypeStringCode indent x) t.tpes in
      strJoin "" ["(", strJoin ", " tpes, ")"]
    | TyRecord t ->
      let conventry = lam entry.
          strJoin "" [entry.ident, " : ", getTypeStringCode indent entry.tpe]
      in
      strJoin "" ["{", strJoin ", " (map conventry t.tpes), "}"]
    | TyCon t -> pprintCode indent (TmConFun {ident = t.ident})
    | TyInt _ -> "Int"
    | TyBool _ -> "Bool"
    | TyApp t ->
      -- Unsure about how this should be formatted or what this type even means.
      getTypeStringCode indent (TyArrow {from = t.lhs, to = t.rhs})
end

lang MExprPrettyPrint = VarPrettyPrint + AppPrettyPrint + FunPrettyPrint +
                        LetPrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint +
                        UnitPrettyPrint + IntPrettyPrint + ArithIntPrettyPrint +
                        BoolPrettyPrint + CmpPrettyPrint + CharPrettyPrint +
                        SeqPrettyPrint + TuplePrettyPrint + RecordPrettyPrint +
                        DataPrettyPrint + MatchPrettyPrint + UtestPrettyPrint +
                        TypePrettyPrint

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
    else match letexpr with TmConDef t then
        TmConDef {t with inexpr = letappend t.inexpr expr}
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
let confun_ = lam s. TmConFun {ident = s} in
let condef_ = lam s. lam tpe. TmConDef {ident = s, tpe = tpe, inexpr = unit_} in
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
let match_ = lam target. lam pat. lam thn. lam els.
    TmMatch {target = target, pat = pat, thn = thn, els = els}
in
let pvar_ = lam s. PVar {ident = s} in
let punit_ = PUnit {} in
let pint_ = lam i. PInt {val = i} in
let ptrue_ = PBool {val = true} in
let pfalse_ = PBool {val = false} in
let ptuple_ = lam pats. PTuple {pats = pats} in
let pcon_ = lam cs. lam cp. PCon {ident = cs, subpat = cp} in
let seq_ = lam tms. TmSeq {tms = tms} in
let tuple_ = lam tms. TmTuple {tms = tms} in
let proj_ = lam tup. lam idx. TmProj {tup = tup, idx = idx} in
let record_empty = TmRecord {bindings = []} in
let record_add = lam key. lam value. lam record.
    match record with TmRecord t then
        TmRecord {t with bindings = cons {key = key, value = value} t.bindings}
    else
        error "record is not a TmRecord construct"
in
let recordproj_ = lam key. lam rec. TmRecordProj {rec = rec, key = key} in
let recordupdate_ = lam key. lam value. lam rec. TmRecordUpdate {rec = rec, key = key, value = value} in

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
let cons_ = appf2_ (TmVar {ident = "cons"}) in
let concat_ = appf2_ (TmVar {ident = "concat"}) in

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
    reclets_add "factorial" (Some (TyInt {}))
        (lam_ "n" (Some (TyInt {}))
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


-- let recget = {i = 5, s = "hello!"} in
let func_recget =
    let_ "recget" (Some (TyRecord {tpes = [{ident = "i", tpe = TyInt {}},
                                           {ident = "s", tpe = TySeq {tpe = TyChar {}}}]})) (
        record_add "i" (int_ 5) (
        record_add "s" (str_ "hello!")
        record_empty))
in

-- let recconcs = lam rec. lam s. {rec with s = concat rec.s s} in
let func_recconcs =
    let_ "recconcs" (None ()) (lam_ "rec" (None ()) (lam_ "s" (Some (TyString {})) (
        recordupdate_ "s"
                      (concat_ (recordproj_ "s" (var_ "rec"))
                               (var_ "s"))
                      (var_ "rec"))))
in

-- con MyConA in
let func_mycona = condef_ "MyConA" (None ()) in

-- con #con"myConB" : (Bool, Int) in
let func_myconb = condef_ "myConB" (Some (TyProd {tpes = [TyBool {}, TyInt {}]})) in

-- let isconb : Bool = lam c : #con"myConB".
--     match c with #con"myConB" (true, 17) then
--         true
--     else
--         false
let func_isconb =
    let_ "isconb" (Some (TyBool {})) (
        lam_ "c" (Some (TyCon {ident = "myConB"})) (
            match_ (var_ "c")
                   (pcon_ "myConB" (ptuple_ [ptrue_, pint_ 17]))
                   (true_)
                   (false_)))
in

let sample_ast = unit_ in
let sample_ast = letappend sample_ast func_foo in
let sample_ast = letappend sample_ast func_factorial in
let sample_ast = letappend sample_ast funcs_evenodd in
let sample_ast = letappend sample_ast func_recget in
let sample_ast = letappend sample_ast func_recconcs in
let sample_ast = letappend sample_ast func_mycona in
let sample_ast = letappend sample_ast func_myconb in
let sample_ast = letappend sample_ast func_isconb in

--let _ = print "\n\n" in
--let _ = print (pprintCode 0 sample_ast) in
--let _ = print "\n\n" in

utest geqi (length (pprintCode 0 sample_ast)) 0 with true in
()
