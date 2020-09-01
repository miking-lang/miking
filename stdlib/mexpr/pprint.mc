
include "char.mc"
include "option.mc"
include "seq.mc"
include "string.mc"
include "name.mc"
include "symbol.mc"

include "mexpr/ast.mc"

let spacing = lam indent. makeSeq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

-- Set spacing on increment
let incr = lam indent. addi indent 2

let symbolDelim = "'"

-- Constructor name translation
let conString = lam name.
  match name with (str,sym) then
    let str =
      if eqi (length str) 0 then
        "#con\"\""
      else if is_upper_alpha (head str) then
        str
      else
        join ["#con\"", str, "\""] in
    let sym = if nameHasSym name then sym2string sym else "" in
    strJoin symbolDelim [str, sym]
  else never

-- Variable name translation (TODO Some code duplication)
let varString = lam name.
  match name with (str,sym) then
    let str =
      if eqi (length str) 0 then
        "#var\"\""
      else if is_lower_alpha (head str) then
        str
      else
        join ["#var\"", str, "\""] in
    let sym = if nameHasSym name then sym2string sym else "" in
    strJoin symbolDelim [str, sym]
  else never

-----------
-- TERMS --
-----------

lang VarPrettyPrint = VarAst
  sem pprintCode (indent : Int) =
  | TmVar t -> varString t.ident
end

lang AppPrettyPrint = AppAst
  sem pprintCode (indent : Int) =
  | TmApp t ->
    let l = pprintCode indent t.lhs in
    let r = pprintCode indent t.rhs in
    join ["(", l, ") (", r, ")"]
end

lang FunPrettyPrint = FunAst
  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) =
  | TmLam t ->
    let ident = varString t.ident in
    let tpe =
      match t.tpe with Some t1 then
        concat " : " (getTypeStringCode indent t1)
      else ""
    in
    let body = pprintCode (incr indent) t.body in
    join ["lam ", ident, tpe, ".", newline (incr indent), body]
end

lang RecordPrettyPrint = RecordAst
  sem pprintCode (indent : Int) =
  | TmRecord t ->
    if eqi (length t.bindings) 0 then "{}"
    else
      let binds =
        map (lam r. join
                      [r.0, " = ",
                       pprintCode (incr indent) r.1])
          t.bindings in
      let merged = strJoin (concat ", " (newline (incr indent))) binds in
      join ["{ ", merged, " }"]
  | TmRecordUpdate t ->
    join ["{", pprintCode indent t.rec, " with ", t.key,
                " = ", pprintCode indent t.value, "}"]
end

lang LetPrettyPrint = LetAst
  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) =
  | TmLet t ->
    let ident = varString t.ident in
    let body = pprintCode (incr indent) t.body in
    let inexpr = pprintCode indent t.inexpr in
    join ["let ", ident, " =", newline (incr indent),
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
      let ident = varString l.ident in
      let body = pprintCode (incr (incr indent)) l.body in
      join [acc, newline (incr indent),
                  "let ", ident, " =", newline (incr (incr indent)),
                  body]
    in
    join [foldl pprintLets "recursive" lets, newline indent,
                "in", newline indent, inexpr]
end

lang ConstPrettyPrint = ConstAst
  sem getConstStringCode (indent : Int) =
  -- intentionally left blank

  sem pprintCode (indent : Int) =
  | TmConst t -> getConstStringCode indent t.val
end

lang DataPrettyPrint = DataAst
  sem getTypeStringCode (indent : Int) =
  -- Intentionally left blank

  sem pprintCode (indent : Int) =
  | TmConDef t ->
    let name = conString t.ident in
    let tpe =
      match t.tpe with Some t1 then
        concat " : " (getTypeStringCode indent t1)
      else ""
    in
    let inexpr = pprintCode indent t.inexpr in
    join ["con ", name, tpe, " in", newline indent, inexpr]

  | TmConApp t ->
    let l = conString t.ident in
    let r = pprintCode indent t.body in
    join ["(", l, ") (", r, ")"]
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
    join ["match ", target, " with ", pat, " then",
                newline (incr indent), thn, newline indent, "else",
                newline (incr indent), els]
end

lang UtestPrettyPrint = UtestAst
  sem pprintCode (indent : Int) =
  | TmUtest t ->
    let test = pprintCode indent t.test in
    let expected = pprintCode indent t.expected in
    let next = pprintCode indent t.next in
    join ["utest ", test, newline indent,
                "with ", expected, newline indent,
                "in", newline indent, next]
end

lang SeqPrettyPrint = SeqAst + ConstPrettyPrint + CharAst
  sem pprintCode (indent : Int) =
  | TmSeq t ->
    let extract_char = lam e.
      match e with TmConst t1 then
        match t1.val with CChar c then
          Some (c.val)
        else None ()
      else None ()
    in
    let is_char = lam e. match extract_char e with Some c then true else false in
    if all is_char t.tms then
      concat "\"" (concat (map (lam e. match extract_char e with Some c then c else '?') t.tms)
                          "\"")
    else
      let merged = strJoin (concat ", " (newline (incr indent)))
                     (map (pprintCode (incr indent)) t.tms) in
      join ["[ ", merged, " ]"]
end

lang NeverPrettyPrint = NeverAst
  sem pprintCode (indent : Int) =
  | TmNever {} -> "never"
end

---------------
-- CONSTANTS --
---------------
-- All constants in boot have not been implemented. Missing ones can be added
-- as needed.

lang IntPrettyPrint = IntAst + IntPat + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CInt t -> int2string t.val
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddi _ -> "addi"
  | CSubi _ -> "subi"
  | CMuli _ -> "muli"
end

lang FloatPrettyPrint = FloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CFloat t -> float2string t.val
end

lang ArithFloatPrettyPrint = ArithFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CAddf _ -> "addf"
  | CSubf _ -> "subf"
  | CMulf _ -> "mulf"
  | CDivf _ -> "divf"
  | CNegf _ -> "negf"
end

lang BoolPrettyPrint = BoolAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CBool b -> if b.val then "true" else "false"
  | CNot _ -> "not"
end

lang CmpIntPrettyPrint = CmpIntAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqi _ -> "eqi"
  | CLti _ -> "lti"
end

lang CmpFloatPrettyPrint = CmpFloatAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CEqf _ -> "eqf"
  | CLtf _ -> "ltf"
end

lang CharPrettyPrint = CharAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CChar c -> ['\'', c.val, '\'']
end

lang SymbPrettyPrint = SymbAst + ConstPrettyPrint
  sem getConstStringCode (indent : Int) =
  | CSymb _ -> "sym"
end

lang CmpSymbPrettyPrint = CmpSymbAst + ConstPrettyPrint
   sem getConstStringCode (indent : Int) =
   | CEqs _ -> "eqs"
end

lang SeqOpPrettyPrint = SeqOpAst + ConstPrettyPrint + CharAst
  sem getConstStringCode (indent : Int) =
  | CGet _ -> "get"
  | CCons _ -> "cons"
  | CSnoc _ -> "snoc"
  | CConcat _ -> "concat"
  | CLength _ -> "length"
  | CHead _ -> "head"
  | CTail _ -> "tail"
  | CNull _ -> "null"
  | CReverse _ -> "reverse"
end

--------------
-- PATTERNS --
--------------

lang VarPatPrettyPrint = VarPat
  sem getPatStringCode (indent : Int) =
  | PVar {ident = PName name} -> varString name
  | PVar {ident = PWildcard ()} -> "_"
end

lang SeqTotPatPrettyPrint = SeqTotPat
  -- TODO
end

lang SeqEdgPatPrettyPrint = SeqEdgPat
  -- TODO
end

lang RecordPatPrettyPrint = RecordPat
  sem getPatStringCode (indent : Int) =
  | PRecord {bindings = bindings} ->
    let binds = map
      (lam r. join [r.0, " = ", getPatStringCode indent r.1]) bindings
    in
    join ["{", strJoin ", " binds, "}"]
end

lang DataPatPrettyPrint = DataPat
  sem getPatStringCode (indent : Int) =
  | PCon t ->
    let name = conString t.ident in
    let subpat = getPatStringCode indent t.subpat in
    join [name, " (", subpat, ")"]
end

lang IntPatPrettyPrint = IntPat
  sem getPatStringCode (indent : Int) =
  | PInt t -> int2string t.val
end

lang CharPatPrettyPrint = CharPat
  sem getPatStringCode (indent : Int) =
  | PChar t -> ['\'', t.val, '\'']
end

lang BoolPatPrettyPrint = BoolPat
  sem getPatStringCode (indent : Int) =
  | PBool b -> if b.val then "true" else "false"
end

lang AndPatPrettyPrint = AndPat
  -- TODO
end

lang OrPatPrettyPrint = OrPat
  -- TODO
end

lang NotPatPrettyPrint = NotPat
  -- TODO
end

-----------
-- TYPES --
-----------
-- TODO Update (also not up to date in boot?)

lang TypePrettyPrint = FunTypeAst + DynTypeAst + UnitTypeAst + CharTypeAst + SeqTypeAst +
                       TupleTypeAst + RecordTypeAst + DataTypeAst + ArithTypeAst +
                       BoolTypeAst + AppTypeAst + FunAst + DataPrettyPrint
    sem getTypeStringCode (indent : Int) =
    | TyArrow t -> join ["(", getTypeStringCode indent t.from, ") -> (",
                               getTypeStringCode indent t.to, ")"]
    | TyDyn _ -> "Dyn"
    | TyUnit _ -> "()"
    | TyChar _ -> "Char"
    | TyString _ -> "String"
    | TySeq t -> join ["[", getTypeStringCode indent t.tpe, "]"]
    | TyProd t ->
      let tpes = map (lam x. getTypeStringCode indent x) t.tpes in
      join ["(", strJoin ", " tpes, ")"]
    | TyRecord t ->
      let conventry = lam entry.
          join [entry.ident, " : ", getTypeStringCode indent entry.tpe]
      in
      join ["{", strJoin ", " (map conventry t.tpes), "}"]
    | TyCon t -> t.ident
    | TyInt _ -> "Int"
    | TyBool _ -> "Bool"
    | TyApp t ->
      -- Unsure about how this should be formatted or what this type even means.
      getTypeStringCode indent (TyArrow {from = t.lhs, to = t.rhs})
end

------------------------
-- MEXPR PPRINT FRAGMENT --
------------------------

lang MExprPrettyPrint =

  -- Terms
  VarPrettyPrint + AppPrettyPrint + FunPrettyPrint + RecordPrettyPrint +
  LetPrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint + DataPrettyPrint +
  MatchPrettyPrint + UtestPrettyPrint + SeqPrettyPrint + NeverPrettyPrint

  -- Constants
  + IntPrettyPrint + ArithIntPrettyPrint + FloatPrettyPrint +
  ArithFloatPrettyPrint + BoolPrettyPrint + CmpIntPrettyPrint +
  CmpFloatPrettyPrint + CharPrettyPrint + SymbPrettyPrint + CmpSymbPrettyPrint
  + SeqOpPrettyPrint

  -- Patterns
  + VarPatPrettyPrint + SeqTotPatPrettyPrint + SeqEdgPatPrettyPrint +
  RecordPatPrettyPrint + DataPatPrettyPrint + IntPatPrettyPrint +
  CharPatPrettyPrint + BoolPatPrettyPrint + AndPatPrettyPrint +
  OrPatPrettyPrint + NotPatPrettyPrint

  -- Types
  + TypePrettyPrint

mexpr
use MExprPrettyPrint in

let cons_ = appf2_ (var_ "cons") in
let concat_ = appf2_ (var_ "concat") in

-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in
let func_foo =
  let_ "foo" (
    lam_ "a" (None ()) (
      lam_ "b" (None ()) (
        bindall_ [
          let_ "bar" (
            lam_ "x" (None ()) (
              addi_ (var_ "b") (var_ "x")
            )
          ),
          let_ "babar" (int_ 3),
          addi_ (app_ (var_ "bar")
                      (var_ "babar"))
                (var_ "a")
        ]
      )
    )
  )
in

-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
let func_factorial =
    reclets_add "factorial"
        (lam_ "n" (Some (tyint_))
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
    reclets_add "even"
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 0))
                 (true_)
                 (not_ (app_ (var_ "odd")
                             (subi_ (var_ "x") (int_ 1))))))
    (reclets_add "odd"
        (lam_ "x" (None ())
            (if_ (eqi_ (var_ "x") (int_ 1))
                 (true_)
                 (not_ (app_ (var_ "even")
                             (subi_ (var_ "x") (int_ 1))))))
    reclets_empty)
in


-- let recget = {i = 5, s = "hello!"} in
let func_recget =
    let_ "recget" (
        record_add "i" (int_ 5) (
        record_add "s" (str_ "hello!")
        record_empty))
in

-- let recconcs = lam rec. lam s. {rec with s = concat rec.s s} in
let func_recconcs =
    let_ "recconcs" (lam_ "rec" (None ()) (lam_ "s" (Some (tystr_)) (
        recordupdate_ (var_ "rec")
                      "s"
                      (concat_ (recordproj_ "s" (var_ "rec"))
                               (var_ "s")))))
in

-- con MyConA in
let func_mycona = condef_ "MyConA" (None ()) in

-- con #con"myConB" : (Bool, Int) in
let func_myconb = condef_ "myConB" (Some (typrod_ [tybool_, tyint_])) in

-- let isconb : Bool = lam c : #con"myConB".
--     match c with #con"myConB" (true, 17) then
--         true
--     else
--         false
let func_isconb =
    let_ "isconb" (
        lam_ "c" (Some (tycon_ "myConB")) (
            match_ (var_ "c")
                   (pcon_ "myConB" (ptuple_ [ptrue_, pint_ 17]))
                   (true_)
                   (false_)))
in

-- let addone : Int -> Int = lam i : Int. (lam x : Int. addi x 1) i
let func_addone =
  let_ "addone" (
      lam_ "i" (Some (tyint_)) (
        app_ (lam_ "x" (Some (tyint_)) (addi_ (var_ "x") (int_ 1)))
             (var_ "i")
      )
  )
in

let sample_ast =
  bindall_ [
    func_foo,
    func_factorial,
    funcs_evenodd,
    func_recget,
    func_recconcs,
    func_mycona,
    func_myconb,
    func_isconb,
    func_addone
  ]
in

-- let _ = print "\n\n" in
-- let _ = print (pprintCode 0 sample_ast) in
-- let _ = print "\n\n" in

utest geqi (length (pprintCode 0 sample_ast)) 0 with true in
()
