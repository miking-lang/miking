
include "assoc-seq.mc"
include "string.mc"

mexpr

type Term in
con TmLam  : (String, Term) -> Term in
con TmApp  : (Term, Term) -> Term in
con TmVar  : (String) -> Term in
con TmInt  : (int) -> Term in
con TmAdd  : (Term, Term) -> Term in

let insert = assocSeqInsert in
let lookup = assocSeqLookup {eq = eqString} in

let p1 = TmAdd(TmInt(1),TmInt(2)) in
let p2 = TmApp(TmLam("x", TmAdd(TmVar("x"), TmInt(3))), TmInt(2)) in
let p3 = TmAdd(TmVar("y"), p2) in

recursive
  let lower = lam env. lam t.
    switch t
      case TmLam(x, t1) then
        dive (lam y. lower (insert x y env) t1)
      case TmApp(t1, t2) then
        (lower env t1) (lower env t2)
      case TmVar(x) then
        match lookup x env with Some y in y
      case TmAdd(t1, t2) then
        match (lower env t1, lower env t2) with (i1, i2) in
        addi i1 i2
      case TmInt(i) then
        i
    end
in

let prog = lam y. prerun (lower [("y", y)] p3) in
dprint prog; print "\n------\n";
dprint (prog 10); print "\n";
dprint (prog 100); print "\n"
