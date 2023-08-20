
include "assoc-seq.mc"
include "string.mc"

mexpr

type Term in
con TmLam    : (String, Term) -> Term in
con TmApp    : (Term, Term) -> Term in
con TmVar    : (String) -> Term in
con TmLetRec : (String, Term, Term) -> Term in
con TmIf     : (Term, Term, Term) -> Term in
con TmInt    : (int) -> Term in
con TmBool   : (bool) -> Term in
con TmLeq    : (Term, Term) -> Term in
con TmAdd    : (Term, Term) -> Term in
con TmSub    : (Term, Term) -> Term in
con TmClos   : (String, Term, AssocSec String Term) -> Term in

let insert = assocSeqInsert in
let lookup = assocSeqLookup {eq = eqString} in

let p = TmLetRec("fib", TmLam("n",
          TmIf(TmLeq(TmVar("n"), TmInt(1)),
             TmVar("n"),
             TmAdd(
                TmApp(TmVar("fib"), TmSub(TmVar("n"), TmInt(1))),
                TmApp(TmVar("fib"), TmSub(TmVar("n"), TmInt(2)))))),
          TmApp(TmVar("fib")))
in


let p1 = TmLam("x", TmAdd(TmVar("x"), TmInt(5)))
in


let p2 = TmLam("x", TmLeq(TmVar("x"), TmInt(7)))
in

let p3 = TmLam("x",
           TmIf(TmLeq(TmVar("x"), TmInt(7)), TmInt(100), TmInt(200)))
in

let p4 = TmLetRec("my", TmLam("x", TmVar("x")), TmVar("my")) in

recursive
  let lower = lam env. lam t.
    switch t
      case TmLam(x, t1) then
        dive (lam y. lower (insert x y env) t1)
      case TmApp(t1, t2) then
        (lower env t1) (lower env t2)
      case TmVar(x) then
        match lookup x env with Some y in y
      case TmLetRec(x, t1, t2) then
          recursive
            let y = lower (insert x y env) t1
          in
          lower (insert x y env) t2
      case TmIf(t1, t2, t3) then
        if lower env t1 then lower env t2 else lower env t3
      case TmInt(i) then i
      case TmBool(b) then b
      case TmLeq(t1, t2) then
        leqi (lower env t1) (lower env t2)
      case TmAdd(t1, t2) then
        match (lower env t1, lower env t2) with (i1, i2) in
        addi i1 i2
      case TmSub(t1, t2) then
        match (lower env t1, lower env t2) with (i1, i2) in
        subi i1 i2
    end
in


/-
let tt = TmLam("x", TmAdd(TmVar("x"), TmInt(5))) in
let tt_ = TmInt(1) in
let fib = lam y. prerun (lower [] tt) in
dprint fib; print "\n------\n";
dprint (fib 10); print "\n"
-/


let fib = lam y. prerun (lower [] p4) y in
dprint fib; print "\n------\n";
dprint (fib 3); print "\n"
