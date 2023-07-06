
include "assoc-seq.mc"
include "string.mc"

mexpr

type Term in
con TmLam  : (String, Term) -> Term in
con TmApp  : (Term, Term) -> Term in
con TmVar  : (String) -> Term in
con TmInt  : (Int) -> Term in
con TmAdd  : (Term, Term) -> Term in
con TmClos : (String, Term, AssocSec String Term) -> Term in

let insert = assocSeqInsert in
let lookup = assocSeqLookup {eq = eqString} in

--addi y ((lam x. addi x 3) 2)
let p1 = TmAdd(TmInt(1),TmInt(2)) in
let p2 = TmApp(TmLam("x", TmAdd(TmVar("x"), TmInt(3))), TmInt(2)) in
let p3 = TmAdd(TmVar("y"), p2) in

recursive
  let eval = lam env. lam t.
    switch t
      case TmLam(x, t1) then
        TmClos(x, t1, env)
      case TmApp(t1, t2) then
        match (eval env t1, eval env t2) with (TmClos(x, t1_, env_), v2) in
        eval (insert x v2 env) t1_
      case TmVar(x) then
        match lookup x env with Some v in v
      case TmClos _ then
        t
      case TmAdd(t1, t2) then
        match (eval env t1, eval env t2) with (TmInt(i1), TmInt(i2)) in
        TmInt(addi i1 i2)
      case TmInt(_) then
        t
    end
in

--dprint (eval [] p1); print "\n"

-- dprint (eval [] p2); print "\n"

-- dprint (eval [("y", TmInt(10))] p3); print "\n"


let prog = lam y. eval [("y", TmInt(y))] p3 in
dprint prog; print "\n------\n";
dprint (prog 10); print "\n";
dprint (prog 100); print "\n"
