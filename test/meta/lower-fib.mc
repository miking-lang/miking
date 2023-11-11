
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
con TmMul    : (Term, Term) -> Term in

let insert = assocSeqInsert in
let lookup = assocSeqLookup {eq = eqString} in

let p = TmLetRec("fib", TmLam("n",
          TmIf(TmLeq(TmVar("n"), TmInt(1)),
             TmVar("n"),
             TmAdd(
                TmApp(TmVar("fib"), TmSub(TmVar("n"), TmInt(1))),
                TmApp(TmVar("fib"), TmSub(TmVar("n"), TmInt(2)))))),
          TmApp(TmVar("fib"), TmVar("y")))
in

let p2 = TmIf(TmBool(true), TmAdd(TmVar("y"), TmInt(2)), TmInt(7)) in

let p3 = TmIf(TmLeq(TmInt(3),TmInt(4)), TmAdd(TmVar("y"), TmInt(2)), TmInt(7)) in

let p4 = TmLetRec("foo", TmLam("n",
            TmVar("n")),
            TmApp(TmVar("foo"), TmVar("y"))) in

let p5 = TmLetRec("foo",
            TmLam("n",
              TmIf(TmLeq(TmVar("n"),TmInt(0)),
                TmInt(1),
                TmApp(TmVar("foo"),
                  TmAdd(TmVar("n"), TmInt(subi 0 1))))),
            TmApp(TmVar("foo"), TmVar("y"))) in


let p6 = TmLetRec("foo",
            TmLam("n",
              TmIf(TmLeq(TmVar("n"),TmInt(0)),
                TmInt(1),
                TmAdd(
                  TmApp(TmVar("foo"),
                    TmSub(TmVar("n"), TmInt(1))),
                TmInt(10))
              )),
            TmApp(TmVar("foo"), TmInt(4))) in

let fact = TmLetRec("fact",
            TmLam("n",
              TmIf(TmLeq(TmVar("n"),TmInt(0)),
                TmInt(1),
                TmMul(
                  TmApp(TmVar("fact"),
                    TmSub(TmVar("n"), TmInt(1))),
                TmVar("n"))
              )),
            TmApp(TmVar("fact"), TmVar("y"))) in

let p = p in

recursive
  let lower = lam env. lam t.
--    print "-- Loop\n";
    --dprint ["-- Env:", env]; print "\n";
    switch t
      case TmLam(x, t1) then
        dive (lam w. lower (insert x w env) t1)
      case TmApp(t1, t2) then
--        print "-- TmApp\n";
        (lower env t1) (lower env t2)
         --print "---------------------------- t1a\n";
         --dprint ["t1", t1]; print "\n";
         --print "---------------------------- t1b\n";
         --dprint ["t2", t2]; print "\n";
         --let tt1 = (lower env t1) in
         --let tt2 = (lower env t2) in
         --print "-- before app\n";
         --print "---------------------------- tt1a\n";
         --dprint ["tt1", tt1]; print "\n";
         --print "---------------------------- tt1b\n";
         --dprint ["tt2", tt2]; print "\n";
         --let tt3 = tt1 tt2 in
         --print "-- after app\n";
         --tt3
      case TmVar(x) then
        --dprint ["-- TmVar2: ", x]; print "\n";
        match lookup x env with Some y in y
--        else print "==============\n"
      case TmLetRec(x, t1, t2) then
--          print "--- LetRec\n";
          recursive
            let z = lower (insert x z env) t1
          in
          lower (insert x z env) t2
      case TmIf(t1, t2, t3) then
        if lower env t1 then lower env t2 else lower env t3
--        let xx = lower env t1 in
--        dprint ["-- TmIf: ", xx]; print "\n";
 --       if xx then
 --                  (print "**2\n"; lower env t2) else
 --                  (print "**3\n"; lower env t3)
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
      case TmMul(t1, t2) then
        match (lower env t1, lower env t2) with (i1, i2) in
        muli i1 i2
    end
in


let fib = lam y. prerun (lower [("y", y)] p) in

dprint fib; print "\n------\n";
dprint (fib 8); print "\n"
()
