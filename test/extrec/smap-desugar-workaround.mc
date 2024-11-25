let digit2char = lam d.
  int2char (addi d (char2int '0'))

let int2string = lam n.
  recursive
  let int2string_rechelper = lam n. lam acc.
    if lti n 10
    then cons (digit2char n) acc
    else int2string_rechelper (divi n 10) (cons (digit2char (modi n 10)) acc)
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n) "")
  else int2string_rechelper n ""

utest int2string 5 with "5"
utest int2string 25 with "25"
utest int2string 314159 with "314159"
utest int2string (negi 314159) with "-314159"

lang BaseArith
  syn Expr = 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr} 
  | TmSub {lhs : Expr, rhs : Expr}

  sem eval : atmost BaseArith::Expr -> Int
  sem eval =
  | TmInt t -> t.val 
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)
  | TmSub t -> subi (eval t.lhs) (eval t.rhs)

  sem smap_Expr_Expr f = 
  | TmInt t -> TmInt t
  | TmAdd t -> 
    TmAdd {TmAddType of lhs = f t.lhs, rhs = f t.rhs}
  | TmSub t -> 
    TmSub {TmSubType of lhs = f t.lhs, rhs = f t.rhs}

  sem pprint = 
  | TmInt t -> 
    print (int2string t.val)
  | TmAdd t -> 
    print "(";
    pprint t.lhs;
    print " + ";
    pprint t.rhs;
    print ")"
  | TmSub t -> 
    print "(";
    pprint t.lhs;
    print " - ";
    pprint t.rhs;
    print ")"

end

lang SugarArith = BaseArith
  syn Expr += 
  | TmIncr {e : Expr} 

  sem smap_Expr_Expr f +=
  | TmIncr t -> TmIncr {TmIncrType of e = f t.e}

  sem pprint +=
  | TmIncr t -> 
    print "(";
    pprint t.e;
    print "++)"

  sem errorOnTmIncr = 
  | TmIncr t -> error "This is not allowed!"
  | TmAdd t -> 
    TmAdd {TmAddType of lhs = errorOnTmIncr t.lhs,
                        rhs = errorOnTmIncr t.rhs}
  | TmSub t -> 
    TmSub {TmSubType of lhs = errorOnTmIncr t.lhs,
                        rhs = errorOnTmIncr t.rhs}
  | TmInt t ->
    TmInt {TmIntType of val = t.val}
   

  sem desugar =
  | TmIncr t -> TmAdd {TmAddType of lhs = desugar t.e, 
                                    rhs = TmInt {TmIntType of val = 1}}
  | other -> smap_Expr_Expr desugar other
end

mexpr
use SugarArith in
let expr = TmInt {TmIntType of val = 42} in
eval expr ;
utest eval expr with 42 using eqi in 
let expr2 = TmAdd {TmAddType of lhs = TmInt {TmIntType of val = 23},
                                rhs = TmInt {TmIntType of val = 42}} in 
eval expr2 ;
utest eval expr2 with 65 using eqi in 
let expr3 = TmIncr {TmIncrType of e = expr} in 

let desugaredExpr = desugar expr3 in 
let stripped = errorOnTmIncr desugaredExpr in 
utest eval stripped with 43 in 
()