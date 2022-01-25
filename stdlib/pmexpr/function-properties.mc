-- Provides an extensible way to define functions as associative, as
-- commutative, and define what their neutral element is.

include "map.mc"
include "option.mc"
include "set.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "pmexpr/ast.mc"

lang PMExprFunctionProperties = PMExprAst + MExprCmp
  sem isAssociative =
  | t -> isAssociativeH (setEmpty cmpExpr) t

  sem isAssociativeH (assocFunctions : Set Expr) =
  | TmConst {val = CAddi _} -> true
  | TmConst {val = CMuli _} -> true
  | TmConst {val = CConcat _} -> true
  | t -> setMem t assocFunctions

  sem isCommutative =
  | t -> isCommutativeH (setEmpty cmpExpr) t

  sem isCommutativeH (commFunctions : Set Expr) =
  | TmConst {val = CAddi _} -> true
  | TmConst {val = CMuli _} -> true
  | t -> setMem t commFunctions

  sem getNeutralElement =
  | t -> getNeutralElementH (mapEmpty cmpExpr) t

  sem getNeutralElementH (neutralElementMap : Map Expr Expr) =
  | TmConst {val = CAddi _} ->
    Some (TmConst {val = CInt {val = 0}, ty = TyInt {info = NoInfo ()},
                   info = NoInfo ()})
  | TmConst {val = CMuli _} ->
    Some (TmConst {val = CInt {val = 1}, ty = TyInt {info = NoInfo ()},
                   info = NoInfo ()})
  | TmConst {val = CConcat _} ->
    Some (TmSeq {tms = [], ty = TySeq {ty = TyUnknown {info = NoInfo ()},
                                       info = NoInfo ()},
                 info = NoInfo ()})
  | t -> mapLookup t neutralElementMap
end

lang TestLang = PMExprFunctionProperties + MExprCmp + MExprEq + MExprSym end

mexpr

use TestLang in

let addi = uconst_ (CAddi ()) in
let subi = uconst_ (CSubi ()) in
let muli = uconst_ (CMuli ()) in
let concat = uconst_ (CConcat ()) in

utest isAssociative addi with true in
utest isAssociative subi with false in
utest isAssociative muli with true in
utest isAssociative concat with true in

utest isCommutative addi with true in
utest isCommutative subi with false in
utest isCommutative muli with true in
utest isCommutative concat with false in

utest getNeutralElement addi with Some (int_ 0) using optionEq eqExpr in
utest getNeutralElement subi with None () using optionEq eqExpr in
utest getNeutralElement muli with Some (int_ 1) using optionEq eqExpr in
utest getNeutralElement concat with Some (seq_ []) using optionEq eqExpr in

let f = symbolize (ulam_ "x" (ulam_ "y" (muli_ (int_ 2) (addi_ (var_ "x") (var_ "y"))))) in
let setEnv = setOfSeq cmpExpr [f] in
let mapEnv = mapFromSeq cmpExpr [(f, int_ 0)] in
utest isAssociativeH setEnv f with true in
utest isCommutativeH setEnv f with true in
utest getNeutralElementH mapEnv f with Some (int_ 0) using optionEq eqExpr in

()
