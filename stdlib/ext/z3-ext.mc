include "option.mc" -- Option
include "string.mc" -- eqString
include "seq.mc" -- join

type Z3Context
type Z3Solver
type Z3SolverStatus
type Z3Model
type Z3Symbol
type Z3Expr

type Z3SolverResult
con Z3Unsatisfiable : () -> Z3SolverResult
con Z3Unknown : () -> Z3SolverResult
con Z3Satisfiable : () -> Z3SolverResult

external externalZ3MkContext : [(String, String)] -> Z3Context
let z3MkContext = lam params : [(String, String)]. externalZ3MkContext params

external externalZ3MkSolver : Z3Context -> Z3Solver
external externalZ3SolverAdd ! : Z3Solver -> Z3Expr -> ()
external externalZ3SolverReset ! : Z3Solver -> ()
external externalZ3SolverCheck : Z3Solver -> Z3SolverStatus
external externalZ3SolverStatusInt : Z3SolverStatus -> Int
external externalZ3SolverGetModel : Z3Solver -> Z3Model
let z3MkSolver = lam ctx : Z3Context. externalZ3MkSolver ctx
let z3SolverAdd = lam s : Z3Solver. lam e : Z3Expr. externalZ3SolverAdd s e
let z3SolverReset = lam s : Z3Solver. externalZ3SolverReset s
let z3SolverCheck = lam s : Z3Solver.
  let status : Z3SolverStatus = externalZ3SolverCheck s in
  let n = externalZ3SolverStatusInt status in
  if eqi n 0 then Z3Unsatisfiable ()
  else if eqi n 1 then Z3Unknown ()
  else if eqi n 2 then Z3Satisfiable ()
  else never
let z3SolverGetModel = lam s : Z3Solver. externalZ3SolverGetModel s

external externalZ3ModelGetConstInterpExpr : Z3Model -> Z3Expr -> Option Z3Expr
let z3ModelGetConstInterpExpr = lam m : Z3Model. lam e : Z3Expr.
  externalZ3ModelGetConstInterpExpr m e

external externalZ3SymbolMkString : Z3Context -> String -> Z3Symbol
let z3SymbolMkString = lam ctx : Z3Context. lam str : String.
  externalZ3SymbolMkString ctx str

external externalZ3ExprToString : Z3Expr -> String
let z3ExprToString = lam e : Z3Expr. externalZ3ExprToString e

external externalZ3MkInteger : Z3Context -> Z3Symbol -> Z3Expr
external externalZ3MkIntegerLiteral : Z3Context -> Int -> Z3Expr
let z3MkInteger = lam ctx : Z3Context. lam sym : Z3Symbol.
  externalZ3MkInteger ctx sym
let z3MkIntegerLiteral = lam ctx : Z3Context. lam i : Int.
  externalZ3MkIntegerLiteral ctx i

external externalZ3ArithmeticMkGt : Z3Context -> Z3Expr -> Z3Expr -> Z3Expr
external externalZ3ArithmeticMkAdd : Z3Context -> Z3Expr -> Z3Expr -> Z3Expr
external externalZ3ArithmeticMkSub : Z3Context -> Z3Expr -> Z3Expr -> Z3Expr
external externalZ3ArithmeticMkMul : Z3Context -> Z3Expr -> Z3Expr -> Z3Expr
let z3ArithmeticMkGt = lam ctx : Z3Context. lam lhs : Z3Expr. lam rhs : Z3Expr.
  externalZ3ArithmeticMkGt ctx lhs rhs
let z3ArithmeticMkAdd = lam ctx : Z3Context. lam lhs : Z3Expr. lam rhs : Z3Expr.
  externalZ3ArithmeticMkAdd ctx lhs rhs
let z3ArithmeticMkSub = lam ctx : Z3Context. lam lhs : Z3Expr. lam rhs : Z3Expr.
  externalZ3ArithmeticMkSub ctx lhs rhs
let z3ArithmeticMkMul = lam ctx : Z3Context. lam lhs : Z3Expr. lam rhs : Z3Expr.
  externalZ3ArithmeticMkMul ctx lhs rhs

external externalZ3BooleanMkEq : Z3Context -> Z3Expr -> Z3Expr -> Z3Expr
external externalZ3BooleanMkNot : Z3Context -> Z3Expr -> Z3Expr
let z3BooleanMkEq = lam ctx : Z3Context. lam lhs : Z3Expr. lam rhs : Z3Expr.
  externalZ3BooleanMkEq ctx lhs rhs
let z3BooleanMkNot = lam ctx : Z3Context. lam e : Z3Expr.
  externalZ3BooleanMkNot ctx e

mexpr

let ctx = z3MkContext [] in
let solver = z3MkSolver ctx in
let asym = z3SymbolMkString ctx "a" in
let a = z3MkInteger ctx asym in
let bsym = z3SymbolMkString ctx "b" in
let b = z3MkInteger ctx bsym in
let csym = z3SymbolMkString ctx "c" in
let c = z3MkInteger ctx csym in

-- Solve the system:
-- a + a = 10
-- a * b + b = 12
-- a * b - c * a = a
let ten = z3MkIntegerLiteral ctx 10 in
let twelve = z3MkIntegerLiteral ctx 12 in
let fst = z3ArithmeticMkAdd ctx a a in
let snd = z3ArithmeticMkAdd ctx (z3ArithmeticMkMul ctx a b) b in
let trd =
  z3ArithmeticMkSub ctx
    (z3ArithmeticMkMul ctx a b)
    (z3ArithmeticMkMul ctx c a) in
z3SolverAdd solver (z3BooleanMkEq ctx fst ten) ;
z3SolverAdd solver (z3BooleanMkEq ctx snd twelve) ;
z3SolverAdd solver (z3BooleanMkEq ctx trd a) ;

let status : Z3SolverResult = z3SolverCheck solver in
utest status with Z3Satisfiable () in

let model : Z3Model = z3SolverGetModel solver in

let getStringValue = lam var : Z3Expr.
  -- Interpret the value of the variable in the model
  match z3ModelGetConstInterpExpr model var with Some e then
    z3ExprToString e
  else never
in

-- The above system has solution a = 5, b = 2, c = 1
utest getStringValue a with "5" using eqString in
utest getStringValue b with "2" using eqString in
utest getStringValue c with "1" using eqString in

()
