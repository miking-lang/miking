-- Pretty printing of a COP/CSP as a MiniZinc model.

include "ast.mc"
include "common.mc"
include "mexpr/pprint.mc"

lang COPPrettyPrintBase = COPAst + IdentifierPrettyPrint
  sem pprintCOPModel: COPModel -> (PprintEnv, String)
  sem pprintCOPModel =
  | {decls = decls, objective = objective} ->
    match mapAccumL (lam env. lam d. pprintCOPDecl env d) pprintEnvEmpty decls
    with (env, decls) in
    match pprintCOPObjective env objective
    with (env, objective) in
    (env, strJoin "\n" (snoc decls objective))

  sem pprintCOPDecl: PprintEnv -> COPDecl -> (PprintEnv, String)
  sem pprintCOPDomain: PprintEnv -> COPDomain -> (PprintEnv, String)
  sem pprintCOPExpr: PprintEnv -> COPExpr -> (PprintEnv, String)
  sem pprintCOPObjective: PprintEnv -> COPObjective -> (PprintEnv, String)

  -- NOTE(Linnea, 2023-02-08): Assumes that the base string of the name is a
  -- valid MiniZinc identifier (not a MiniZinc keyword, etc.).
  sem pprintVarName : PprintEnv -> Name -> (PprintEnv, String)
  sem pprintVarName env =
  | name ->
    pprintEnvGetStr env name
end

-------------
-- DOMAINS --
-------------

lang COPDomainIntRangePrettyPrint = COPPrettyPrintBase + COPDomainIntRangeAst
  sem pprintCOPDomain env =
  | COPDomainIntRange {min = min, max = max} ->
    match pprintCOPExpr env min with (env, min) in
    match pprintCOPExpr env max with (env, max) in
    (env, join [min, "..", max])
end

lang COPDomainBooleanPrettyPrint = COPPrettyPrintBase + COPDomainBooleanAst
  sem pprintCOPDomain env =
  | COPDomainBoolean {} -> (env, "bool")
end

---------------
-- VARIABLES --
---------------

lang COPVarDeclPrettyPrint = COPPrettyPrintBase + COPVarDeclAst
  sem pprintCOPDecl env =
  | COPVarDecl {id = id, domain = domain } ->
    match pprintVarName env id with (env, id) in
    match pprintCOPDomain env domain with (env, domain) in
    (env, join ["var ", domain, ": ", id, ";"])
end

lang COPVarArrayDeclPrettyPrint = COPPrettyPrintBase + COPVarArrayDeclAst
  sem pprintCOPDecl env =
  | COPVarArrayDecl {id = id, domain = domain, length = length} ->
    match pprintVarName env id with (env, id) in
    match pprintCOPExpr env length with (env, length) in
    match pprintCOPDomain env domain with (env, domain) in
    (env, join ["array [1..", length, "] of var ", domain, ": ", id, ";"])
end

-----------------
-- CONSTRAINTS --
-----------------

lang COPConstraintDeclPrettyPrint = COPPrettyPrintBase + COPConstraintDeclAst
  sem pprintCOPConstraint: PprintEnv -> COPConstraint ->
                           (PprintEnv, Option String, String)
  sem pprintCOPDecl env =
  | COPConstraintDecl { constraint = constraint } ->
    match pprintCOPConstraint env constraint with (env, incl, str) in
    ( env, join [optionMapOr "" (lam i. join ["include \"", i, "\";\n"]) incl,
                 "constraint ", str, ";"])
end

lang COPConstraintTablePrettyPrint = COPConstraintDeclPrettyPrint + COPConstraintTableAst
  sem pprintCOPConstraint env =
  | COPConstraintTable { vars = vars, tuples = tuples } ->
    match pprintCOPExpr env vars with (env, vars) in
    match pprintCOPExpr env tuples with (env, tuples) in
    ( env, Some "table.mzn", join ["table(", vars, ",", tuples, ")"] )
end

lang COPConstraintTableReifPrettyPrint = COPConstraintDeclPrettyPrint + COPConstraintTableReifAst
  sem pprintCOPConstraint env =
  | COPConstraintTableReif { vars = vars, tuples = tuples, b = b } ->
    match pprintCOPExpr env vars with (env, vars) in
    match pprintCOPExpr env tuples with (env, tuples) in
    match pprintCOPExpr env b with (env, b) in
    ( env, Some "table.mzn", join ["table(", vars, ",", tuples, ") <-> ", b] )
end

lang COPConstraintLEPrettyPrint = COPConstraintDeclPrettyPrint + COPConstraintLEAst
  sem pprintCOPConstraint env =
  | COPConstraintLE { lhs = lhs, rhs = rhs } ->
    match pprintCOPExpr env lhs with (env, lhs) in
    match pprintCOPExpr env rhs with (env, rhs) in
    ( env, None (), join [lhs, " <= ", rhs] )
end

lang COPConstraintLTPrettyPrint = COPConstraintDeclPrettyPrint + COPConstraintLTAst
  sem pprintCOPConstraint env =
  | COPConstraintLT { lhs = lhs, rhs = rhs } ->
    match pprintCOPExpr env lhs with (env, lhs) in
    match pprintCOPExpr env rhs with (env, rhs) in
    ( env, None (), join [lhs, " < ", rhs] )
end

----------------
-- OBJECTIVES --
----------------

lang COPObjectivePrettyPrint = COPPrettyPrintBase
  sem pprintCOPObjectiveH: PprintEnv -> COPObjective -> (PprintEnv, String)
  sem pprintCOPObjective env =
  | obj ->
    match pprintCOPObjectiveH env obj with (env, obj) in
    (env, join ["solve ", obj, ";"])
end

lang COPObjectiveMinimizePrettyPrint = COPObjectivePrettyPrint
                                     + COPObjectiveMinimizeAst
  sem pprintCOPObjectiveH env =
  | COPMinimize { expr = expr } ->
    match pprintCOPExpr env expr with (env, expr) in
    (env, concat "minimize " expr)
end

lang COPObjectiveMaximizePrettyPrint = COPObjectivePrettyPrint
                                     + COPObjectiveMaximizeAst
  sem pprintCOPObjectiveH env =
  | COPMaximize { expr = expr } ->
    match pprintCOPExpr env expr with (env, expr) in
    (env, concat "maximize " expr)
end

lang COPObjectiveSatisfyPrettyPrint = COPObjectivePrettyPrint
                                    + COPObjectiveSatisfyAst
  sem pprintCOPObjectiveH env =
  | COPSatisfy {} -> (env, "satisfy")
end

-----------------
-- EXPRESSIONS --
-----------------

lang COPExprSumPrettyPrint = COPPrettyPrintBase + COPExprSumAst
  sem pprintCOPExpr env =
  | COPExprSum { expr = expr } ->
    match pprintCOPExpr env expr with (env, expr) in
    (env, join ["sum(", expr, ")"])
end

lang COPExprVarPrettyPrint = COPPrettyPrintBase + COPExprVarAst
  sem pprintCOPExpr env =
  | COPExprVar { id = id } -> pprintVarName env id
end

lang COPExprVarAccessPrettyPrint = COPPrettyPrintBase + COPExprVarAccessAst
  sem pprintCOPExpr env =
  | COPExprVarAccess { id = id, index = index } ->
    match pprintVarName env id with (env, id) in
    match pprintCOPExpr env index with (env, index) in
    (env, join [id, "[", index, "]"])
end

lang COPExprIntPrettyPrint = COPPrettyPrintBase + COPExprIntAst
  sem pprintCOPExpr env =
  | COPExprInt { value = value } -> (env, int2string value)
end

lang COPExprArrayPrettyPrint = COPPrettyPrintBase + COPExprArrayAst
  sem pprintCOPExpr env =
  | COPExprArray { array = array } ->
    match mapAccumL (lam env. lam e. pprintCOPExpr env e) env array
    with (env, array) in
    (env, join ["[", strJoin "," array, "]"])
end

lang COPExprArray2dPrettyPrint = COPPrettyPrintBase + COPExprArray2dAst
  sem pprintCOPExpr env =
  | COPExprArray2d { array = array } ->
    match mapAccumL (lam env. lam inner.
        match mapAccumL (lam env. lam e. pprintCOPExpr env e) env inner
        with (env, inner) in
        (env, strJoin "," inner)
      ) env array
    with (env, array) in
    (env, join ["[|", strJoin "|" array, "|]"])
end


-------------------------------
-- COP PRETTY PRINT FRAGMENT --
-------------------------------

lang COPPrettyPrint =
  -- Domains --
  COPDomainIntRangePrettyPrint + COPDomainBooleanPrettyPrint +
  -- Variables --
  COPVarDeclPrettyPrint + COPVarArrayDeclPrettyPrint +
  -- Constraints --
  COPConstraintDeclPrettyPrint + COPConstraintTablePrettyPrint +
  COPConstraintTableReifPrettyPrint + COPConstraintLEPrettyPrint +
  COPConstraintLTPrettyPrint +
  -- Objectives --
  COPObjectiveMinimizePrettyPrint + COPObjectiveMaximizePrettyPrint +
  COPObjectiveSatisfyPrettyPrint +
  -- Expressions --
  COPExprSumPrettyPrint + COPExprVarPrettyPrint + COPExprVarAccessPrettyPrint +
  COPExprIntPrettyPrint + COPExprArrayPrettyPrint + COPExprArray2dPrettyPrint
end

mexpr

use COPPrettyPrint in

-- Enable debug printing
let debug = false in

let cpInt_ = lam i. COPExprInt {value = i} in

let eqTest = lam lhs: COPModel. lam rhs: String.
  match pprintCOPModel lhs with (_, lhs) in
  let lhs = strTrim lhs in
  let rhs = strTrim rhs in
  (if debug then
     printLn "\n*** LHS ***";
     printLn lhs;
     printLn "\n*** RHS ***";
     printLn rhs
   else ());
  eqString lhs rhs
in


utest
  let x = nameSym "x" in
  let y = nameSym "y" in
  {
    decls = [
      COPVarArrayDecl {
         id = x,
         domain = COPDomainIntRange {min = cpInt_ 1, max = cpInt_ 10},
         length = cpInt_ 5
       },
       COPVarDecl {id = y, domain = COPDomainBoolean {}},
       COPConstraintDecl {constraint = COPConstraintLE {
         lhs = COPExprVarAccess {id = x, index = cpInt_ 1},
         rhs = COPExprVarAccess {id = x, index = cpInt_ 2}}}],

    objective = COPMinimize {
      expr = COPExprSum {expr = COPExprArray {
      array = [COPExprVarAccess {id = x, index = cpInt_ 1},
               COPExprVarAccess {id = x, index = cpInt_ 2},
               COPExprVar {id = y}]}}}
  }
with
"
array [1..5] of var 1..10: x;
var bool: y;
constraint x[1] <= x[2];
solve minimize sum([x[1],x[2],y]);
"
using eqTest in

utest
  let x = nameSym "x" in
  let y = nameSym "y" in
  let zero = cpInt_ 0 in
  let one = cpInt_ 1 in
  {
    decls = [
      COPVarArrayDecl {
        id = x,
        domain = COPDomainIntRange {min = cpInt_ 0, max = cpInt_ 1},
        length = cpInt_ 3},
      COPVarDecl {id = y, domain = COPDomainBoolean {}},
      COPConstraintDecl {constraint = COPConstraintTable {
        vars = COPExprVar {id = x},
        tuples = COPExprArray2d {array = [[zero,zero,one],[one,zero,one],[zero,zero,zero]]}
      }},
      COPConstraintDecl {constraint = COPConstraintTableReif {
        vars = COPExprVar {id = x},
        tuples = COPExprArray2d {array = [[zero,zero,one],[one,zero,one]]},
        b = COPExprVar {id = y}
      }}],
    objective = COPMinimize {expr = COPExprSum {expr = COPExprVar {id = x}}}
  }
with
"
array [1..3] of var 0..1: x;
var bool: y;
include \"table.mzn\";
constraint table(x,[|0,0,1|1,0,1|0,0,0|]);
include \"table.mzn\";
constraint table(x,[|0,0,1|1,0,1|]) <-> y;
solve minimize sum(x);
"
using eqTest in

utest
  let x = nameSym "x" in
  {
    decls = [COPVarDecl {id = x, domain = COPDomainBoolean {}}],
    objective = COPSatisfy {}
  }
with
"
var bool: x;
solve satisfy;
"
using eqTest in

()
