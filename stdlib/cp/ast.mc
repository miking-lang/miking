-- AST representation of a constraint optimization or satisfaction problem
-- (COP/CSP).

-- TODO(vipa, 2023-04-21): int set domain
-- TODO(vipa, 2023-04-21): functions and predicates (plus applications thereof)
-- TODO(vipa, 2023-04-21): multiplication
-- TODO(vipa, 2023-04-21): if-then-else
-- TODO(vipa, 2023-04-21): equality and boolean operators
-- TODO(vipa, 2023-04-21): table? might be present already

-- TODO(vipa, 2023-04-21): "looping" constructs, forall & sum

include "name.mc"

----------------------------
-- BASE LANGUAGE FRAGMENT --
----------------------------

lang COPAst
  type COPModel = [COPDecl]

  syn COPDecl =
  syn COPDomain =
  syn COPExpr =
end

-------------
-- DOMAINS --
-------------

lang COPDomainIntRangeAst = COPAst
  syn COPDomain =
  | COPDomainIntRange { min: COPExpr, max: COPExpr }
end

lang COPDomainBooleanAst = COPAst
  syn COPDomain =
  | COPDomainBoolean {}
end

lang COPDomainSetAst = COPAst
  syn COPDomain =
  | COPDomainSet { values : [COPExpr] }
end

---------------
-- VARIABLES --
---------------

lang COPVarDeclAst = COPAst
  syn COPDecl =
  | COPVarDecl { id: Name,
                 domain: COPDomain }
end

lang COPVarArrayDeclAst = COPAst
  syn COPDecl =
  | COPVarArrayDecl { id: Name,
                      domain: COPDomain,
                      length: COPExpr }
end

-----------------
-- CONSTRAINTS --
-----------------

lang COPConstraintDeclAst = COPAst
  syn COPConstraint =
  syn COPDecl =
  | COPConstraintDecl { constraint: COPConstraint }
end

lang COPConstraintDeclExprAst = COPAst
  syn COPDecl =
  | COPConstraintDeclExpr { constraint : COPExpr }
end

-- Table constraint
lang COPConstraintTableAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintTable { vars: COPExpr, tuples: COPExpr }
end

-- Reified table constraint: table('vars', 'tuples') <=> 'b'
lang COPConstraintTableReifAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintTableReif { vars: COPExpr, tuples: COPExpr, b: COPExpr }
end

-- Constrain 'lhs' to be smaller or equal to 'rhs'
lang COPConstraintLEAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintLE { lhs: COPExpr, rhs: COPExpr }
end

-- Constrain 'lhs' to be smaller than 'rhs'
lang COPConstraintLTAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintLT { lhs: COPExpr, rhs: COPExpr }
end

----------------
-- OBJECTIVES --
----------------

lang COPObjectiveDeclAst = COPAst
  syn COPObjective =
  syn COPDecl =
  | COPObjectiveDecl { objective: COPObjective }
end

lang COPObjectiveMinimizeAst = COPObjectiveDeclAst
  syn COPObjective =
  | COPObjectiveMinimize { expr: COPExpr }
end

-----------------
-- EXPRESSIONS --
-----------------

lang COPExprSumAst = COPAst
  syn COPExpr =
  | COPExprSum { expr: COPExpr }
end

lang COPExprVarAst = COPAst
  syn COPExpr =
  | COPExprVar { id: Name }
end

lang COPExprVarAccessAst = COPAst
  syn COPExpr =
  | COPExprVarAccess { id: Name, index: COPExpr }
end

lang COPExprIntAst = COPAst
  syn COPExpr =
  | COPExprInt { value: Int }
end

lang COPExprFloatAst = COPAst
  syn COPExpr =
  | COPExprFloat { value: Float }
end

lang COPExprBoolAst = COPAst
  syn COPExpr =
  | COPExprBool { value: Bool }
end

lang COPExprArrayAst = COPAst
  syn COPExpr =
  | COPExprArray { array: [COPExpr] }
end

lang COPExprArray2dAst = COPAst
  syn COPExpr =
  | COPExprArray2d { array: [[COPExpr]] }
end

lang COPExprAddAst = COPAst
  syn COPExpr =
    | COPExprAdd { exprs: [COPExpr] }
end

lang COPExprSubAst = COPAst
  syn COPExpr =
  | COPExprSub { left: COPExpr, right: COPExpr }
end

lang COPExprMulAst = COPAst
  syn COPExpr =
  | COPExprMul { exprs: [COPExpr] }
end

lang COPExprDivAst = COPAst
  syn COPExpr =
  | COPExprDiv { left: COPExpr, right: COPExpr }
end

lang COPExprEqAst = COPAst
  syn COPExpr =
  | COPExprEq { left: COPExpr, right: COPExpr }
end

lang COPExprNeAst = COPAst
  syn COPExpr =
  | COPExprNe { left: COPExpr, right: COPExpr }
end

lang COPExprLeAst = COPAst
  syn COPExpr =
  | COPExprLe { left: COPExpr, right: COPExpr }
end

lang COPExprGeAst = COPAst
  syn COPExpr =
  | COPExprGe { left: COPExpr, right: COPExpr }
end

lang COPExprLtAst = COPAst
  syn COPExpr =
  | COPExprLt { left: COPExpr, right: COPExpr }
end

lang COPExprGtAst = COPAst
  syn COPExpr =
  | COPExprGt { left: COPExpr, right: COPExpr }
end

lang COPExprAndAst = COPAst
  syn COPExpr =
  | COPExprAnd { exprs: [COPExpr] }
end

lang COPExprOrAst = COPAst
  syn COPExpr =
  | COPExprOr { exprs: [COPExpr] }
end

lang COPExprNotAst = COPAst
  syn COPExpr =
  | COPExprNot { expr: COPExpr }
end

lang COPExprIfThenElseAst = COPAst
  syn COPExpr =
  | COPExprIfThenElse { cond : COPExpr, ifTrue : COPExpr, ifFalse : COPExpr }
end

----------------------
-- COP AST FRAGMENT --
----------------------

lang COP =
  -- Domains --
  COPDomainIntRangeAst + COPDomainBooleanAst + COPDomainSetAst +
  -- Variables --
  COPVarDeclAst + COPVarArrayDeclAst +
  -- Constraints --
  COPConstraintDeclAst + COPConstraintTableAst + COPConstraintTableReifAst +
  COPConstraintLEAst + COPConstraintLTAst + COPConstraintDeclExprAst +
  -- Objectives --
  COPObjectiveDeclAst + COPObjectiveMinimizeAst +
  -- Expressions --
  COPExprSumAst + COPExprVarAst + COPExprVarAccessAst + COPExprIntAst +
  COPExprFloatAst + COPExprBoolAst +
  COPExprArrayAst + COPExprArray2dAst +
  COPExprAddAst + COPExprSubAst + COPExprMulAst + COPExprDivAst +
  COPExprGtAst + COPExprLtAst + COPExprGeAst + COPExprLeAst + COPExprNeAst + COPExprEqAst +
  COPExprAndAst + COPExprOrAst + COPExprNotAst + COPExprIfThenElseAst
end
