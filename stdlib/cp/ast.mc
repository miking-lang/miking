-- AST representation of a constraint optimization or satisfaction problem
-- (COP/CSP).

-- NOTE(Linnea, 2023-02-08): Arrays are indexed from 1.

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

-- Table constraint
lang COPConstraintTableAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintTable { vars: COPExpr, tuples: COPExpr }
end

-- Constrain 'lhs' to be smaller or equal to 'rhs'
lang COPConstraintLEAst = COPConstraintDeclAst
  syn COPConstraint =
  | COPConstraintLE { lhs: COPExpr, rhs: COPExpr }
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

lang COPExprArrayAst = COPAst
  syn COPExpr =
  | COPExprArray { array: [COPExpr] }
end

lang COPExprArray2dAst = COPAst
  syn COPExpr =
  | COPExprArray2d { array: [[COPExpr]] }
end

----------------------
-- COP AST FRAGMENT --
----------------------

lang COP =
  -- Domains --
  COPDomainIntRangeAst + COPDomainBooleanAst +
  -- Variables --
  COPVarDeclAst + COPVarArrayDeclAst +
  -- Constraints --
  COPConstraintDeclAst + COPConstraintTableAst + COPConstraintLEAst +
  -- Objectives --
  COPObjectiveDeclAst + COPObjectiveMinimizeAst +
  -- Expressions --
  COPExprSumAst + COPExprVarAst + COPExprVarAccessAst + COPExprIntAst +
  COPExprArrayAst + COPExprArray2dAst
end
