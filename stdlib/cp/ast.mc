-- AST representation of a constraint optimization or satisfaction problem
-- (COP/CSP).

include "name.mc"

----------------------------
-- BASE LANGUAGE FRAGMENT --
----------------------------

lang COPAst
  type COPModel = {
    decls: [COPDecl],
    objective: COPObjective
  }

  syn COPDecl =
  syn COPDomain =
  syn COPExpr =
  syn COPObjective =

  sem isOptimizationModel: COPModel -> Bool
  sem isOptimizationModel =
  | m -> isOptimization m.objective

  sem isOptimization: COPObjective -> Bool
  sem isOptimization =
  | _ -> false
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

lang COPObjectiveMinimizeAst = COPAst
  syn COPObjective =
  | COPMinimize { expr: COPExpr }

  sem isOptimization =
  | COPMinimize _ -> true
end

lang COPObjectiveMaximizeAst = COPAst
  syn COPObjective =
  | COPMaximize { expr: COPExpr }

  sem isOptimization =
  | COPMaximize _ -> true
end

lang COPObjectiveSatisfyAst = COPAst
  syn COPObjective =
  | COPSatisfy {}
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
  COPConstraintDeclAst + COPConstraintTableAst + COPConstraintTableReifAst +
  COPConstraintLEAst + COPConstraintLTAst +
  -- Objectives --
  COPObjectiveMinimizeAst + COPObjectiveMaximizeAst + COPObjectiveSatisfyAst +
  -- Expressions --
  COPExprSumAst + COPExprVarAst + COPExprVarAccessAst + COPExprIntAst +
  COPExprArrayAst + COPExprArray2dAst
end
