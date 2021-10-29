-- CFA framework for MExpr. Currently, only 0-CFA (context insensitive) is
-- supported. The algorithm is based on Table 3.7 in the book "Principles of
-- Program Analysis" (Nielson et al.).

include "set.mc"

-- OPT(dlunde,2021-10-29): Map all names in analyzed program to integers 0,1,...,#variables-1
-- to speed up analysis? Or, use a hash table?

-- Extensible types (syn)
-- * Abstract values. By default, this will only contain term names (for, e.g., functions).
-- * Constraints. By default, we have direct constraints and implication constraints

-- Required data structures for algorithm
-- * A set of constraints (Could possibly just be a list?)
-- * A sequence W containing nodes for which constraints must be propagated.
-- * A data tensor D such that D[n] is a set of abstract values.
-- * Edge tensor E encoding constraints for each node.

-- Semantic functions (sem)
-- * Generate constraints from a program
-- * Build the graph from constraints
-- * Propagate constraints

type CFAGraph = {
  constraints: [Constraint],
  worklist: [Name],
  data: Map Name (Set AbsVal),
  edges: Map Name [Constraint]
}

lang CFA = ...

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  sem generateConstraints =
  -- Intentionally left blank
  | -- sfold as default?

  sem initCFA (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (graph: CFAGraph) =
  -- Intentionally left blank

end
