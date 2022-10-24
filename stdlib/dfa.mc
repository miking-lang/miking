include "nfa.mc"

-- Represents a deterministic finite automaton.
-- Equality and print functions are required for
-- the states (eqv,s2s) and labels (eql,l2s) for the
-- construct function (dfaConstr).

-- States are represented by a vertex in a directed graph.
-- They are unique values, there cannot be two states
-- whose value of the equality function is true.

-- transitions are represented as edges in a directed graph
-- (digraph), where the vertices are states. All labels between two states
-- also has to be unique.

-- adds syntactic sugar for DFA type
-- DFA is based on the same data types as the NFA
type DFA v l = NFA v l

-- check for specific duplicate label
recursive
let checkSpecificDuplicate : all v. all l.
  DigraphEdge v l -> [DigraphEdge v l] -> (v -> v -> Bool) -> (l -> l -> Bool) -> Bool =
  lam trans. lam rest. lam eqv. lam eql.
  if(eqi (length rest) 0) then false
  else
  let first = head rest in
  let rest = tail rest in
  if(and (eqv first.0 trans.0) (eql first.2 trans.2)) then true
  else checkSpecificDuplicate trans rest eqv eql
end

-- check for duplicate labels
recursive
let checkDuplicateLabels : all v. all l.
  [DigraphEdge v l] -> (v -> v -> Bool) -> (l -> l -> Bool) -> Option (v, l) =
  lam trans. lam eqv. lam eql.
  if (leqi (length trans) 1) then None ()
  else
  let first = head trans in
  let rest = tail trans in
  if(checkSpecificDuplicate first rest eqv eql) then Some (first.0, first.2)
  else
  checkDuplicateLabels rest eqv eql
end

-- constructor for the DFA
let dfaConstr = lam s. lam trans. lam startS. lam accS. lam cmpv. lam eql.
  let eqv = lam v1. lam v2. eqi (cmpv v1 v2) 0 in
	match checkDuplicateLabels trans eqv eql with
	Some _ then error "There are duplicate labels for same state outgoing transition at"
	else nfaConstr s trans startS accS cmpv eql

-- Creat a DFA from a Digraph
let dfaFromDigraph = nfaFromDigraph

mexpr
let states = [0,1,2] in
let transitions = [(0,1,'1'),(1,1,'1'),(1,2,'0'),(2,2,'0'),(2,1,'1')] in
let startState = 0 in
let acceptStates = [2] in
let newDfa = dfaConstr states transitions startState acceptStates subi eqChar in
utest eqi startState newDfa.startState with true in
utest eqsetEqual eqi acceptStates newDfa.acceptStates with true in
utest (digraphHasVertices states newDfa.graph) with true in
utest (digraphHasEdges transitions newDfa.graph) with true in
utest (digraphHasEdges [(1,2,'1')] (nfaAddTransition newDfa (1,2,'1')).graph) with true in
utest (digraphHasVertex 7 (nfaAddState newDfa 7).graph) with true in
utest nfaIsAcceptedState 2 newDfa with true in
utest nfaIsAcceptedState 3 newDfa with false in ()
