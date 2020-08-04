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
type DFA = NFA


-- check for specific duplicate label
recursive
let checkSpecificDuplicate = lam trans. lam rest. lam eqv. lam eql.
    if(eqi (length rest) 0) then false
    else
    let first = head rest in
    let rest = tail rest in
    if(and (eqv first.0 trans.0) (eql first.2 trans.2)) then true
    else checkSpecificDuplicate trans rest eqv eql
end

-- check for duplicate labels
recursive
let checkDuplicateLabels = lam trans. lam eqv. lam eql.
    if(eqi (length trans) 1) then (false, (0,0))
    else
    let first = head trans in
    let rest = tail trans in
    if(checkSpecificDuplicate first rest eqv eql) then (true, (first.0, first.2))
    else
    checkDuplicateLabels rest eqv eql
end
    
-- constructor for the DFA
let dfaConstr = lam s. lam trans. lam alph. lam startS. lam accS. lam eqv. lam eql.
	let err = checkDuplicateLabels trans eqv eql in
	if(err.0) then error "There are duplicate labels for same state outgoing transition at"
	else nfaConstr s trans alph startS accS eqv eql

 

mexpr
let alphabet = ['0','1'] in
let states = [0,1,2] in
let transitions = [(0,1,'1'),(1,1,'1'),(1,2,'0'),(2,2,'0'),(2,1,'1')] in
let startState = 0 in
let acceptStates = [2] in
let newDfa = dfaConstr states transitions alphabet startState acceptStates eqi eqchar in
utest setEqual eqchar alphabet newDfa.alphabet with true in
utest eqi startState newDfa.startState with true in
utest setEqual eqi acceptStates newDfa.acceptStates with true in
utest (digraphHasVertices states newDfa.graph) with true in
utest (digraphHasEdges transitions newDfa.graph) with true in
utest nfaCheckLabels transitions alphabet eqchar with true in
utest nfaCheckLabels [(1,2,'2')] alphabet eqchar with false in
utest (digraphHasEdges [(1,2,'1')] (nfaAddTransition newDfa (1,2,'1')).graph) with true in
utest (digraphHasVertex 7 (nfaAddState newDfa 7).graph) with true in
utest nfaIsAcceptedState 2 newDfa with true in
utest nfaIsAcceptedState 3 newDfa with false in
utest nfaNextStates 1 newDfa.graph '0' with [2] in
-- Not accepted
utest nfaMakeInputPath (negi 1) newDfa.startState "1011" newDfa with
    [{status = "",state = 0,index = negi 1},
    {status = "",state = 1,index = 0},
    {status = "",state = 2,index = 1},
    {status = "",state = 1,index = 2},
    {status = "not accepted",state = 1,index = 3}] in
-- Accepted
utest nfaMakeInputPath (negi 1) newDfa.startState "10110" newDfa with
    [{status = "",state = 0,index = negi 1},
    {status = "",state = 1,index = 0},
    {status = "",state = 2,index = 1},
    {status = "",state = 1,index = 2},
    {status = "",state = 1,index = 3},
    {status = "accepted",state = 2,index = 4}] in
-- Invalid transition
utest nfaMakeInputPath (negi 1) newDfa.startState "0110" newDfa with
    [{status = "stuck",state = 0,index = negi 1}] in
-- Input of length 0
utest nfaMakeInputPath (negi 1) newDfa.startState "" newDfa with 
    [{status = "not accepted", state = 0, index = negi 1}] in
()

