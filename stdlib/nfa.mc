include "graph.mc"
include "char.mc"
include "string.mc"

-- Represents a nondeterministic finite automaton
-- Equality and print functions are required for
-- the states (eqv,s2s) and labels (eql,l2s) for the
-- construct function (nfaConstr).

-- States are represented by a vertex in a directed graph.
-- They are unique, there cannot be two states whose value of the
-- equality function is true.

-- transitions are represented as edges in a directed graph
-- (digraph), where the vertices are states.

type NFA v l  = {
  graph: Digraph v l,
  startState: v,
  acceptStates: [v]
}

-- get equality function for states
let nfaGetEqv : all v. all l. NFA v l -> v -> v -> Bool = lam dfa.
  digraphEqv dfa.graph

-- get comparison function for states
let nfaGetCmp : all v. all l. NFA v l -> v -> v -> Int = lam dfa.
  digraphCmpv dfa.graph

-- get equality functions for labels
let nfaGetEql : all v. all l. NFA v l -> l -> l -> Bool = lam dfa.
  dfa.graph.eql

-- get all states in nfa
let nfaStates : all v. all l. NFA v l -> [v] = lam nfa.
  digraphVertices nfa.graph

-- get all transitions in nfa
let nfaTransitions : all v. all l. NFA v l -> [DigraphEdge v l] = lam nfa.
  digraphEdges nfa.graph

-- get start state of the nfa
let nfaStartState : all v. all l. NFA v l -> v = lam nfa.
  nfa.startState

-- get the accept states in the nfa
let nfaAcceptStates : all v. all l. NFA v l -> [v] = lam nfa.
  nfa.acceptStates

-- get all transitions from state s1 to state s2
let nfaTransitionsBetween : all v. all l. v -> v -> NFA v l -> [DigraphEdge v l] =
  lam s1. lam s2. lam nfa.
  digraphEdgesBetween s1 s2 nfa.graph

-- get all predecessor states to state s
let nfaInStates : all v. all l. v -> NFA v l -> [v] = lam s. lam nfa.
  digraphPredeccessors s nfa.graph

-- get all successor states to state s
let nfaOutStates : all v. all l. v -> NFA v l -> [v] = lam s. lam nfa.
  digraphSuccessors s nfa.graph

-- check that values are acceptable for the NFA
let nfaCheckValues = lam trans. lam s. lam eqv. lam eql. lam accS. lam startS.
  if not (setIsSubsetEq eqv accS s) then error "Some accepted states do not exist"
  else if not (eqsetMem eqv startS s) then error "The start state does not exist"
  else ()

-- States are represented by vertices in a directed graph
let nfaAddState : all v. all l. NFA v l -> v -> NFA v l =  lam nfa. lam state.
  {
    graph = (digraphAddVertex state nfa.graph),
    startState = nfa.startState,
    acceptStates = nfa.acceptStates
  }

-- Transitions between two states are represented by edges between vertices
let nfaAddTransition : all v. all l. NFA v l -> DigraphEdge v l -> NFA v l =
  lam nfa. lam trans.
  let states = nfaStates nfa in
  let from = trans.0 in
  let to = trans.1 in
  let label = trans.2 in
  {
    graph = (digraphAddEdge from to label nfa.graph),
    startState = nfa.startState,
    acceptStates = nfa.acceptStates
  }

-- returns true if state s is an accepted state in the nfa
let nfaIsAcceptedState : all v. all l. v -> NFA v l -> Bool = lam s. lam nfa.
  eqsetMem (digraphEqv nfa.graph) s nfa.acceptStates

-- check if there is a transition with label lbl from state s
let nfaStateHasTransition : all v. all l. v -> Digraph v l -> l -> Bool =
  lam s. lam trans. lam lbl.
  let neighbors = digraphEdgesFrom s trans in
  --check if lbl is a label in the neighbors list
  eqsetMem trans.eql lbl (map (lam x. x.2) neighbors)

-- get next state from state s with label lbl. Throws error if no transition is found
let nfaNextStates : all v. all l. v -> Digraph v l -> l -> [v] =
  lam from. lam graph. lam lbl.
  let neighbors = digraphEdgesFrom from graph in
  let matches = filter (lam x. graph.eql x.2 lbl) neighbors in
  let neighboringStates = map (lam x. x.1) matches in
  match matches with [] then
  error "No transition was found"
  else neighboringStates

-- goes through the nfa, one state of the input at a time. Returns a list of {state, status, input}
-- where status is either accepted,stuck,not accepted or neutral ("")
recursive
let nfaMakeInputPath : all v. all l.
  Int -> v -> [l] -> NFA v l -> [{state : v, index : Int, status : String}] =
  lam i. lam currentState. lam input. lam nfa.
  let pathIsAccepted = lam path.
    if null path then false
    else (eqsetEqual eqChar (last path).status "accepted")
  in
  if (eqi (length input) 0) then
    if (nfaIsAcceptedState currentState nfa) then [{state = currentState,index = i, status = "accepted"}]
    else [{state = currentState, index = i, status = "not accepted"}]
  -- check if transition exists. If yes, go to next state
  else if nfaStateHasTransition currentState nfa.graph (head input) then
    foldl (lam path. lam elem.
      if (pathIsAccepted path) then path
      else
        let config = [{state = currentState,index = i, status = ""}] in
        join [path, config, nfaMakeInputPath (addi i 1) elem (tail input) nfa]
    ) [] (nfaNextStates currentState nfa.graph (head input))
  else [{state = currentState, index = i, status = "stuck"}]
end

recursive
let nfaMakeEdgeInputPath : all v. all l. v -> [l] -> NFA v l -> [(v, v)] =
  lam currentState. lam input. lam nfa.
  if (eqi (length input) 0) then []
  -- check if transition exists. If yes, go to next state
  else if nfaStateHasTransition currentState nfa.graph (head input) then
    foldl (lam path. lam elem.
      join [path, [(currentState,elem)], nfaMakeEdgeInputPath elem (tail input) nfa]
    ) [] (nfaNextStates currentState nfa.graph (head input))
  else []
end

-- constructor for the NFA
let nfaConstr = lam s. lam trans. lam startS. lam accS. lam cmpv. lam eql.
  let eqv = lam v1. lam v2. eqi (cmpv v1 v2) 0 in
  nfaCheckValues trans s eqv eql accS startS;
  let emptyDigraph = digraphEmpty cmpv eql in
  let initNfa = {
    graph = emptyDigraph,
    startState = startS,
    acceptStates = accS
  } in
  foldl nfaAddTransition (foldl nfaAddState initNfa s) trans

-- Create an NFA from a Digraph
let nfaFromDigraph = lam g. lam startS. lam accS.
  nfaConstr (digraphVertices g) (digraphEdges g) startS accS (digraphCmpv g) (digraphEql g)

mexpr
let states = [0,1,2] in
let states2 = [0,1,2,3,4] in
let transitions = [(0,1,'1'),(1,1,'1'),(1,2,'0'),(2,2,'0'),(2,1,'1')] in
let transitions2 = [(0,1,'1'),(1,3,'1'),(1,2,'1')] in
let startState = 0 in
let acceptStates = [2] in
let newNfa = nfaConstr states transitions startState acceptStates subi eqChar in
let newNfa2 = nfaConstr states2 transitions2 startState acceptStates subi eqChar in
let newNfa3 = nfaConstr states2 transitions2 startState [3] subi eqChar in
utest eqi startState newNfa.startState with true in
utest eqsetEqual eqi acceptStates newNfa.acceptStates with true in
utest (digraphHasVertices states newNfa.graph) with true in
utest (digraphHasEdges transitions newNfa.graph) with true in
utest (digraphHasEdges [(1,2,'1')] (nfaAddTransition newNfa (1,2,'1')).graph) with true in
utest (digraphHasVertex 7 (nfaAddState newNfa 7).graph) with true in
utest nfaIsAcceptedState 2 newNfa with true in
utest nfaIsAcceptedState 3 newNfa with false in
utest nfaNextStates 1 newNfa.graph '0' with [2] in
-- Not accepted
utest nfaMakeInputPath (negi 1) newNfa.startState "1011" newNfa with
  [{status = "",state = 0,index = negi 1},
  {status = "",state = 1,index = 0},
  {status = "",state = 2,index = 1},
  {status = "",state = 1,index = 2},
  {status = "not accepted",state = 1,index = 3}] in
-- Accepted
utest nfaMakeInputPath (negi 1) newNfa.startState "10110" newNfa with
  [{status = "",state = 0,index = negi 1},
  {status = "",state = 1,index = 0},
  {status = "",state = 2,index = 1},
  {status = "",state = 1,index = 2},
  {status = "",state = 1,index = 3},
  {status = "accepted",state = 2,index = 4}] in
-- Invalid transition
utest nfaMakeInputPath (negi 1) newNfa.startState "0110" newNfa with
  [{status = "stuck",state = 0,index = negi 1}] in
-- Input of length 0
utest nfaMakeInputPath (negi 1) newNfa.startState "" newNfa with
  [{status = "not accepted",state = 0,index = negi 1}] in
-- Accepted, after branch got stuck.
 utest nfaMakeInputPath (negi 1) newNfa2.startState "11" newNfa2 with
  [{status = "",state = 0,index = (negi 1)},
  {status = "",state = 1,index = 0},
  {status = "not accepted", state = 3,index = 1},
  {status = "",state = 1,index = 0},
  {status = "accepted",state = 2,index = 1}] in
-- Accepted, got accepted in the first branch (the second isn't)
utest nfaMakeInputPath (negi 1) newNfa3.startState "11" newNfa3 with
  [{status = "",state = 0,index = (negi 1)},
  {status = "",state = 1,index = 0},
  {status = "accepted",state = 3,index = 1}] in
()
