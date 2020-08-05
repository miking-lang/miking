include "graph.mc"
include "char.mc"
include "map.mc"
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

type NFA = {
  graph: Digraph,
  startState: a,
  acceptStates: [a]
}

-- get equality function for states
let nfaGetEqv = lam dfa.
  dfa.graph.eqv

-- get equality functions for labels
let nfaGetEql = lam dfa.
  dfa.graph.eql

-- get all states in nfa
let nfaStates = lam nfa.
  digraphVertices nfa.graph

-- get all transitions in nfa
let nfaTransitions = lam nfa.
  digraphEdges nfa.graph

-- get start state of the nfa
let nfaStartState = lam nfa.
  nfa.startState

-- get the accept states in the nfa
let nfaAcceptStates = lam nfa.
  nfa.acceptStates

-- get all transitions from state s1 to state s2
let nfaTransitionsBetween = lam s1. lam s2. lam nfa.
  digraphEdgesBetween s1 s2 nfa.graph

-- get all predecessor states to state s
let nfaInStates = lam s. lam nfa.
  digraphPredeccessors s nfa.graph

-- get all successor states to state s
let nfaOutStates = lam s. lam nfa.
  digraphSuccessors s nfa.graph

-- check that values are acceptable for the NFA
let nfaCheckValues = lam trans. lam s. lam eqv. lam eql. lam accS. lam startS.
<<<<<<< HEAD
  if not (setIsSubsetEq eqv accS s) then error "Some accepted states do not exist"
  else if not (setMem eqv startS s) then error "The start state does not exist"
  else true

-- States are represented by vertices in a directed graph
let nfaAddState =  lam nfa. lam state.
  {
    graph = (digraphAddVertex state nfa.graph),
    startState = nfa.startState,
    acceptStates = nfa.acceptStates
  }

-- Transitions between two states are represented by edges between vertices
let nfaAddTransition = lam nfa. lam trans.
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
let nfaIsAcceptedState = lam s. lam nfa.
  setMem nfa.graph.eqv s nfa.acceptStates
=======
    if not (setIsSubsetEq eqv accS s) then error "Some accepted states do not exist"
        else if not (setMem eqv startS s) then error "The start state does not exist"
        else true

-- States are represented by vertices in a directed graph
let nfaAddState =  lam nfa. lam state.
    {
        graph = (digraphAddVertex state nfa.graph),
        startState = nfa.startState,
        acceptStates = nfa.acceptStates
    }

-- Transitions between two states are represented by edges between vertices
let nfaAddTransition = lam nfa. lam trans.
    let states = getStates nfa in
    let from = trans.0 in
    let to = trans.1 in
    let label = trans.2 in
    {
        graph = (digraphAddEdge from to label nfa.graph),
        startState = nfa.startState,
        acceptStates = nfa.acceptStates
    }

-- returns true if state s is an accepted state in the nfa
let nfaIsAcceptedState = lam s. lam nfa.
    setMem nfa.graph.eqv s nfa.acceptStates
>>>>>>> DFA/NFA: Clean up whitespace and make alphabet implicit

-- check if there is a transition with label lbl from state s
let nfaStateHasTransition = lam s. lam trans. lam lbl.
  let neighbors = digraphEdgesFrom s trans in
  --check if lbl is a label in the neighbors list
  setMem trans.eql lbl (map (lam x. x.2) neighbors)

-- get next state from state s with label lbl. Throws error if no transition is found
let nfaNextStates = lam from. lam graph. lam lbl.
  let neighbors = digraphEdgesFrom from graph in
  let matches = filter (lam x. graph.eql x.2 lbl) neighbors in
  let neighboringStates = map (lam x. x.1) matches in
  match matches with [] then
  error "No transition was found"
  else neighboringStates

-- takes a path and returns whether it's accepted or not.
let pathIsAccepted = lam path.
  if null path then false
  else (setEqual eqchar (last path).status "accepted")

-- goes through the nfa, one state of the input at a time. Returns a list of {state, status, input}
-- where status is either accepted,stuck,not accepted or neutral ("")
recursive
let nfaMakeInputPath = lam i. lam currentState. lam input. lam nfa.
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
let nfaMakeEdgeInputPath = lam currentState. lam input. lam nfa.
  if (eqi (length input) 0) then []
  -- check if transition exists. If yes, go to next state
  else if nfaStateHasTransition currentState nfa.graph (head input) then
    foldl (lam path. lam elem.
      join [path, [(currentState,elem)], nfaMakeEdgeInputPath elem (tail input) nfa]
    ) [] (nfaNextStates currentState nfa.graph (head input))
  else []
end

-- constructor for the NFA
let nfaConstr = lam s. lam trans. lam startS. lam accS. lam eqv. lam eql.
<<<<<<< HEAD
  if nfaCheckValues trans s eqv eql accS startS then
  let emptyDigraph = digraphEmpty eqv eql in
  let initNfa = {
    graph = emptyDigraph,
    startState = startS,
    acceptStates = accS
  } in
  foldl nfaAddTransition (foldl nfaAddState initNfa s) trans
  else {}
=======
    if nfaCheckValues trans s eqv eql accS startS then
    let emptyDigraph = digraphEmpty eqv eql in
    let initNfa = {
        graph = emptyDigraph,
        startState = startS,
        acceptStates = accS
    } in
    foldl nfaAddTransition (foldl nfaAddState initNfa s) trans
    else {}

let printList = lam list.
    map (lam x. print x) list

let nfaPrintDotWithStates = lam nfa. lam v2str. lam l2str. lam direction. lam activeState.
    let eqv = getEqv nfa in
    let edges = getTransitions nfa in
    let vertices = getStates nfa in
    let _ = print "digraph {" in
    let _ = printList ["rankdir=", direction, ";\n"] in
    let _ = printList ["node [style=filled fillcolor=white shape=circle];"] in
    let _ = map
        (lam v.
            let _ = print (v2str v) in
            let dbl = (if (any (lam x. eqv x v) nfa.acceptStates) then "shape=doublecircle " else "") in
            let active = match activeState with () then "" else (
                if (eqv v activeState) then "fillcolor=darkgreen color=darkgreen fontcolor = white" else ""
            ) in
            printList ["[", dbl, active, "];"])
        vertices in
    let _ = print "start [fontcolor = white color = white];\n" in
    let _ = printList ["start -> ", v2str nfa.startState, "[label=start];"] in
    let eqEdge = (lam a. lam b. if and (eqv a.0 b.0) (eqv a.1 b.1) then true else false) in
    let _ = map
        (lam e.
            let _ = print (v2str e.0) in
            let _ = print " -> " in
            let _ = print (v2str e.1) in
            let _ = print "[label=\"" in
            let _ = print (l2str e.2) in
            print "\"];")
        edges in
    let _ = print "}\n" in ()

let nfaPrintDot = lam nfa. lam v2str. lam l2str. lam direction.
    nfaPrintDotWithStates nfa v2str l2str direction ()
>>>>>>> DFA/NFA: Clean up whitespace and make alphabet implicit

mexpr
let states = [0,1,2] in
let states2 = [0,1,2,3,4] in
let transitions = [(0,1,'1'),(1,1,'1'),(1,2,'0'),(2,2,'0'),(2,1,'1')] in
let transitions2 = [(0,1,'1'),(1,3,'1'),(1,2,'1')] in
let startState = 0 in
let acceptStates = [2] in
let newNfa = nfaConstr states transitions startState acceptStates eqi eqchar in
let newNfa2 = nfaConstr states2 transitions2 startState acceptStates eqi eqchar in
let newNfa3 = nfaConstr states2 transitions2 startState [3] eqi eqchar in
utest eqi startState newNfa.startState with true in
utest setEqual eqi acceptStates newNfa.acceptStates with true in
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
<<<<<<< HEAD
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
=======
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
>>>>>>> DFA/NFA: Clean up whitespace and make alphabet implicit
()
