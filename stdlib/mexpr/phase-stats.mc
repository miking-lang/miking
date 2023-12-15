include "common.mc"
include "ast.mc"

lang PhaseStats = Ast
  type StatState =
    { lastPhaseEnd : Ref Float
    , log : Bool
    }

  sem endPhaseStats : StatState -> String -> Expr -> ()
  sem endPhaseStats state phaseLabel = | e ->
    if state.log then
      let before = deref state.lastPhaseEnd in
      let now = wallTimeMs () in
      printLn phaseLabel;
      printLn (join ["  Phase duration: ", float2string (subf now before), "ms"]);
      let preTraverse = wallTimeMs () in
      let size = countExprNodes 0 e in
      let postTraverse = wallTimeMs () in
      printLn (join ["  Ast size: ", int2string size, " (Traversal takes ~", float2string (subf postTraverse preTraverse), "ms)"]);
      let newNow = wallTimeMs () in
      modref state.lastPhaseEnd newNow
    else ()

  sem mkPhaseLogState : Bool -> StatState
  sem mkPhaseLogState = | log -> { lastPhaseEnd = ref (wallTimeMs ()), log = log }
end
