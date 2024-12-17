include "common.mc"
include "ast.mc"
include "basic-types.mc"

include "mlang/ast.mc"

lang PhaseStats = Ast + MLangTopLevel
  type StatState =
    { lastPhaseEnd : Ref Float
    , log : Bool
    }

  sem endPhaseStatsExpr : StatState -> String -> Expr -> ()
  sem endPhaseStatsExpr state phaseLabel =
  | e -> endPhaseStats state phaseLabel (Left e)

  sem endPhaseStatsProg : StatState -> String -> MLangProgram -> ()
  sem endPhaseStatsProg state phaseLabel =
  | p -> endPhaseStats state phaseLabel (Right p)

  sem endPhaseStats : StatState -> String -> Either Expr MLangProgram -> ()
  sem endPhaseStats state phaseLabel = | e ->
    if state.log then
      let before = deref state.lastPhaseEnd in
      let now = wallTimeMs () in
      printLn phaseLabel;
      printLn (join ["  Phase duration: ", float2string (subf now before), "ms"]);
      let preTraverse = wallTimeMs () in
      let size = (switch e 
        case Left expr then countExprNodes 0 expr
        case Right prog then countProgNodes prog
      end) in 
      let postTraverse = wallTimeMs () in
      printLn (join ["  Ast size: ", int2string size, " (Traversal takes ~", float2string (subf postTraverse preTraverse), "ms)"]);
      let newNow = wallTimeMs () in
      modref state.lastPhaseEnd newNow
    else ()

  sem mkPhaseLogState : Bool -> StatState
  sem mkPhaseLogState = | log -> { lastPhaseEnd = ref (wallTimeMs ()), log = log }
end
