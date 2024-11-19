include "common.mc"
include "ast.mc"
include "basic-types.mc"
include "either.mc"
include "json-debug.mc"

include "mlang/ast.mc"

lang PhaseStats = Ast + MLangTopLevel + AstToJson + MLangProgramToJson
  type StatState =
    { lastPhaseEnd : Ref Float
    , log : Bool
    , jsonDumpPhases : Set String
    }

  sem endPhaseStatsExpr : StatState -> String -> Expr -> ()
  sem endPhaseStatsExpr state phaseLabel =
  | e -> endPhaseStats state phaseLabel (Left e)

  sem endPhaseStatsProg : StatState -> String -> MLangProgram -> ()
  sem endPhaseStatsProg state phaseLabel =
  | p -> endPhaseStats state phaseLabel (Right p)

  sem endPhaseStats : StatState -> String -> Either Expr MLangProgram -> ()
  sem endPhaseStats state phaseLabel = | e ->
    let before = deref state.lastPhaseEnd in
    let now = wallTimeMs () in

    (if state.log then
      printLn phaseLabel;
      printLn (join ["  Phase duration: ", float2string (subf now before), "ms"]);
      let preTraverse = wallTimeMs () in
      let size = (switch e
        case Left expr then countExprNodes 0 expr
        case Right prog then countProgNodes prog
      end) in
      let postTraverse = wallTimeMs () in
      printLn (join ["  Ast size: ", int2string size, " (Traversal takes ~", float2string (subf postTraverse preTraverse), "ms)"])
     else ());

    (if setMem phaseLabel state.jsonDumpPhases then
      printJsonLn (JsonString (concat "Computing AST after " phaseLabel));
      let e = eitherEither exprToJson progToJson e in
      printJsonLn (JsonString (concat "Printing AST after " phaseLabel));
      printJsonLn e
     else ());

    let newNow = wallTimeMs () in
    modref state.lastPhaseEnd newNow

  sem mkPhaseLogState : Set String -> Bool -> StatState
  sem mkPhaseLogState jsonDumpPhases = | log ->
    { lastPhaseEnd = ref (wallTimeMs ())
    , jsonDumpPhases = jsonDumpPhases
    , log = log
    }
end
