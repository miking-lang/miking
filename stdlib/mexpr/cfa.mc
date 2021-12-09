-- CFA framework for MExpr. Currently, only 0-CFA (0 = context insensitive) is
-- supported. The algorithm is loosely based on Table 3.7 in the book
-- "Principles of Program Analysis" (Nielson et al.).
--
-- Some details:
-- - Only works on fully labelled terms provided by MExprANFAll (see mexpr/anf.mc).
-- - Uses efficient lazy constraint expansion, and not the static
--   constraints from table 3.7 in Nielson et al. (see p. 202 in Nielson et al.
--   for a discussion about this).
--
-- OPT(dlunde,2021-10-29): Map all names in analyzed program to integers
-- 0,1,...,#variables-1 to speed up analysis through tensor lookups? Current
-- analysis adds a log factor for lookups to the (already cubic) complexity.

include "set.mc"
include "either.mc"
include "name.mc"

include "pprint.mc"
include "boot-parser.mc"
include "ast.mc"
include "anf.mc"
include "ast-builder.mc"

type GenFun = Expr -> [Constraint]
type MatchGenFun = Name -> Name -> Pat -> [Constraint]

-- NOTE(dlunde,2021-11-03): CFAGraph should of course when possible be defined
-- as part of the CFA fragment (AbsVal and Constraint are not defined out
-- here).
type CFAGraph = {

  -- Contains updates that needs to be processed in the main CFA loop
  worklist: [(Name,AbsVal)],

  -- Contains abstract values currently associated with each name in the program.
  data: Map Name (Set AbsVal),

  -- For each name in the program, gives constraints which needs to be
  -- repropagated upon updates to the abstract values for the name.
  edges: Map Name [Constraint],

  -- Contains a list of functions used for generating match constraints
  -- TODO(dlunde,2021-11-17): Should be added as a product extension
  -- in the MatchCFA fragment instead, when possible.
  mcgfs: [MatchGenFun],

  -- NOTE(dlunde,2021-11-18): Data needed for analyses based on this framework
  -- must be put below directly, since we do not yet have product extensions.

  -- Used for alignment analysis in miking-dppl
  stochMatches: Set Name,

  -- Used to store any custom data in the graph
  graphData: Option GraphData

}

let emptyCFAGraph = {
  worklist = [],
  data = mapEmpty nameCmp,
  edges = mapEmpty nameCmp,
  mcgfs = [],
  stochMatches = setEmpty nameCmp,
  graphData = None ()
}

-------------------
-- BASE FRAGMENT --
-------------------

lang CFA = Ast + LetAst + MExprPrettyPrint

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  syn GraphData =
  -- Intentionally left blank

  sem cfa =
  | t -> match cfaDebug (None ()) (None ()) t with (_,graph) in graph

  sem cfaData (graphData: GraphData) =
  | t -> match cfaDebug (Some graphData) (None ()) t with (_,graph) in graph

  -- Main algorithm
  sem cfaDebug (graphData: Option GraphData) (env: Option PprintEnv) =
  | t ->

    let printGraph = lam env. lam graph. lam str.
      match env with Some env then
        match cfaGraphToString env graph with (env, graph) in
        printLn (join ["\n--- ", str, " ---"]);
        printLn graph;
        Some env
      else None ()
    in

    let graph = initGraph graphData t in

    -- Iteration
    recursive let iter = lam env: Option PprintEnv. lam graph: CFAGraph.
      if null graph.worklist then (env,graph)
      else
        match printGraph env graph "INTERMEDIATE CFA GRAPH" with env in
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match edgesLookup q graph with cc in
        let graph = foldl (propagateConstraint h) graph cc in
        iter env graph
    in
    iter env graph

  -- For a given expression, returns the variable "labeling" that expression.
  -- The existence of such a label is guaranteed by ANF.
  sem exprName =
  | t -> infoErrorExit (infoTm t) "Error in exprName for CFA"

  -- Required for the data type Set AbsVal
  sem cmpAbsVal (lhs: AbsVal) =
  | rhs /- : AbsVal -/ -> cmpAbsValH (lhs, rhs)
  sem cmpAbsValH =
  | (lhs, rhs) /- : (AbsVal, AbsVal) -/ ->
    let res = subi (constructorTag lhs) (constructorTag rhs) in
    if eqi res 0 then
      error
        "Missing case in cmpAbsValH for abstract values with same constructor."
    else res

  -- Required for the data type Set AbsVal
  sem eqAbsVal (lhs: AbsVal) =
  | rhs -> eqi (cmpAbsVal lhs rhs) 0

  -- Base constraint generation function (must still be included manually in
  -- constraintGenFuns)
  sem generateConstraints =
  | t -> []

  -- This function is responsible for setting up the initial CFAGraph given the
  -- program to analyze.
  sem initGraph (graphData: Option GraphData) =
  -- Intentionally left blank

  -- Call a set of constraint generation functions on each term in program.
  -- Useful when defining initGraph.
  sem collectConstraints (cgfs: [GenFun]) (acc: [Constraint]) =
  | t /- : Expr -/ ->
    let acc = foldl (lam acc. lam f. concat (f t) acc) acc cgfs in
    sfold_Expr_Expr (collectConstraints cgfs) acc t

  sem initConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  -- Intentionally left blank

  -- CFAGraph -> Name -> Constraint -> CFAGraph
  sem addEdge (graph: CFAGraph) (q: Name) =
  | cstr ->
    match edgesLookup q graph with cstrsq in
    { graph with edges = mapInsert q (cons cstr cstrsq) graph.edges }

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem initConstraintName (name: Name) (graph: CFAGraph) =
  | cstr ->
    let graph = addEdge graph name cstr in
    let avs = dataLookup name graph in
    setFold (lam graph. lam av. propagateConstraint (name,av) graph cstr)
      graph avs

  sem dataLookup (key: Name) =
  | graph ->
    let graph: CFAGraph = graph in
    mapLookupOrElse (lam. setEmpty cmpAbsVal) key graph.data

  sem edgesLookup (key: Name) =
  | graph ->
    let graph: CFAGraph = graph in
    mapLookupOrElse (lam. []) key graph.edges

  -- CFAGraph -> AbsVal -> Name -> CFAGraph
  sem addData (graph: CFAGraph) (d: AbsVal) =
  | q ->
    match dataLookup q graph with dq in
    if setMem d dq then graph else
      {{ graph with
           data = mapInsert q (setInsert d dq) graph.data } with
           worklist = cons (q,d) graph.worklist }

  ---------------------
  -- PRETTY PRINTING --
  ---------------------

  sem constraintToString (env: PprintEnv) =
  -- Intentionally left blank

  sem absValToString (env: PprintEnv) =
  -- Intentionally left blank

  -- Prints a CFA graph
  sem cfaGraphToString (env: PprintEnv) =
  | graph ->
    let graph: CFAGraph = graph in
    let f = lam env. lam e: (Name,AbsVal).
      match pprintVarName env e.0 with (env,n) in
      match absValToString env e.1 with (env,av) in
      (env,join ["(", n, ", ", av, ")"]) in
    match mapAccumL f env graph.worklist with (env,worklist) in
    match mapAccumL (lam env: PprintEnv. lam b:(Name,Set AbsVal).
        match pprintVarName env b.0 with (env,b0) in
        match mapAccumL absValToString env (setToSeq b.1) with (env,b1) in
        (env,(b0,b1))
      ) env (mapBindings graph.data)
    with (env, data) in
    match mapAccumL (lam env: PprintEnv. lam b:(Name,[Constraint]).
        match pprintVarName env b.0 with (env,b0) in
        match mapAccumL constraintToString env b.1 with (env,b1) in
        (env,(b0,b1))
      ) env (mapBindings graph.edges)
    with (env, edges) in

    let str = join [
      "*** WORKLIST ***\n",
      "  [", strJoin ", " worklist, "]\n",
      "*** DATA ***\n",
      strJoin "\n" (map (lam b:(String,[String]).
        let avs = strJoin "\n" (map (concat "    ") b.1) in
        join ["  ", b.0, " =\n", avs]
      ) data), "\n",
      "*** EDGES ***\n",
      strJoin "\n" (map (lam b:(String,[String]).
        let cstrs = strJoin "\n" (map (concat "    ") b.1) in
        join ["  ", b.0, " =\n", cstrs]
      ) edges), "\n"
    ] in

    (env, str)

end

----------------------
-- BASE CONSTRAINTS --
----------------------

lang InitConstraint = CFA

  syn Constraint =
  -- {lhs} ⊆ rhs
  | CstrInit { lhs: AbsVal, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrInit r -> addData graph r.lhs r.rhs

  sem constraintToString (env: PprintEnv) =
  | CstrInit { lhs = lhs, rhs = rhs } ->
    match absValToString env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])


end

lang DirectConstraint = CFA

  syn Constraint =
  -- lhs ⊆ rhs
  | CstrDirect { lhs: Name, rhs: Name }

  sem isDirect =
  | _ /- : AbsVal -/ -> true

  -- AbsVal -> AbsVal
  sem directTransition (graph: CFAGraph) (rhs: Name) =
  | av -> av

  sem initConstraint (graph: CFAGraph) =
  | CstrDirect r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrDirect r ->
    if isDirect update.1 then
      let av = directTransition graph r.rhs update.1 in
      addData graph av r.rhs
    else graph

  sem constraintToString (env: PprintEnv) =
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match pprintVarName env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])

end

lang DirectAbsValConstraint = CFA

  syn Constraint =
  -- {lhsav} ⊆ lhs ⇒ {rhsav} ⊆ rhs
  | CstrDirectAv { lhs: Name, lhsav: AbsVal, rhs: Name, rhsav: AbsVal }

  sem initConstraint (graph: CFAGraph) =
  | CstrDirectAv r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrDirectAv r ->
    if eqAbsVal update.1 r.lhsav then
      addData graph r.rhsav r.rhs
    else graph

  sem constraintToString (env: PprintEnv) =
  | CstrDirectAv { lhs = lhs, lhsav = lhsav, rhs = rhs, rhsav = rhsav } ->
    match pprintVarName env lhs with (env,lhs) in
    match absValToString env lhsav with (env,lhsav) in
    match pprintVarName env rhs with (env,rhs) in
    match absValToString env rhsav with (env,rhsav) in
    (env, join ["{", lhsav ,"} ⊆ ", lhs, " ⇒ {", rhsav ,"} ⊆ ", rhs])

end

-----------
-- TERMS --
-----------

lang VarCFA = CFA + DirectConstraint + VarAst

  sem generateConstraints =
  | TmLet { ident = ident, body = TmVar t } ->
    [ CstrDirect { lhs = t.ident, rhs = ident } ]

  sem exprName =
  | TmVar t -> t.ident

end

lang LamCFA = CFA + InitConstraint + LamAst

  -- Abstract representation of lambdas.
  syn AbsVal =
  | AVLam { ident: Name, body: Name }

  sem cmpAbsValH =
  | (AVLam { ident = lhs, body = lbody },
     AVLam { ident = rhs, body = rbody }) ->
     let diff = nameCmp lhs rhs in
     if eqi diff 0 then nameCmp lbody rbody else diff

  sem generateConstraints =
  | TmLet { ident = ident, body = TmLam t } ->
    let av: AbsVal = AVLam { ident = t.ident, body = exprName t.body } in
    [ CstrInit { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVLam { ident = ident, body = body } ->
    match pprintVarName env ident with (env,ident) in
    match pprintVarName env body with (env,body) in
    (env, join ["lam ", ident, ". ", body])

end

lang AppCFA = CFA + DirectConstraint + LamCFA + AppAst

  syn Constraint =
  -- {lam x. b} ⊆ lhs ⇒ (rhs ⊆ x and b ⊆ res)
  | CstrLamApp { lhs: Name, rhs: Name, res: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrLamApp r & cstr -> initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match update.1 with AVLam { ident = x, body = b } then
      -- Add rhs ⊆ x constraint
      let graph = initConstraint graph (CstrDirect { lhs = rhs, rhs = x }) in
      -- Add b ⊆ res constraint
      initConstraint graph (CstrDirect { lhs = b, rhs = res })
    else graph

  sem constraintToString (env: PprintEnv) =
  | CstrLamApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarName env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    match pprintVarName env res with (env,res) in
    (env, join [ "{lam >x<. >b<} ⊆ ", lhs, " ⇒ ", rhs, " ⊆ >x< AND >b< ⊆ ", res ])

  sem generateConstraints =
  | TmLet { ident = ident, body = TmApp app} ->
    match app.lhs with TmVar l then
      match app.rhs with TmVar r then
        [ CstrLamApp { lhs = l.ident, rhs = r.ident, res = ident } ]
      else infoErrorExit (infoTm app.rhs) "Not a TmVar in application"
    else infoErrorExit (infoTm app.lhs) "Not a TmVar in application"

end

lang LetCFA = CFA + LetAst
  sem exprName =
  | TmLet t -> exprName t.inexpr
end

lang RecLetsCFA = CFA + LamCFA + RecLetsAst
  sem exprName =
  | TmRecLets t -> exprName t.inexpr

  sem generateConstraints =
  | TmRecLets { bindings = bindings } ->
    map (lam b: RecLetBinding.
      match b.body with TmLam t then
        let av: AbsVal = AVLam { ident = t.ident, body = exprName t.body } in
        CstrInit { lhs = av, rhs = b.ident }
      else infoErrorExit (infoTm b.body) "Not a lambda in recursive let body"
    ) bindings

end

lang ConstCFA = CFA + ConstAst

  sem generateConstraints =
  | TmLet { ident = ident, body = TmConst t } ->
    generateConstraintsConst t.info t.val

  sem generateConstraintsConst (info: Info) =
  | const -> infoErrorExit info "Constant not supported in CFA"

end

lang SeqCFA = CFA + InitConstraint + SeqAst

  syn AbsVal =
  -- Abstract representation of sequences. Contains a set of names that may
  -- flow to the sequence.
  | AVSeq { names: Set Name }

  sem cmpAbsValH =
  | (AVSeq { names = lhs }, AVSeq { names = rhs }) -> setCmp lhs rhs

  sem generateConstraints =
  | TmLet { ident = ident, body = TmSeq t } ->
    let names = foldl (lam acc: [Name]. lam t: Expr.
      match t with TmVar t then cons t.ident acc else acc) [] t.tms
    in
    let av: AbsVal = AVSeq { names = setOfSeq nameCmp names } in
    [ CstrInit { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVSeq { names = names } ->
    match mapAccumL pprintVarName env (setToSeq names) with (env,names) in
    let names = strJoin ", " names in
    (env, join ["[{", names, "}]"])

end

lang RecordCFA = CFA + InitConstraint + RecordAst
  -- NOTE(dlunde,2021-11-10) TmRecordUpdate is currently not supported.

  syn AbsVal =
  -- Abstract representation of records. The bindings are from SIDs to names,
  -- rather than expressions.
  | AVRec { bindings: Map SID Name }

  sem cmpAbsValH =
  | (AVRec { bindings = lhs }, AVRec { bindings = rhs }) ->
    mapCmp nameCmp lhs rhs

  sem generateConstraints =
  | TmLet { ident = ident, body = TmRecord t } ->
    let bindings = mapMap (lam v: Expr.
        match v with TmVar t then t.ident
        else infoErrorExit (infoTm v) "Not a TmVar in record"
      ) t.bindings
    in
    let av: AbsVal = AVRec { bindings = bindings } in
    [ CstrInit { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVRec { bindings = bindings } ->
    match mapMapAccum (lam env. lam k. lam v.
        match pprintVarName env v with (env, v) in
        (env, join [pprintLabelString k, " = ", v])
      ) env bindings
    with (env, bindings) in
    let binds = mapValues bindings in
    let merged = strJoin ", " binds in
    (env, join ["{ ", merged, " }"])

end

lang TypeCFA = CFA + TypeAst
  sem exprName =
  | TmType t -> exprName t.inexpr
end

lang DataCFA = CFA + InitConstraint + DataAst
  syn AbsVal =
  -- Abstract representation of constructed data.
  | AVCon { ident: Name, body: Name }

  sem cmpAbsValH =
  | (AVCon { ident = ilhs, body = blhs },
     AVCon { ident = irhs, body = brhs }) ->
    let idiff = nameCmp ilhs irhs in
    if eqi idiff 0 then nameCmp blhs brhs else idiff

  sem generateConstraints =
  | TmLet { ident = ident, body = TmConApp t } ->
    let body = match t.body with TmVar t then t.ident
      else infoErrorExit (infoTm t.body) "Not a TmVar in con app" in
    let av: AbsVal = AVCon { ident = t.ident, body = body } in
    [ CstrInit { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVCon { ident = ident, body = body } ->
    match pprintConName env ident with (env,ident) in
    match pprintVarName env body with (env,body) in
    (env, join [ident, " ", body])

  sem exprName =
  | TmConDef t -> exprName t.inexpr

end

lang MatchCFA = CFA + DirectConstraint + MatchAst

  syn Constraint =
  | CstrMatch { id: Name, pat: Pat, target: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrMatch r & cstr -> initConstraintName r.target graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrMatch r ->
    propagateMatchConstraint graph r.id (r.pat,update.1)

  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | _ -> graph -- Default: do nothing

  sem constraintToString (env: PprintEnv) =
  | CstrMatch { id = id, pat = pat, target = target } ->
    match pprintVarName env id with (env, id) in
    match getPatStringCode 0 env pat with (env, pat) in
    match pprintVarName env target with (env, target) in
    (env, join [id, ": match ", target, " with ", pat])

  sem generateConstraintsMatch (mcgfs: [MatchGenFun]) =
  | _ -> []
  | TmLet { ident = ident, body = TmMatch t } ->
    let thnName = exprName t.thn in
    let elsName = exprName t.els in
    let cstrs = [
      CstrDirect { lhs = thnName, rhs = ident },
      CstrDirect { lhs = elsName, rhs = ident }
    ] in
    match t.target with TmVar tv then
      foldl (lam acc. lam f. concat (f ident tv.ident t.pat) acc) cstrs mcgfs
    else infoErrorExit (infoTm t.target) "Not a TmVar in match target"

  sem generateMatchConstraints (id: Name) (target: Name) =
  | pat /- : Pat -/ -> [ CstrMatch { id = id, pat = pat, target = target } ]

end

lang UtestCFA = CFA + UtestAst
  sem exprName =
  | TmUtest t -> exprName t.next
end

lang NeverCFA = CFA + NeverAst
  -- Nothing to be done here
end

lang ExtCFA = CFA + ExtAst
  sem exprName =
  | TmExt t -> exprName t.inexpr
end

---------------
-- CONSTANTS --
---------------
-- Most data-flow constraints will need to add data-flow components related to
-- constants (e.g., abstract values for positive and negative integers).
-- However, in this base version of 0-CFA, no data flow constraints are
-- generated.

lang IntCFA = CFA + ConstCFA + IntAst
  sem generateConstraintsConst (info: Info) =
  | CInt _ -> []
end

lang ArithIntCFA = CFA + ConstCFA + ArithIntAst
  sem generateConstraintsConst (info: Info) =
  | CAddi _ -> []
  | CSubi _ -> []
  | CMuli _ -> []
  | CDivi _ -> []
  | CNegi _ -> []
  | CModi _ -> []
end

lang ShiftIntCFA = CFA + ConstCFA + ShiftIntAst
  sem generateConstraintsConst (info: Info) =
  | CSlli _ -> []
  | CSrli _ -> []
  | CSrai _ -> []
end

lang FloatCFA = CFA + ConstCFA + FloatAst
  sem generateConstraintsConst (info: Info) =
  | CFloat _ -> []
end

lang ArithFloatCFA = CFA + ConstCFA + ArithFloatAst
  sem generateConstraintsConst (info: Info) =
  | CAddf _ -> []
  | CSubf _ -> []
  | CMulf _ -> []
  | CDivf _ -> []
  | CNegf _ -> []
end

lang FloatIntConversionCFA = CFA + ConstCFA + FloatIntConversionAst
  sem generateConstraintsConst (info: Info) =
  | CFloorfi _ -> []
  | CCeilfi _ -> []
  | CRoundfi _ -> []
  | CInt2float _ -> []
end

lang BoolCFA = CFA + ConstCFA + BoolAst
  sem generateConstraintsConst (info: Info) =
  | CBool _ -> []
end

lang CmpIntCFA = CFA + ConstCFA + CmpIntAst
  sem generateConstraintsConst (info: Info) =
  | CEqi _ -> []
  | CNeqi _ -> []
  | CLti _ -> []
  | CGti _ -> []
  | CLeqi _ -> []
  | CGeqi _ -> []
end

lang CmpFloatCFA = CFA + ConstCFA + CmpFloatAst
  sem generateConstraintsConst (info: Info) =
  | CEqf _ -> []
  | CLtf _ -> []
  | CLeqf _ -> []
  | CGtf _ -> []
  | CGeqf _ -> []
  | CNeqf _ -> []
end

lang CharCFA = CFA + ConstCFA + CharAst
  sem generateConstraintsConst (info: Info) =
  | CChar _ -> []
end

lang CmpCharCFA = CFA + ConstCFA + CmpCharAst
  sem generateConstraintsConst (info: Info) =
  | CEqc _ -> []
end

lang IntCharConversionCFA = CFA + ConstCFA + IntCharConversionAst
  sem generateConstraintsConst (info: Info) =
  | CInt2Char _ -> []
  | CChar2Int _ -> []
end

lang FloatStringConversionCFA = CFA + ConstCFA + FloatStringConversionAst
  sem generateConstraintsConst (info: Info) =
  | CString2float _ -> []
  | CFloat2string _ -> []
end

lang SymbCFA = CFA + ConstCFA + SymbAst
  sem generateConstraintsConst (info: Info) =
  | CSymb _ -> []
  | CGensym _ -> []
  | CSym2hash _ -> []
end

lang CmpSymbCFA = CFA + ConstCFA + CmpSymbAst
  sem generateConstraintsConst (info: Info) =
  | CEqsym _ -> []
end

-- TODO(dlunde,2021-11-11): Add flow constraints for sequence operations?
lang SeqOpCFA = CFA + ConstCFA + SeqOpAst
  sem generateConstraintsConst (info: Info) =
  -- | CSet _ -> []
  -- | CGet _ -> []
  -- | CCons _ -> []
  -- | CSnoc _ -> []
  -- | CConcat _ -> []
  -- | CLength _ -> []
  -- | CReverse _ -> []
  -- | CHead _ -> []
  -- | CTail _ -> []
  -- | CNull _ -> []
  -- | CMap _ -> []
  -- | CMapi _ -> []
  -- | CIter _ -> []
  -- | CIteri _ -> []
  -- | CFoldl _ -> []
  -- | CFoldr _ -> []
  -- | CCreate _ -> []
  -- | CCreateList _ -> []
  -- | CCreateRope _ -> []
  -- | CSplitAt _ -> []
  -- | CSubsequence _ -> []
end

lang FileOpCFA = CFA + ConstCFA + FileOpAst
  sem generateConstraintsConst (info: Info) =
  | CFileRead _ -> []
  | CFileWrite _ -> []
  | CFileExists _ -> []
  | CFileDelete _ -> []
end

lang IOCFA = CFA + ConstCFA + IOAst
  sem generateConstraintsConst (info: Info) =
  | CPrint _ -> []
  | CPrintError _ -> []
  | CDPrint _ -> []
  | CFlushStdout _ -> []
  | CFlushStderr _ -> []
  | CReadLine _ -> []
  | CReadBytesAsString _ -> []
end

lang RandomNumberGeneratorCFA = CFA + ConstCFA + RandomNumberGeneratorAst
  sem generateConstraintsConst (info: Info) =
  | CRandIntU _ -> []
  | CRandSetSeed _ -> []
end

lang SysCFA = CFA + ConstCFA + SysAst
  sem generateConstraintsConst (info: Info) =
  | CExit _ -> []
  | CError _ -> []
  | CArgv _ -> []
  | CCommand _ -> []
end

lang TimeCFA = CFA + ConstCFA + TimeAst
  sem generateConstraintsConst (info: Info) =
  | CWallTimeMs _ -> []
  | CSleepMs _ -> []
end

lang ConTagCFA = CFA + ConstCFA + ConTagAst
  sem generateConstraintsConst (info: Info) =
  | CConstructorTag _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang RefOpCFA = CFA + ConstCFA + RefOpAst
  sem generateConstraintsConst (info: Info) =
  -- | CRef _ -> []
  -- | CModRef _ -> []
  -- | CDeRef _ -> []
end

-- TODO(dlunde,2021-11-11): Add flow constraints for maps and map operations?
lang MapCFA = CFA + ConstCFA + MapAst
  sem generateConstraintsConst (info: Info) =
  -- | CMapEmpty _ -> []
  -- | CMapInsert _ -> []
  -- | CMapRemove _ -> []
  -- | CMapFindExn _ -> []
  -- | CMapFindOrElse _ -> []
  -- | CMapFindApplyOrElse _ -> []
  -- | CMapBindings _ -> []
  -- | CMapChooseExn _ -> []
  -- | CMapChooseOrElse _ -> []
  -- | CMapSize _ -> []
  -- | CMapMem _ -> []
  -- | CMapAny _ -> []
  -- | CMapMap _ -> []
  -- | CMapMapWithKey _ -> []
  -- | CMapFoldWithKey _ -> []
  -- | CMapEq _ -> []
  -- | CMapCmp _ -> []
  -- | CMapGetCmpFun _ -> []
end

-- TODO(dlunde,2021-11-11): Mutability complicates the analysis, but could
-- probably be added.
lang TensorOpCFA = CFA + ConstCFA + TensorOpAst
  sem generateConstraintsConst (info: Info) =
  -- | CTensorCreateInt _ -> []
  -- | CTensorCreateFloat _ -> []
  -- | CTensorCreate _ -> []
  -- | CTensorGetExn _ -> []
  -- | CTensorSetExn _ -> []
  -- | CTensorRank _ -> []
  -- | CTensorShape _ -> []
  -- | CTensorReshapeExn _ -> []
  -- | CTensorCopy _ -> []
  -- | CTensorTransposeExn _ -> []
  -- | CTensorSliceExn _ -> []
  -- | CTensorSubExn _ -> []
  -- | CTensorIterSlice _ -> []
  -- | CTensorEq _ -> []
  -- | CTensorToString _ -> []
end

lang BootParserCFA = CFA + ConstCFA + BootParserAst
  sem generateConstraintsConst (info: Info) =
  | CBootParserParseMExprString _ -> []
  | CBootParserParseMCoreFile _ -> []
  | CBootParserGetId _ -> []
  | CBootParserGetTerm _ -> []
  | CBootParserGetType _ -> []
  | CBootParserGetString _ -> []
  | CBootParserGetInt _ -> []
  | CBootParserGetFloat _ -> []
  | CBootParserGetListLength _ -> []
  | CBootParserGetConst _ -> []
  | CBootParserGetPat _ -> []
  | CBootParserGetInfo _ -> []
end

--------------
-- PATTERNS --
--------------

lang NamedPatCFA = MatchCFA + NamedPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatNamed { ident = PName n }, av) -> addData graph av n
  | (PatNamed { ident = PWildcard _ }, _) -> graph
end

lang SeqTotPatCFA = MatchCFA + SeqCFA + SeqTotPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatSeqTot p, AVSeq { names = names }) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs =
          foldl (lam acc. lam f. concat (f id name pat) acc) [] graph.mcgfs
        in
        foldl initConstraint graph cstrs
      ) graph names in
    foldl f graph p.pats
end

lang SeqEdgePatCFA = MatchCFA + SeqCFA + SeqEdgePat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatSeqEdge p, AVSeq { names = names } & av) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph: CFAGraph. lam name.
        let cstrs = foldl (lam acc. lam f. concat (f id name pat) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph names in
    let graph = foldl f graph p.prefix in
    let graph = foldl f graph p.postfix in
    match p.middle with PName rhs then addData graph av rhs
    else graph
  | (PatSeqEdge p, av) ->
    match p.middle with PName rhs then addData graph av rhs
    else graph
end

lang RecordPatCFA = MatchCFA + RecordCFA + RecordPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatRecord { bindings = pbindings }, AVRec { bindings = abindings }) ->
    -- Check if record pattern is compatible with abstract value record
    let compatible = mapAllWithKey (lam k. lam. mapMem k abindings) pbindings in
    if compatible then
      mapFoldWithKey (lam graph: CFAGraph. lam k. lam pb: Pattern.
        let ab: Name = mapFindExn k abindings in
        let cstrs = foldl (lam acc. lam f. concat (f id ab pb) acc)
          [] graph.mcgfs in
        foldl initConstraint graph cstrs
      ) graph pbindings
    else graph -- Nothing to be done
end

lang DataPatCFA = MatchCFA + DataCFA + DataPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatCon p, AVCon { ident = ident, body = body }) ->
    if nameEq p.ident ident then
      let cstrs = foldl (lam acc. lam f. concat (f id body p.subpat) acc)
        [] graph.mcgfs in
      foldl initConstraint graph cstrs
    else graph
end

lang IntPatCFA = MatchCFA + IntPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatInt p, _) -> graph
end

lang CharPatCFA = MatchCFA + CharPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatChar p, _) -> graph
end

lang BoolPatCFA = MatchCFA + BoolPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatBool p, _) -> graph
end

lang AndPatCFA = MatchCFA + AndPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatAnd p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

lang OrPatCFA = MatchCFA + OrPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatOr p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

lang NotPatCFA = MatchCFA + NotPat
  sem propagateMatchConstraint (graph: CFAGraph) (id: Name) =
  | (PatNot p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

---------------
-- MEXPR CFA --
---------------

lang MExprCFA = CFA +

  -- Base constraints
  InitConstraint + DirectConstraint + DirectAbsValConstraint +

  -- Terms
  VarCFA + LamCFA + AppCFA +
  LetCFA + RecLetsCFA + ConstCFA + SeqCFA + RecordCFA + TypeCFA + DataCFA +
  MatchCFA + UtestCFA + NeverCFA + ExtCFA +

  -- Constants
  IntCFA + ArithIntCFA + ShiftIntCFA + FloatCFA + ArithFloatCFA +
  FloatIntConversionCFA + BoolCFA + CmpIntCFA + CmpFloatCFA + CharCFA +
  CmpCharCFA + IntCharConversionCFA + FloatStringConversionCFA + SymbCFA +
  CmpSymbCFA + SeqOpCFA + FileOpCFA + IOCFA + RandomNumberGeneratorCFA +
  SysCFA + TimeCFA + ConTagCFA + RefOpCFA + MapCFA + TensorOpCFA +
  BootParserCFA +

  -- Patterns
  NamedPatCFA + SeqTotPatCFA + SeqEdgePatCFA + RecordPatCFA + DataPatCFA +
  IntPatCFA + CharPatCFA + BoolPatCFA + AndPatCFA + OrPatCFA + NotPatCFA

-----------
-- TESTS --
-----------

lang Test = MExprCFA + MExprANFAll + BootParser + MExprPrettyPrint

  -- Type: Expr -> CFAGraph
  sem initGraph (graphData : Option GraphData) =
  | t ->

    -- Initial graph
    let graph = emptyCFAGraph in

    -- Initialize match constraint generating functions
    let graph = { graph with mcgfs = [generateMatchConstraints] } in

    -- Initialize constraint generating functions
    let cgfs = [generateConstraints, generateConstraintsMatch graph.mcgfs] in

    -- Recurse over program and generate constraints
    let cstrs: [Constraint] = collectConstraints cgfs [] t in

    -- Initialize all collected constraints
    let graph = foldl initConstraint graph cstrs in

    -- Return graph
    graph

end

mexpr
use Test in

-- Test functions --
let _parse = parseMExprString [] in
let _testBase: Option PprintEnv -> Expr -> (Option PprintEnv, CFAGraph) =
  lam env: Option PprintEnv. lam t: Expr.
    match env with Some env then
      -- Version with debug printouts
      let tANF = normalizeTerm t in
      match pprintCode 0 env t with (env,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 env tANF with (env,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match cfaDebug (Some env) tANF with (Some env,cfaRes) in
      match cfaGraphToString env cfaRes with (env, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      (Some env,cfaRes)

    else
      -- Version without debug printouts
      let tANF = normalizeTerm t in
      let cfaRes = cfa tANF in
      (None (), cfaRes)
in

let _test: Bool -> Expr -> [String] -> [(String,[String])] =
  lam debug. lam t. lam vars.
    let env = if debug then Some pprintEnvEmpty else None () in
    match _testBase env t with (_, cfaRes) in
    map (lam var: String.
      let avs = dataLookup (nameNoSym var) cfaRes in
      let val = setFold
        (lam acc. lam av.
           match av with AVLam { ident = i } then
             cons (nameGetStr i) acc
           else acc)
        [] avs
      in (var, val)
    ) vars
in

-- Custom equality function for testing lambda control flow only
let eqTestLam = eqSeq (lam t1:(String,[String]). lam t2:(String,[String]).
  if eqString t1.0 t2.0 then
    let t11 = setOfSeq cmpString t1.1 in
    let t21 = setOfSeq cmpString t2.1 in
    setEq t11 t21
  else false
) in
--------------------

-- First test from Nielson et al.
let t = _parse "
  (lam x. x) (lam y. y)
------------------------" in
utest _test false t ["x","y"] with [
  ("x", ["y"]),
  ("y", [])
] using eqTestLam in

-- Second test from Nielson et al.
let t = _parse "
  let f = lam x. x 1 in
  let g = lam y. addi y 2 in
  let h = lam z. addi z 3 in
  let res = addi (f g) (f h) in
  res
------------------------" in
utest _test false t ["f","g","h","x","y","z","res"] with [
  ("f", ["x"]),
  ("g", ["y"]),
  ("h", ["z"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam in

-- Third test from Nielson et al.
let t = _parse "
recursive let g = lam x. g (lam y. y) in
let res = g (lam z. z) in
res
------------------------" in
utest _test false t ["g","x","y","z","res"] with [
  ("g", ["x"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam in

-- Sequence
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let seq = [f, lam z. z] in
  let res = match seq with [a] ++ _ then
      a g
    else
      (lam v. v)
  in res
------------------------" in
utest _test false t ["res","a"] with [
  ("res", ["v","y"]),
  ("a", ["x","z"])
] using eqTestLam in

-- Record
let t = _parse "
  let f = lam x. x in
  let g = lam y. y in
  let r = { a = f, b = 3 } in
  let res = match r with { a = a } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

-- ConApp
let t = _parse "
  type T in
  con C: (a -> a) -> T in
  let f = lam x. x in
  let g = lam y. y in
  let d = C f in
  let res = match d with C a then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

-- Nested
let t = _parse "
  type T in
  con C: (a -> a) -> T in
  let f = lam x. x in
  let g = lam y. y in
  let d = { a = [C f], b = 3 } in
  let res = match d with { a = [C a] } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest _test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

()
