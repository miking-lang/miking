-- CFA framework for MExpr. Currently, only 0-CFA (context insensitive) is
-- supported. The algorithm is based on Table 3.7 in the book "Principles of
-- Program Analysis" (Nielson et al.).
--
-- Some details:
-- - Only works on terms in ANF (e.g., by transformation with mexpr/anf.mc).
-- - Uses efficient lazy constraint expansion, and not the static
--   constraints from table 3.7 in Nielson et al. (see p. 202 in Nielson et al.
--   for a discussion about this).

include "set.mc"
include "either.mc"
include "name.mc"

include "pprint.mc"
include "boot-parser.mc"
include "ast.mc"
include "anf.mc"
include "ast-builder.mc"

-- OPT(dlunde,2021-10-29): Map all names in analyzed program to integers
-- 0,1,...,#variables-1 to speed up analysis through tensor lookups? Current
-- analysis adds a log factor for lookups to the (already cubic) complexity.

-- NOTE(dlunde,2021-11-03): CFAGraph should of course when possible be defined
-- as part of the CFA fragment (AbsVal and Constraint are not defined out
-- here).
type CFAGraph = {
  worklist: [(Name,AbsVal)],
  data: Map Name (Set AbsVal),
  edges: Map Name [Constraint]
}

let emptyCFAGraph = {
  worklist = [],
  data = mapEmpty nameCmp,
  edges = mapEmpty nameCmp
}

-------------------
-- BASE FRAGMENT --
-------------------

lang CFA = Ast + LetAst + MExprPrettyPrint

  syn Constraint =
  -- Intentionally left blank

  syn AbsVal =
  -- Intentionally left blank

  -- Main CFA algorithm
  sem cfa =
  | t ->

    -- Generate and collect all constraints
    let cstrs: [Constraint] = _collectConstraints [] t in

    -- Build the graph
    let graph = foldl initConstraint emptyCFAGraph cstrs in

    -- Iteration
    recursive let iter = lam graph: CFAGraph.
      if null graph.worklist then graph
      else
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match _dataLookup q graph with dq in
        match _edgesLookup q graph with cc in
        let graph = foldl (propagateConstraint h) graph cc in
        iter graph
    in
    iter graph

  sem cfaDebug (env: PprintEnv) =
  | t ->

    let printGraph = lam env. lam graph. lam str.
      match cfaGraphToString env graph with (env, graph) in
      printLn (join ["\n--- ", str, " ---"]);
      printLn graph;
      env
    in

    -- Generate and collect all constraints
    let cstrs: [Constraint] = _collectConstraints [] t in

    -- Build the graph
    let graph = foldl initConstraint emptyCFAGraph cstrs in

    -- Iteration
    recursive let iter = lam env: PprintEnv. lam graph: CFAGraph.
      if null graph.worklist then (env,graph)
      else
        match printGraph env graph "INTERMEDIATE CFA GRAPH" with env in
        match head graph.worklist with (q,d) & h in
        let graph = { graph with worklist = tail graph.worklist } in
        match _dataLookup q graph with dq in
        match _edgesLookup q graph with cc in
        let graph = foldl (propagateConstraint h) graph cc in
        iter env graph
    in
    iter env graph


  -- For a given expression, returns the variable "labeling" that expression.
  -- The existence of such a label is guaranteed by ANF.
  sem exprName =
  | t -> infoErrorExit (infoTm t) "Unsupported in exprName for CFA"

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
  -- _constraintGenFuns)
  sem generateConstraints =
  | t -> []

  -- Type () -> [Expr -> [Constraint]]
  -- This must be overriden in the final fragment where CFA should be applied.
  -- Gives a list of constraint generating functions (e.g., generateConstraints)
  sem _constraintGenFuns =
  -- Intentionally left blank

  -- Traverses all subterms and collects constraints
  sem _collectConstraints (acc: [Constraint]) =
  | t ->
    let acc =
      foldl (lam acc. lam f. concat (f t) acc) acc (_constraintGenFuns ()) in
    sfold_Expr_Expr _collectConstraints acc t

  sem initConstraint (graph: CFAGraph) =
  -- Intentionally left blank

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  -- Intentionally left blank

  -- CFAGraph -> Name -> Constraint -> CFAGraph
  sem _addEdge (graph: CFAGraph) (q: Name) =
  | cstr ->
    match _edgesLookup q graph with cstrsq in
    { graph with edges = mapInsert q (cons cstr cstrsq) graph.edges }

  -- Helper function for initializing a constraint for a given name (mainly
  -- used for convenience in initConstraint)
  sem _initConstraintName (name: Name) (graph: CFAGraph) =
  | cstr ->
    let graph = _addEdge graph name cstr in
    let avs = _dataLookup name graph in
    setFold (lam graph. lam av. propagateConstraint (name,av) graph cstr)
      graph avs

  sem _dataLookup (key: Name) =
  | graph ->
    let graph: CFAGraph = graph in
    mapLookupOrElse (lam. setEmpty cmpAbsVal) key graph.data

  sem _edgesLookup (key: Name) =
  | graph ->
    let graph: CFAGraph = graph in
    mapLookupOrElse (lam. []) key graph.edges

  -- CFAGraph -> AbsVal -> Name -> CFAGraph
  sem _addData (graph: CFAGraph) (d: AbsVal) =
  | q ->
    match _dataLookup q graph with dq in
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

lang DirectConstraint = CFA

  syn Constraint =
  -- lhs ⊆ rhs
  | CstrDirect { lhs: Name, rhs: Name }
  -- {lhs} ⊆ rhs
  | CstrDirectAv { lhs: AbsVal, rhs: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrDirect r & cstr -> _initConstraintName r.lhs graph cstr

  | CstrDirectAv r -> _addData graph r.lhs r.rhs

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrDirect r -> _addData graph update.1 r.rhs

  sem constraintToString (env: PprintEnv) =
  | CstrDirect { lhs = lhs, rhs = rhs } ->
    match pprintVarName env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    (env, join [lhs, " ⊆ ", rhs])
  | CstrDirectAv { lhs = lhs, rhs = rhs } ->
    match absValToString env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    (env, join ["{", lhs, "}", " ⊆ ", rhs])

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

lang LamCFA = CFA + DirectConstraint + LamAst

  -- Abstract representation of lambdas. The body can either be another
  -- abstract lambda or the exprName of the body.
  syn AbsVal =
  | AVLam { ident: Name, body: Either AbsVal Name }

  sem cmpAbsValH =
  | (AVLam { ident = lhs }, AVLam { ident = rhs }) ->
    nameCmp lhs rhs

  -- Type Expr -> Either AbsVal Name
  -- Convert a lambda to an Either AbsVal Name
  sem _lamBody =
  | t ->
    match t with TmLam t then
      let body = _lamBody t.body in
      Left (AVLam { ident = t.ident, body = body })
    else Right (exprName t)

  sem generateConstraints =
  | TmLet { ident = ident, body = TmLam t } ->
    let av: AbsVal = AVLam { ident = t.ident, body = _lamBody t.body } in
    [ CstrDirectAv { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVLam { ident = ident, body = body } ->
    match pprintVarName env ident with (env,ident) in
    let tmp =
      match body with Left av then absValToString env body
      else match body with Right n then pprintVarName env n
      else never
    in
    match tmp with (env, body) in
    (env, join ["lam ", ident, ". ", body])

end

lang AppCFA = CFA + DirectConstraint + LamCFA + AppAst

  syn Constraint =
  -- {lam x. b} ⊆ lhs ⇒ (rhs ⊆ x and b ⊆ res)
  | CstrApp { lhs: Name, rhs: Name, res: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrApp r & cstr -> _initConstraintName r.lhs graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrApp { lhs = lhs, rhs = rhs, res = res } ->
    -- Only lambda abstract values have an effect here.
    match update.1 with AVLam { ident = x, body = b } then
      -- Add rhs ⊆ x constraint
      let graph = initConstraint graph (CstrDirect { lhs = rhs, rhs = x }) in
      -- Add b ⊆ res constraint
      match b with Left av then
        _addData graph av res
      else match b with Right b then
        initConstraint graph (CstrDirect { lhs = b, rhs = res })
      else never

    -- Not a lambda abstract value
    else graph

  sem constraintToString (env: PprintEnv) =
  | CstrApp { lhs = lhs, rhs = rhs, res = res } ->
    match pprintVarName env lhs with (env,lhs) in
    match pprintVarName env rhs with (env,rhs) in
    match pprintVarName env res with (env,res) in
    (env, join [ "{lam >x<. >b<} ⊆ ", lhs, " ⇒ ", rhs, " ⊆ >x< and >b< ⊆ ", res ])

  sem generateConstraints =
  | TmLet { ident = ident, body = TmApp _ & body} ->
    recursive let rec = lam acc: [Constraint]. lam res: Name. lam t: Expr.
      match t with TmApp t then
        match t.lhs with TmApp _ | TmVar _ then
          let nameLhs =
            match t.lhs with TmApp t then nameSym "cfa"
            else match t.lhs with TmVar t then t.ident
            else error "Impossible"
          in
          let cstr =
            match t.rhs with TmVar { ident = nameRhs } then
              [CstrApp { lhs = nameLhs, rhs = nameRhs, res = res}]
            else []
          in
          let acc = concat cstr acc in
          match t.lhs with TmApp _ then rec acc nameLhs t.lhs else acc
        else acc
      else infoErrorExit (infoTm t)
             "Non-application in generateConstraints for TmApp"
    in rec [] ident body

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
        let av: AbsVal = AVLam { ident = t.ident, body = _lamBody t.body } in
        CstrDirectAv { lhs = av, rhs = b.ident }
      else infoErrorExit (infoTm b.body) "Not a lambda in recursive let body"
    ) bindings

end

lang ConstCFA = CFA + ConstAst

  sem generateConstraints =
  | TmConst t ->
    generateConstraintsConst t.info t.val

  sem generateConstraintsConst (info: Info) =
  | const -> infoErrorExit info "Constant not supported in CFA"

end

lang SeqCFA = CFA + DirectConstraint + SeqAst
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
    [ CstrDirectAv { lhs = av, rhs = ident } ]

  sem absValToString (env: PprintEnv) =
  | AVSeq { names = names } ->
    match mapAccumL pprintVarName env (setToSeq names) with (env,names) in
    let names = strJoin ", " names in
    (env, join ["[{", names, "}]"])

end

-- Empty name used in records and conapps
let nameEmpty = nameSym "cfaEmpty"

lang RecordCFA = CFA + DirectConstraint + RecordAst
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
      match v with TmVar t then t.ident else nameEmpty) t.bindings
    in
    let av: AbsVal = AVRec { bindings = bindings } in
    [ CstrDirectAv { lhs = av, rhs = ident } ]

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

lang DataCFA = CFA + DirectConstraint + DataAst
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
    let body = match t.body with TmVar t then t.ident else nameEmpty in
    let av: AbsVal = AVCon { ident = t.ident, body = body } in
    [ CstrDirectAv { lhs = av, rhs = ident } ]

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
  | CstrMatch { pat: Pat, target: Name }

  sem initConstraint (graph: CFAGraph) =
  | CstrMatch r & cstr -> _initConstraintName r.target graph cstr

  sem propagateConstraint (update: (Name,AbsVal)) (graph: CFAGraph) =
  | CstrMatch { pat = pat, target = target } ->
    propagateMatchConstraint graph (pat,update.1)

  sem propagateMatchConstraint (graph: CFAGraph) =
  | _ -> graph -- Default: do nothing

  sem constraintToString (env: PprintEnv) =
  | CstrMatch { pat = pat, target = target } ->
    match getPatStringCode 0 env pat with (env, pat) in
    match pprintVarName env target with (env, target) in
    (env, join ["match ", target, " with ", pat])

  sem generateConstraints =
  | TmLet { ident = ident, body = TmMatch t } ->
    let thnName = exprName t.thn in
    let elsName = exprName t.els in
    let cstr1 = [
      CstrDirect { lhs = thnName, rhs = ident },
      CstrDirect { lhs = elsName, rhs = ident }
    ] in
    let cstr2 = match t.target with TmVar tv then
        [ CstrMatch { pat = t.pat, target = tv.ident } ]
      else []
    in
    concat cstr1 cstr2

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
-- Most data-flow constraints will need to add things here. However, in this
-- base version of 0-CFA without data-flow, no data flow constraints are
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
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatNamed { ident = PName n }, av) ->
    _addData graph av n
  | (PatNamed { ident = PWildcard _ }, _) -> graph
end

lang SeqTotPatCFA = MatchCFA + SeqCFA + SeqTotPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatSeqTot p, AVSeq { names = names }) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph. lam name.
        let cstr = CstrMatch { pat = pat, target = name } in
        initConstraint graph cstr
      ) graph names in
    foldl f graph p.pats
end

lang SeqEdgePatCFA = MatchCFA + SeqCFA + SeqEdgePat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatSeqEdge p, AVSeq { names = names }) ->
    let f = lam graph. lam pat: Pat. setFold (lam graph. lam name.
        let cstr = CstrMatch { pat = pat, target = name } in
        initConstraint graph cstr
      ) graph names in
    let graph = foldl f graph p.prefix in
    let graph = foldl f graph p.postfix in
    match p.middle with PName rhs then
      foldl (lam graph. lam lhs: Name.
        let cstr = CstrDirect { lhs = lhs, rhs = rhs } in
        initConstraint graph cstr
      ) graph names
    else graph
end

lang RecordPatCFA = MatchCFA + RecordCFA + RecordPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatRecord { bindings = pbindings }, AVRec { bindings = abindings }) ->
    -- Check if record pattern is compatible with abstract value record
    let compatible = mapAllWithKey (lam k. lam. mapMem k abindings) pbindings in
    if compatible then
      mapFoldWithKey (lam graph. lam k. lam pb: Pattern.
        let ab: Name = mapFindExn k abindings in
        let cstr = CstrMatch { pat = pb, target = ab } in
        initConstraint graph cstr
      ) graph pbindings
    else graph -- Nothing to be done
end

lang DataPatCFA = MatchCFA + DataCFA + DataPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatCon p, AVCon { ident = ident, body = body }) ->
    if nameEq p.ident ident then
      let cstr = CstrMatch { pat = p.subpat, target = body } in
      initConstraint graph cstr
    else graph
end

lang IntPatCFA = MatchCFA + IntPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatInt p, _) -> graph
end

lang CharPatCFA = MatchCFA + CharPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatChar p, _) -> graph
end

lang BoolPatCFA = MatchCFA + BoolPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatBool p, _) -> graph
end

lang AndPatCFA = MatchCFA + AndPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatAnd p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

lang OrPatCFA = MatchCFA + OrPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatOr p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

lang NotPatCFA = MatchCFA + NotPat
  sem propagateMatchConstraint (graph: CFAGraph) =
  | (PatNot p, _) ->
    infoErrorExit p.info "Pattern currently unsupported in CFA"
end

---------------
-- MEXPR CFA --
---------------

lang MExprCFA = CFA +

  -- Base constraints
  DirectConstraint +

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

lang Test = MExprCFA + MExprANF + BootParser + MExprPrettyPrint

  -- Specify what functions to use when generating constraints
  sem _constraintGenFuns =
  | _ -> [generateConstraints]

end

mexpr
use Test in

-- Test functions --
let parse = parseMExprString [] in
let test: Bool -> Expr -> [String] -> [[AbsVal]] =
  lam debug: Bool. lam t: Expr. lam vars: [String].
    if debug then
      -- Version with debug printouts
      let tANF = normalizeTerm t in
      match pprintCode 0 pprintEnvEmpty t with (_,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 pprintEnvEmpty tANF with (env,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match cfaDebug env tANF with (env,cfaRes) in
      match cfaGraphToString env cfaRes with (_, resStr) in
      printLn "\n--- FINAL CFA GRAPH ---";
      printLn resStr;
      map (lam var: String.
        (var, _dataLookup (nameNoSym var) cfaRes)
      ) vars

    else
      -- Version without debug printouts
      let tANF = normalizeTerm t in
      let cfaRes = cfa tANF in
      map (lam var: String.
        (var, _dataLookup (nameNoSym var) cfaRes)
      ) vars
in

-- Custom equality function for testing lambda control flow only
let eqTestLam = eqSeq (lam t1:(String,Set AbsVal). lam t2:(String,[String]).
  if eqString t1.0 t2.0 then
    let t11 = setFold
      (lam acc. lam av.
       match av with AVLam { ident = i } then setInsert (nameGetStr i) acc
       else acc)
      (setEmpty cmpString) t1.1 in
    let t21 = setOfSeq cmpString t2.1 in
    setEq t11 t21
  else false
) in
--------------------

-- First test from Nielson et al.
let t = parse "
  (lam x. x) (lam y. y)
------------------------" in
utest test false t ["x","y"] with [
  ("x", ["y"]),
  ("y", [])
] using eqTestLam in

-- Second test from Nielson et al.
let t = parse "
  let f = lam x. x 1 in
  let g = lam y. addi y 2 in
  let h = lam z. addi z 3 in
  let res = addi (f g) (f h) in
  res
------------------------" in
utest test false t ["f","g","h","x","y","z","res"] with [
  ("f", ["x"]),
  ("g", ["y"]),
  ("h", ["z"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam in

-- Third test from Nielson et al.
let t = parse "
recursive let g = lam x. g (lam y. y) in
let res = g (lam z. z) in
res
------------------------" in
utest test false t ["g","x","y","z","res"] with [
  ("g", ["x"]),
  ("x", ["y","z"]),
  ("y", []),
  ("z", []),
  ("res", [])
] using eqTestLam in

-- Sequence
let t = parse "
  let f = lam x. x in
  let g = lam y. y in
  let seq = [f, lam z. z] in
  let res = match seq with [a] ++ _ then
      a g
    else
      (lam v. v)
  in res
------------------------" in
utest test false t ["res","a"] with [
  ("res", ["v","y"]),
  ("a", ["x","z"])
] using eqTestLam in

-- Record
let t = parse "
  let f = lam x. x in
  let g = lam y. y in
  let r = { a = f, b = 3 } in
  let res = match r with { a = a } then
      a g
    else
      (lam z. z)
  in res
------------------------" in
utest test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

-- ConApp
let t = parse "
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
utest test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

-- Nested
let t = parse "
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
utest test false t ["res","a"] with [
  ("res", ["y","z"]),
  ("a", ["x"])
] using eqTestLam in

()
