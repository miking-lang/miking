include "mexpr/call-graph.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"

lang PMExprClassify = PMExprAst + PMExprExtractAccelerate + MExprCallGraph
  syn Class =
  | Any ()
  | Cuda ()
  | Futhark ()
  | Invalid ()

  type ClassificationEnv = Map Name (Info, Class)
  type ClassificationResult = Map Class (Map Name AccelerateData, Expr)

  sem cmpClass : Class -> Class -> Int
  sem cmpClass lhs =
  | rhs -> subi (constructorTag lhs) (constructorTag rhs)

  sem lub : Class -> Class -> Class
  sem lub lhs =
  | rhs -> lubH (lhs, rhs)

  sem lubH : (Class, Class) -> Class
  sem lubH =
  | (Any _, rhs) -> rhs
  | (lhs & !(Any _), Any _) -> lhs
  | (Cuda _, Cuda _) -> Cuda ()
  | (Futhark _, Futhark _) -> Futhark ()
  | _ -> Invalid ()

  sem classify : Expr -> (Name, ClassificationEnv)
  sem classify =
  | e ->
    -- NOTE(larshum, 2022-06-02): We use an empty name as the name of the
    -- top-level expressions. It is returned with the classification map as its
    -- symbol must be known to distinguish it from sequencing expressions.
    let emptyNameId = nameSym "" in
    (emptyNameId, classifyH (mapEmpty nameCmp) emptyNameId e)

  sem classifyH : ClassificationEnv -> Name -> Expr -> ClassificationEnv
  sem classifyH env id =
  | TmLet t ->
    let env = classifyH env t.ident t.body in
    classifyH env id t.inexpr
  | TmRecLets t ->
    let bindMap : Map Name RecLetBinding =
      mapFromSeq nameCmp
        (map (lam bind. (bind.ident, bind)) t.bindings) in
    let f : ClassificationEnv -> [Name] -> ClassificationEnv = lam env. lam binds.
      let bindingLub : Class -> Name -> Class = lam acc. lam bindId.
        match mapLookup bindId bindMap with Some binding then
          classifyBody env acc binding.body
        else errorSingle [t.info] "Classification of expression failed"
      in
      let lub = foldl bindingLub (Any ()) binds in
      foldl (lam env. lam bindId. mapInsert bindId (t.info, lub) env) env binds
    in
    -- NOTE(larshum, 2022-06-02): First, we assume all bindings are have been
    -- classified as 'Any'. Next, we classify them independently under this
    -- assumption. Finally, we propagate the classification results using the
    -- least upper bound of all classifications of each strongly connected
    -- component.
    let env =
      foldl
        (lam env. lam bind. mapInsert bind.ident (t.info, Any ()) env)
        env t.bindings in
    let env =
      foldl
        (lam env. lam bind. classifyH env bind.ident bind.body)
        env t.bindings in
    let g : Digraph Name Int = constructCallGraph (TmRecLets t) in
    let sccs = digraphTarjan g in
    let env = foldl f env (reverse sccs) in
    classifyH env id t.inexpr
  | TmType t -> classifyH env id t.inexpr
  | TmConDef t -> classifyH env id t.inexpr
  | TmUtest t -> classifyH env id t.next
  | TmExt t -> classifyH env id t.inexpr
  | e ->
    let class = classifyBody env (Any ()) e in
    mapInsert id (infoTm e, class) env

  sem classifyBody : ClassificationEnv -> Class -> Expr -> Class
  sem classifyBody env acc =
  | TmVar t ->
    match mapLookup t.ident env with Some (_, class) then
      lub acc class
    else acc
  | TmConst t -> lub acc (classifyConst t.val)
  | (TmLoop _ | TmLoopAcc _ | TmParallelLoop _ | TmPrintFloat _) & t ->
    sfold_Expr_Expr (classifyBody env) (lub acc (Cuda ())) t
  | ( TmFlatten _ | TmMap2 _ | TmParallelReduce _ | TmParallelSizeCoercion _
    | TmParallelSizeEquality _ ) & t ->
    sfold_Expr_Expr (classifyBody env) (lub acc (Futhark ())) t
  | e -> sfold_Expr_Expr (classifyBody env) acc e

  sem classifyConst : Const -> Class
  sem classifyConst =
  | CMap _ -> Futhark ()
  | _ -> Any ()

  sem classifyAccelerated : Map Name AccelerateData -> Expr
                         -> ClassificationResult
  sem classifyAccelerated accelerated =
  | ast ->
    match classify ast with (_, classification) in
    let classifiedAccelerateIds : Map Class (Map Name AccelerateData) =
      mapFoldWithKey
        (lam acc. lam id. lam entry.
          match entry with (info, class) in
          match mapLookup id accelerated with Some data then
            let cl =
              match class with Any _ then
                errorSingle [info]
                  (join [ "The accelerate expression does not use any "
                        , "parallel keywords. This is not allowed." ])
              else match class with Invalid _ then
                errorSingle [info]
                  (join [ "Accelerate expression uses parallel "
                        , "keywords of multiple backends" ])
              else class in
            let singleton = mapFromSeq nameCmp [(id, data)] in
            mapInsertWith mapUnion cl singleton acc
          else acc)
        (mapEmpty cmpClass) classification in
    mapMapWithKey
      (lam. lam data.
        let extractIds = mapMapWithKey (lam. lam. ()) data in
        (data, extractAccelerateTerms extractIds ast))
      classifiedAccelerateIds
end

lang TestLang = PMExprClassify + MExprSym + MExprTypeCheck
end

mexpr

use PMExprClassify in

let cmpResult : (String, Class) -> (String, Class) -> Int = lam lhs. lam rhs.
  cmpString lhs.0 rhs.0
in

let classifyExpr : Expr -> [(String, Class)] = lam expr.
  let expr = typeCheck (symbolize expr) in
  match classify expr with (_, classification) in
  sort
    cmpResult
    (map
      (lam result. match result with (id, (_, class)) in (nameGetStr id, class))
      (mapBindings classification))  
in

utest classifyExpr (addi_ (int_ 1) (int_ 2)) with [("", Any ())] in
utest classifyExpr (loop_ (int_ 2) (ulam_ "x" unit_))
with [("", Cuda ())] in
utest classifyExpr (map_ (ulam_ "x" (var_ "x")) (seq_ [int_ 1]))
with [("", Futhark ())] in

let t = bindall_ [
  ulet_ "f" (ulam_ "n" (loop_ (var_ "n") (ulam_ "x" unit_))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "h") (subi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "y" (app_ (var_ "f") (var_ "y")))
  ]
] in
utest classifyExpr t
with [("", Any ()), ("f", Cuda ()), ("g", Cuda ()), ("h", Cuda ())] in

()
