include "./ast.mc"
include "./solve.mc"

lang COPHighLevel = COPSolve
  syn COPType a =
  -- NOTE(vipa, 2023-04-24): These should be GADT constrained to `a = Int` and the like
  | COPTypeInt { min : Int, max : Int }
  | COPTypeBool
  -- NOTE(vipa, 2023-04-24): These are correct
  | COPTypeEnum { alternatives : Ref (Map a Int, [a]) }

  syn COPDomain =
  -- NOTE(vipa, 2023-04-27): We use this type because we cannot store
  -- a `COPType a` with an unknown `a`, since we do not support
  -- existentials.
  | COPDomainDeferredEnum { numValues : () -> Int }

  sem pprintCOPDomain env =
  | COPDomainDeferredEnum x ->
    let dom = COPDomainIntRange
      { min = COPExprInt {value = 0}
      , max = COPExprInt {value = subi (x.numValues ()) 1}
      } in
    pprintCOPDomain env dom

  -- NOTE(vipa, 2023-04-24): This should be considered opaque
  type COPVar a =
    { domain : Option (Set a)
    , solution : Ref (Option a)
    , name : Name
    }

  -- A function to add an additional parameter of a given type to a
  -- function/predicate. The returned expr represents the value of the
  -- parameter in the body of the function. Note that the parameter is
  -- added through a side-effect; the arguments are passed in order to
  -- the corresponding call of this function.
  type AddParam = all a. COPType a -> COPExpr

  -- NOTE(vipa, 2023-04-24): This would ideally be an extensible
  -- record somehow, which is tricky because it has to be returned
  -- from a function to produce some new shared state.
  type API =
    -- Setting up the model to solve
    { newVar : all a. COPType a -> String -> COPVar a
    , newConstrainedVar : all a. COPType a -> String -> Set a -> COPVar a
    , newConstraint : COPExpr -> ()
    -- Triggering a solve
    , solve : () -> COPSolverResult
    , minimize : COPExpr -> COPSolverResult
    , maximize : COPExpr -> COPSolverResult
    -- Reading variables after solving. Fails if no solution has been found.
    , readVar : all a. COPVar a -> a

    -- Types and variables
    , boolTy : COPType Bool
    , intRangeTy : Int -> Int -> COPType Int
    , newEnumType : all a. (a -> a -> Int) -> COPType a -- TODO(vipa, 2023-04-25): The comparison function is annoying
    , registerValue : all a. COPType a -> a -> ()
    , registerValues : all a. COPType a -> Set a -> ()

    -- Functions and predicates
    , declFunc : all ret. COPType ret -> (AddParam -> COPExpr) -> [COPExpr] -> COPExpr
    , declPred : (AddParam -> COPExpr) -> [COPExpr] -> COPExpr

    -- Misc/non-standard constructs
    , elimEnum : all a. COPType a -> COPExpr -> (a -> COPExpr) -> COPExpr
    , enum : all a. COPType a -> a -> COPExpr
    , var : all a. COPVar a -> COPExpr
    , ifte : COPExpr -> COPExpr -> COPExpr -> COPExpr
    , switchDef : COPExpr -> [(COPExpr, COPExpr)] -> COPExpr -> COPExpr

    -- Constructs that range over all members of a type
    , forall : all a. COPType a -> (COPExpr -> COPExpr) -> COPExpr
    , sum : all a. COPType a -> (COPExpr -> COPExpr) -> COPExpr

    -- Arithmetic
    , add : COPExpr -> COPExpr -> COPExpr
    , addMany : [COPExpr] -> COPExpr
    , sub : COPExpr -> COPExpr -> COPExpr
    , mul : COPExpr -> COPExpr -> COPExpr
    , mulMany : [COPExpr] -> COPExpr
    , div : COPExpr -> COPExpr -> COPExpr

    -- Comparators
    , eq : COPExpr -> COPExpr -> COPExpr
    , ne : COPExpr -> COPExpr -> COPExpr
    , le : COPExpr -> COPExpr -> COPExpr
    , ge : COPExpr -> COPExpr -> COPExpr
    , lt : COPExpr -> COPExpr -> COPExpr
    , gt : COPExpr -> COPExpr -> COPExpr

    -- Boolean logic
    , and : COPExpr -> COPExpr -> COPExpr
    , andMany : [COPExpr] -> COPExpr
    , or : COPExpr -> COPExpr -> COPExpr
    , orMany : [COPExpr] -> COPExpr
    , not : COPExpr -> COPExpr

    -- Literals
    , int : Int -> COPExpr
    , float : Float -> COPExpr
    , bool : Bool -> COPExpr
    }

  sem _handleResult : Map Name (COPVarValue -> ()) -> COPSolverResult -> COPSolverResult
  sem _handleResult updaters =
  | res & COPSolution x ->
    mapIntersectWith (lam f. lam val. f val) updaters x.solution;
    res
  | res -> res

  sem _decodeVar : all a. Ref (Option a) -> COPType a -> (COPVarValue -> ())
  sem _decodeVar ref =
  | COPTypeEnum x -> lam var.
    match var with COPInt {val = v} in
    let v = get (deref x.alternatives).1 v in
    modref ref (Some v)
  | COPTypeBool _ -> lam var.
    match var with COPBool {val = v} in
    let gadtFixer : Bool -> a = unsafeCoerce in
    modref ref (Some (gadtFixer v))
  | COPTypeInt _ -> lam var.
    match var with COPInt {val = v} in
    let gadtFixer : Int -> a = unsafeCoerce in
    modref ref (Some (gadtFixer v))

  -- NOTE(vipa, 2023-04-28): This function assumes that the value in
  -- question has been registered for the type
  sem _encodeVal : all a. a -> COPType a -> COPExpr
  sem _encodeVal val =
  | COPTypeEnum x ->
    match mapLookup val (deref x.alternatives).0
    with Some i then COPExprInt { value = i }
    else error "Attempting to encode an unregistered value"

  sem _mkVarDecl : all a. Option (Set a) -> Name -> COPType a -> COPDecl
  sem _mkVarDecl dom name =
  | COPTypeEnum x ->
    let domain =
      match dom with Some dom then
        let toExpr = lam. lam i. COPExprInt {value = i} in
        COPDomainSet { values = mapValues (mapIntersectWith toExpr dom (deref x.alternatives).0) }
      else COPDomainDeferredEnum { numValues = lam. length (deref x.alternatives).1 } in
    COPVarDecl { id = name, domain = domain }

  sem newModel : () -> API
  sem newModel = | _ ->
    let varUpdaters : Ref (Map Name (COPVarValue -> ())) = ref (mapEmpty nameCmp) in
    let decls : Ref [COPDecl] = ref [] in
    let registerValues : all a. COPType a -> Set a -> () = lam ty. lam vals.
      match ty with COPTypeEnum x then
        match deref x.alternatives with (aToInt, intToA) in
        let newA = mapDifference vals aToInt in
        let addIndex = lam acc. lam. lam. (addi acc 1, acc) in
        let newA = (mapMapAccum addIndex (length intToA) newA).1 in
        modref x.alternatives (mapUnion aToInt newA, concat intToA (mapKeys newA))
      else () in
    let registerValue : all a. COPType a -> a -> () = lam ty. lam value.
      match ty with COPTypeEnum x then
        match deref x.alternatives with (aToInt, intToA) in
        if optionIsNone (mapLookup value aToInt) then
          modref x.alternatives (mapInsert value (length intToA) aToInt, snoc intToA value)
        else ()
      else () in
    let mkVar : all a. String -> Option (Set a) -> COPType a -> COPVar a = lam name. lam dom. lam ty.
      let r = ref (None ()) in
      let n = nameSym name in
      (match dom with Some dom then registerValues ty dom else ());
      modref varUpdaters (mapInsert n (_decodeVar r ty) (deref varUpdaters));
      modref decls (snoc (deref decls) (_mkVarDecl dom n ty));
      { domain = dom
      , solution = r
      , name = n
      } in
    let api : API =
      { newVar =
        let f : all a. COPType a -> String -> COPVar a = lam ty. lam name. mkVar name (None ()) ty
        in #frozen"f"
      , newConstrainedVar =
        let f : all a. COPType a -> String -> Set a -> COPVar a = lam ty. lam name. lam dom. mkVar name (Some dom) ty
        in #frozen"f"
      , newConstraint = lam constraint.
        modref decls (snoc (deref decls) (COPConstraintDeclExpr { constraint = constraint }))
      , solve = lam. _handleResult
        (deref varUpdaters)
        (solve (deref decls))
      , minimize = lam expr.
        let obj = COPObjectiveMinimize {expr = expr} in
        _handleResult
          (deref varUpdaters)
          (solve (snoc (deref decls) (COPObjectiveDecl {objective = obj})))
      , maximize = lam expr.
        let obj = COPObjectiveMinimize {expr = COPExprSub{left = COPExprInt {value = 0}, right = expr}} in
         _handleResult
          (deref varUpdaters)
          (solve (snoc (deref decls) (COPObjectiveDecl {objective = obj})))
      , readVar =
        let f : all a. COPVar a -> a = lam var.
          match deref var.solution with Some x then x else
          error "Called readVar on a variable without first finding a solution to its model."
        in #frozen"f"

      , boolTy = COPTypeBool {}
      , intRangeTy = lam min. lam max. COPTypeInt { min = min, max = max }
      , newEnumType =
        let f : all a. (a -> a -> Int) -> COPType a = lam cmp.
          COPTypeEnum { alternatives = ref (mapEmpty cmp, []) }
        in #frozen"f"
      , registerValue = #frozen"registerValue"
      , registerValues = #frozen"registerValues"

      , declFunc =
        let f : all ret. COPType ret -> (AddParam -> COPExpr) -> [COPExpr] -> COPExpr = lam. never
        in #frozen"f"
      , declPred = lam f : AddParam -> COPExpr. never

      , elimEnum =
        let f : all a. COPType a -> COPExpr -> (a -> COPExpr) -> COPExpr = lam. never
        in #frozen"f"
      , enum =
        let f : all a. COPType a -> a -> COPExpr = lam ty. lam val.
          registerValue ty val;
          _encodeVal val ty
        in #frozen"f"
      , var =
        let f : all a. COPVar a -> COPExpr = lam var. COPExprVar { id = var.name }
        in #frozen"f"
      , ifte = lam c. lam t. lam e. COPExprIfThenElse {cond = c, ifTrue = t, ifFalse = e}
      , switchDef = lam scrutinee. lam cases. lam default.
        let f : (COPExpr, COPExpr) -> COPExpr -> COPExpr = lam pair. lam acc.
          COPExprIfThenElse
          { cond = COPExprEq {left = scrutinee, right = pair.0}
          , ifTrue = pair.1
          , ifFalse = acc
          }
        in foldr f default cases

      , forall =
        let f : all a. COPType a -> (COPExpr -> COPExpr) -> COPExpr = lam. never
        in #frozen"f"
      , sum =
        let f : all a. COPType a -> (COPExpr -> COPExpr) -> COPExpr = lam. never
        in #frozen"f"

      , add = lam l. lam r. COPExprAdd {exprs = [l, r]}
      , addMany = lam es. COPExprAdd {exprs = es}
      , sub = lam l. lam r. COPExprSub {left = l, right = r}
      , mul = lam l. lam r. COPExprMul {exprs = [l, r]}
      , mulMany = lam es. COPExprMul {exprs = es}
      , div = lam l. lam r. COPExprDiv {left = l, right = r}

      , eq = lam l. lam r. COPExprEq {left = l, right = r}
      , ne = lam l. lam r. COPExprNe {left = l, right = r}
      , le = lam l. lam r. COPExprLe {left = l, right = r}
      , ge = lam l. lam r. COPExprGe {left = l, right = r}
      , lt = lam l. lam r. COPExprLt {left = l, right = r}
      , gt = lam l. lam r. COPExprGt {left = l, right = r}

      , and = lam l. lam r. COPExprAnd {exprs = [l, r]}
      , andMany = lam es. COPExprAnd {exprs = es}
      , or = lam l. lam r. COPExprOr {exprs = [l, r]}
      , orMany = lam es. COPExprOr {exprs = es}
      , not = lam x. COPExprNot {expr = x}

      , int = lam v. COPExprInt {value = v}
      , float = lam v. COPExprFloat {value = v}
      , bool = lam v. COPExprBool {value = v}
      }
    in api
end
