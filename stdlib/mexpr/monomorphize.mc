-- Eliminates occurrences of polymorphic types in the provided (typed) MExpr
-- AST, by replacing polymorphic functions by multiple monomorphic functions
-- (one for each distinct combination of types used to invoke the function).

include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

lang Monomorphize = MExprAst + MExprCmp + MExprPrettyPrint
  type MOptions = {
    -- Enable monomorphization of intrinsic functions. This means that distinct
    -- uses of, e.g., map will be bound to different let-bindings which use
    -- monomorphic types. For example, we may get
    --
    --   let mapIntInt : (Int -> Int) -> [Int] -> [Int] = lam f. lam s. map f s
    intrinsics : Bool
  }

  sem monomorphizeDefaultOptions : () -> MOptions
  sem monomorphizeDefaultOptions =
  | _ -> { intrinsics = true }

  -- An instantiation is a map from type variable identifiers to concrete
  -- types. An instantiation represents a concrete monomorphic use of a
  -- polymorphic construct. The aim of monomorphization is to replace the
  -- polymorphic constructs with monomorphic versions, corresponding to these
  -- uses.
  type Instantiation = Map Name Type

  -- The monomorphization state consists of a map from each polymorphic
  -- binding to its monomorphic instantiations and its polymorphic type. An
  -- instantiation is a map from type parameter names to concrete types. We map
  -- each instantiation to a distinct identifier, which is used when replacing
  -- the polymorphic functions with monomorphic versions.
  type InstEntry = {
    map : Map Instantiation Name,
    polyType : Type
  }
  type MonoState = Map Name InstEntry

  sem emptyInstantiation : () -> Instantiation
  sem emptyInstantiation =
  | _ -> mapEmpty nameCmp

  sem cmpInstantiation : Instantiation -> Instantiation -> Int
  sem cmpInstantiation lhs =
  | rhs -> mapCmp cmpType lhs rhs

  sem initInstEntry : Type -> InstEntry
  sem initInstEntry =
  | polyTy ->
    { map = mapEmpty cmpInstantiation, polyType = polyTy }

  sem printMonoState : MonoState -> String
  sem printMonoState =
  | state ->
    strJoin "\n"
      (mapFoldWithKey
        (lam acc. lam id. lam entry.
          let acc = snoc acc (concat "Binding:   " (nameGetStr id)) in
          let acc = snoc acc (concat "Poly type: " (type2str entry.polyType)) in
          mapFoldWithKey
            (lam acc. lam inst. lam.
              mapFoldWithKey
                (lam acc. lam paramId. lam ty.
                  snoc acc (join [nameGetStr paramId, " -> ", type2str ty]))
                acc inst)
            acc entry.map)
        ["Monomorphization state:"]
        state)

  sem findVariantName : Type -> Name
  sem findVariantName  =
  | TyAll t -> findVariantName t.ty
  | TyApp t -> findVariantName t.lhs
  | TyArrow t -> findVariantName t.to
  | TyCon t -> t.ident
  | ty -> errorSingle [infoTy ty] "Constructor type does not refer to a variant type"
end

lang MonomorphizeTypeInstantiation = Monomorphize
  -- NOTE(larshum, 2023-08-01): Finds the type parameter mapping of a
  -- monomorphic type with respect to its polymorphic type.
  sem findTypeParameterInstantiation : Type -> Type -> Instantiation
  sem findTypeParameterInstantiation polyType =
  | instType ->
    let polyType = unwrapType polyType in
    let pt = inspectType polyType in
    let it = unwrapType instType in
    let boundTypes = findBoundTypes (mapEmpty nameCmp) (pt, it) in
    constructInstantiationMapping boundTypes (emptyInstantiation ()) polyType

  sem constructInstantiationMapping : Map Name Type -> Instantiation -> Type -> Instantiation
  sem constructInstantiationMapping inst acc =
  | TyAll {ident = ident, ty = innerTy, info = info} ->
    let ty =
      match mapLookup ident inst with Some ty then
        match ty with TyUnknown {info = info} then
          TyRecord {fields = mapEmpty cmpSID, info = info}
        else ty
      else
        -- NOTE(larshum, 2023-08-01): We reach this case if the type parameter is
        -- never used. In this case, we choose to use the unit type (empty
        -- record). Note that any type would be valid in this case.
        TyRecord {fields = mapEmpty cmpSID, info = info}
    in
    constructInstantiationMapping inst (mapInsert ident ty acc) innerTy
  | _ ->
    acc

  sem findBoundTypes : Map Name Type -> (Type, Type) -> Map Name Type
  sem findBoundTypes acc =
  | (TyVar {ident = ident}, monoType) ->
    -- NOTE(larshum, 2023-08-01): We assume the instantiated type is well-typed
    -- with respect to the polymorphic type assigned to the type variable.
    mapInsert ident monoType acc
  | (TyArrow {from = f1, to = t1}, TyArrow {from = f2, to = t2}) ->
    let acc = findBoundTypes acc (f1, f2) in
    findBoundTypes acc (t1, t2)
  | (TySeq {ty = lty}, TySeq {ty = rty}) ->
    findBoundTypes acc (lty, rty)
  | (TyTensor {ty = lty}, TyTensor {ty = rty}) ->
    findBoundTypes acc (lty, rty)
  | (TyRecord {fields = lfields}, TyRecord {fields = rfields}) ->
    let mergefn = lam lval. lam rval.
      match (lval, rval) with (Some lty, Some rty) then
        Some (lty, rty)
      else
        error "Monomorphization error: Record field mismatch"
    in
    let f = lam acc. lam. lam tyPair.
      findBoundTypes acc tyPair
    in
    mapFoldWithKey f acc (mapMerge mergefn lfields rfields)
  | (TyApp {lhs = ll, rhs = lr}, TyApp {lhs = rl, rhs = rr}) ->
    let acc = findBoundTypes acc (ll, rl) in
    findBoundTypes acc (lr, rr)
  | (lty, rty) ->
    -- NOTE(larshum, 2023-08-01): In other cases, we accept the type and ignore
    -- its contents if both types have the same constructor tag.
    if eqi (constructorTag lty) (constructorTag rty) then acc
    else
      error "Monomorphization error: Unsupported polymorphic type instantiation"

  sem instantiateExpr : Instantiation -> Expr -> Expr
  sem instantiateExpr instMap =
  | t ->
    let t = smap_Expr_Type (instantiateType instMap) t in
    let t = smap_Expr_TypeLabel (instantiateType instMap) t in
    let t = smap_Expr_Pat (instantiatePat instMap) t in
    smap_Expr_Expr (instantiateExpr instMap) t

  sem instantiateType : Instantiation -> Type -> Type
  sem instantiateType instMap =
  | TyVar t ->
    match mapLookup t.ident instMap with Some ty then
      ty
    else TyVar t
  | ty ->
    smap_Type_Type (instantiateType instMap) ty

  sem instantiatePat : Instantiation -> Pat -> Pat
  sem instantiatePat instMap =
  | p ->
    let p = withTypePat (instantiateType instMap (tyPat p)) p in
    smap_Pat_Pat (instantiatePat instMap) p
end

lang MonomorphizeCollect = Monomorphize
  sem collectPolymorphic : Expr -> MonoState
  sem collectPolymorphic =
  | ast ->
    collectPolymorphicH (mapEmpty nameCmp) ast

  sem collectPolymorphicH : MonoState -> Expr -> MonoState
  sem collectPolymorphicH inst =
  | TmLet t ->
    let inst =
      match t.tyBody with TyAll _ then
        mapInsert t.ident (initInstEntry t.tyBody) inst
      else inst
    in
    let inst = collectPolymorphicH inst t.body in
    collectPolymorphicH inst t.inexpr
  | TmRecLets t ->
    let collectBind = lam inst. lam bind.
      let inst =
        match bind.tyBody with TyAll _ then
          mapInsert bind.ident (initInstEntry bind.tyBody) inst
        else inst
      in
      collectPolymorphicH inst bind.body
    in
    let inst = foldl collectBind inst t.bindings in
    collectPolymorphicH inst t.inexpr
  | TmType t ->
    let inst =
      if null t.params then inst
      else
        let ty =
          match t.tyIdent with TyVariant _ then
            foldr
              (lam paramId. lam accTy.
                TyAll {
                  ident = paramId, sort = MonoVar (), ty = accTy, info = t.info})
              (foldl
                (lam accTy. lam paramId.
                  TyApp {
                    lhs = accTy,
                    rhs = TyVar {ident = paramId, info = t.info},
                    info = t.info})
                (TyCon {ident = t.ident, info = t.info})
                t.params)
              t.params
          else
            t.tyIdent
        in
        mapInsert t.ident (initInstEntry ty) inst
    in
    collectPolymorphicH inst t.inexpr
  | TmConDef t ->
    let inst =
      match t.tyIdent with TyAll _ then
        mapInsert t.ident (initInstEntry t.tyIdent) inst
      else inst
    in
    collectPolymorphicH inst t.inexpr
  | t ->
    sfold_Expr_Expr collectPolymorphicH inst t
end

lang MonomorphizePropagate = Monomorphize + MonomorphizeTypeInstantiation
  sem propagateInstantiations : MonoState -> Expr -> MonoState
  sem propagateInstantiations state =
  | ast ->
    propagateInstantiationsExpr [emptyInstantiation ()] state ast

  sem propagateInstantiationsExpr : [Instantiation] -> MonoState -> Expr -> MonoState
  sem propagateInstantiationsExpr typeInstantiations state =
  | TmVar t ->
    match mapLookup t.ident state with Some instEntry then
      let f : Instantiation -> Instantiation = lam inst.
        let monoTy = instantiateType inst t.ty in
        findTypeParameterInstantiation instEntry.polyType monoTy
      in
      let updInstMap =
        foldl
          (lam instMap. lam inst.
            if mapMem inst instMap then instMap
            else mapInsert inst (nameSetNewSym t.ident) instMap)
          instEntry.map
          (map f typeInstantiations)
      in
      let instEntry = {instEntry with map = updInstMap} in
      mapInsert t.ident instEntry state
    else
      state
  | TmLet t ->
    let state = propagateInstantiationsExpr typeInstantiations state t.inexpr in
    let typeInstantiations =
      match mapLookup t.ident state with Some instEntry then
        let innerTypeInstantiations = mapKeys instEntry.map in
        -- NOTE(larshum, 2023-08-02): For each existing instantiation, we
        -- compute its union with every inner instantiation, and we store them
        -- all in the resulting sequence.
        join
          (map
            (lam outerInst. map (mapUnion outerInst) innerTypeInstantiations)
            typeInstantiations)
      else
        typeInstantiations
    in
    propagateInstantiationsExpr typeInstantiations state t.body
  | TmConDef t ->
    let state = propagateInstantiationsExpr typeInstantiations state t.inexpr in
    match mapLookup t.ident state with Some instEntry then
      let variantId = findVariantName t.tyIdent in
      match mapLookup variantId state with Some varInstEntry then
        -- NOTE(larshum, 2023-08-02): Convert a type instantiation of this
        -- constructor to the corresponding instantiation of its variant type.
        let f : Instantiation -> Instantiation = lam inst.
          let monoTy = inspectType (instantiateType inst t.tyIdent) in
          match monoTy with TyArrow {to = variantTy} then
            findTypeParameterInstantiation varInstEntry.polyType variantTy
          else
            errorSingle [t.info] "Monomorphization error: Invalid constructor type"
        in
        let varInstMap =
          mapFoldWithKey
            (lam instMap. lam inst. lam.
              let inst = f inst in
              if mapMem inst instMap then instMap
              else mapInsert inst (nameSetNewSym variantId) instMap)
            varInstEntry.map
            instEntry.map
        in
        let updEntry = {varInstEntry with map = varInstMap} in
        mapInsert variantId updEntry state
      else
        errorSingle [t.info]
          "Monomorphization error: Constructor belongs to unknown variant type"
    else
      state
  | TmConApp t ->
    let state =
      match mapLookup t.ident state with Some instEntry then
        let f : Instantiation -> Instantiation = lam inst.
          let resultTy = instantiateType inst t.ty in
          let monoTy = TyArrow {
            from = tyTm t.body, to = resultTy, info = t.info
          } in
          findTypeParameterInstantiation instEntry.polyType monoTy
        in
        let updInstMap =
          foldl
            (lam instMap. lam inst.
              if mapMem inst instMap then instMap
              else mapInsert inst (nameSetNewSym t.ident) instMap)
            instEntry.map
            (map f typeInstantiations)
        in
        let instEntry = {instEntry with map = updInstMap} in
        mapInsert t.ident instEntry state
      else
        state
    in
    propagateInstantiationsExpr typeInstantiations state t.body
  | t ->
    let state = sfold_Expr_Pat (propagateInstantiationsPat typeInstantiations) state t in
    sfold_Expr_Expr (propagateInstantiationsExpr typeInstantiations) state t

  sem propagateInstantiationsPat : [Instantiation] -> MonoState -> Pat -> MonoState
  sem propagateInstantiationsPat typeInstantiations state =
  | PatCon t ->
    let state =
      match mapLookup t.ident state with Some instEntry then
        let f : Instantiation -> Instantiation = lam inst.
          let resultTy = instantiateType inst t.ty in
          let monoTy = TyArrow {
            from = tyPat t.subpat, to = resultTy, info = t.info
          } in
          findTypeParameterInstantiation instEntry.polyType monoTy
        in
        let updInstMap =
          foldl
            (lam instMap. lam inst.
              if mapMem inst instMap then instMap
              else mapInsert inst (nameSetNewSym t.ident) instMap)
            instEntry.map
            (map f typeInstantiations)
        in
        let instEntry = {instEntry with map = updInstMap} in
        mapInsert t.ident instEntry state
      else
        state
    in
    propagateInstantiationsPat typeInstantiations state t.subpat
  | p ->
    sfold_Pat_Pat (propagateInstantiationsPat typeInstantiations) state p
end

lang MonomorphizeApply = MonomorphizeTypeInstantiation
  sem applyMonomorphization : MonoState -> Expr -> Expr
  sem applyMonomorphization state =
  | TmVar t ->
    match mapLookup t.ident state with Some instEntry then
      let varInst = findTypeParameterInstantiation instEntry.polyType t.ty in
      match mapLookup varInst instEntry.map with Some newId then
        TmVar {t with ident = newId}
      else
        error "Monomorphization error"
    else
      TmVar t
  | TmLet t ->
    let inexpr = applyMonomorphization state t.inexpr in
    match mapLookup t.ident state with Some instEntry then
      mapFoldWithKey
        (lam acc. lam inst. lam id.
          let body = instantiateExpr inst t.body in
          let body = applyMonomorphization state body in
          TmLet {
            ident = id, tyAnnot = instantiateType inst (inspectType t.tyAnnot),
            tyBody = instantiateType inst (inspectType t.tyBody), body = body,
            inexpr = acc, ty = TyUnknown {info = t.info}, info = t.info})
        inexpr
        instEntry.map
    else
      let body = applyMonomorphization state t.body in
      TmLet {t with body = body, inexpr = inexpr}
  | TmType t ->
    let inexpr = applyMonomorphization state t.inexpr in
    match mapLookup t.ident state with Some instEntry then
      mapFoldWithKey
        (lam acc. lam inst. lam id.
          TmType {
            ident = id, params = [], tyIdent = instantiateType inst t.tyIdent,
            inexpr = acc, ty = TyUnknown {info = t.info}, info = t.info})
        inexpr
        instEntry.map
    else
      TmType {t with inexpr = inexpr}
  | TmConDef t ->
    let inexpr = applyMonomorphization state t.inexpr in
    match mapLookup t.ident state with Some instEntry then
      mapFoldWithKey
        (lam acc. lam inst. lam id.
          let tyIdent = instantiateType inst (inspectType t.tyIdent) in
          TmConDef {
            ident = id, tyIdent = applyMonomorphizationType state tyIdent,
            inexpr = acc, ty = TyUnknown {info = t.info}, info = t.info})
        inexpr
        instEntry.map
    else
      TmConDef {t with inexpr = inexpr}
  | TmConApp t ->
    let newId =
      match mapLookup t.ident state with Some instEntry then
        let monoTy = TyArrow {from = tyTm t.body, to = t.ty, info = t.info} in
        let conInst = findTypeParameterInstantiation instEntry.polyType monoTy in
        match mapLookup conInst instEntry.map with Some newId then
          newId
        else
          error "Monomorphization error"
      else
        t.ident
    in
    TmConApp {t with ident = newId,
                     body = applyMonomorphization state t.body}
  | ast ->
    let ast = smap_Expr_Type (applyMonomorphizationType state) ast in
    let ast = smap_Expr_Pat (applyMonomorphizationPat state) ast in
    smap_Expr_Expr (applyMonomorphization state) ast

  sem applyMonomorphizationType : MonoState -> Type -> Type
  sem applyMonomorphizationType state =
  | ty & (TyCon _ | TyApp _) ->
    recursive let collect = lam acc. lam ty.
      switch ty
      case TyApp t then
        collect (cons t.rhs acc) t.lhs
      case _ then
        (ty, acc)
      end
    in
    match collect [] ty with (TyCon t, args) then
      match mapLookup t.ident state with Some instEntry then
        let conInst = findTypeParameterInstantiation instEntry.polyType ty in
        match mapLookup conInst instEntry.map with Some newId then
          TyCon {ident = newId, info = infoTy ty}
        else
          error "Monomorphization error"
      else
        error "Monomorphization error: Polymorphic constructor type not found"
    else
      smap_Type_Type (applyMonomorphizationType state) ty
  | ty -> smap_Type_Type (applyMonomorphizationType state) ty

  sem applyMonomorphizationPat : MonoState -> Pat -> Pat
  sem applyMonomorphizationPat state =
  | PatCon t ->
    let newId =
      match mapLookup t.ident state with Some instEntry then
        let monoTy = TyArrow {from = tyPat t.subpat, to = t.ty, info = t.info} in
        let conInst = findTypeParameterInstantiation instEntry.polyType monoTy in
        match mapLookup conInst instEntry.map with Some newId then
          newId
        else
          error "Monomorphization error"
      else
        t.ident
    in
    PatCon {t with ident = newId,
                   subpat = applyMonomorphizationPat state t.subpat}
  | p -> smap_Pat_Pat (applyMonomorphizationPat state) p
end

lang MExprMonomorphize =
  MonomorphizeTypeInstantiation + MonomorphizeCollect + MonomorphizePropagate +
  MonomorphizeApply

  sem collectBoundTypeParameters : [(Name, VarSort)] -> Type -> [(Name, VarSort)]
  sem collectBoundTypeParameters btp =
  | TyAll {ident = ident, sort = sort, ty = ty} ->
    let btp = snoc (ident, sort) in
    collectBoundTypeParameters btp ty
  | _ ->
    btp

  sem monomorphize : MOptions -> Expr -> Expr
  sem monomorphize options =
  | ast ->
    let state = collectPolymorphic ast in
    let state = propagateInstantiations state ast in
    printLn (printMonoState state);
    applyMonomorphization state ast
end

lang MExprMonomorphizeTest =
  MExprMonomorphize + MExprSym + MExprTypeCheck + MExprEq + MExprPrettyPrint

  sem isMonomorphic : Expr -> Bool
  sem isMonomorphic =
  | ast -> isMonomorphicExpr true ast

  sem isMonomorphicExpr : Bool -> Expr -> Bool
  sem isMonomorphicExpr acc =
  | e ->
    let acc = sfold_Expr_Expr isMonomorphicExpr acc e in
    let acc = sfold_Expr_Type isMonomorphicType acc e in
    let acc = sfold_Expr_Pat isMonomorphicPat acc e in
    isMonomorphicType acc (tyTm e)

  sem isMonomorphicType : Bool -> Type -> Bool
  sem isMonomorphicType acc =
  | TyAll _ | TyVar _ -> false
  | ty -> sfold_Type_Type isMonomorphicType acc ty

  sem isMonomorphicPat : Bool -> Pat -> Bool
  sem isMonomorphicPat acc =
  | p ->
    let acc = sfold_Pat_Pat isMonomorphicPat acc p in
    sfold_Pat_Type isMonomorphicType acc p
end

mexpr

use MExprMonomorphizeTest in

let preprocess = lam ast.
  typeCheck (symbolize ast)
in
let mm = lam ast.
  monomorphize (monomorphizeDefaultOptions ()) ast
in

-- Tests that we can correctly extract the type parameter mapping of a
-- monomorphic type given the polymorphic declaration type.

let nMapTy = lam fromTy. lam toTy.
  tyarrows_ [ tyint_, tyarrow_ fromTy toTy, tyseq_ fromTy, tyseq_ toTy ]
in
let polyNMapTy = tyall_ "a" (tyall_ "b" (nMapTy (tyvar_ "a") (tyvar_ "b"))) in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy tyint_ tyfloat_))
with [tyint_, tyfloat_] using eqSeq eqType in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy (tyseq_ tychar_) tyint_))
with [tyseq_ tychar_, tyint_] using eqSeq eqType in

utest mapValues (findTypeParameterInstantiation polyNMapTy (nMapTy tyunknown_ tyint_))
with [tyunit_, tyint_] using eqSeq eqType in

let someTy = lam tyArg. tyarrow_ tyArg (tyapp_ (tycon_ "Option") tyArg) in
let polySomeTy = tyall_ "a" (someTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polySomeTy (someTy tyint_))
with [tyint_] using eqSeq eqType in

let lenTy = lam elemTy.
  tyarrow_ (tyseq_ elemTy) tyint_
in
let polyLenTy = tyall_ "a" (lenTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polyLenTy (lenTy tyint_))
with [tyint_] using eqSeq eqType in

let polyTensorLenTy = tyall_ "a" (tyarrow_ (tytensor_ (tyvar_ "a")) tyint_) in
utest mapValues (findTypeParameterInstantiation polyTensorLenTy (tyarrow_ (tytensor_ tyint_) tyint_))
with [tyint_] using eqSeq eqType in

let projIdTy = lam poly.
  tyarrows_ [tyrecord_ [("a", poly), ("b", tyint_)], tyint_]
in
let polyProjTy = tyall_ "a" (projIdTy (tyvar_ "a")) in
utest mapValues (findTypeParameterInstantiation polyProjTy (projIdTy (tyseq_ tyfloat_)))
with [tyseq_ tyfloat_] using eqSeq eqType in

let polyty = tyall_ "a" (tyapp_ (tycon_ "Unknown") (tyvar_ "a")) in
let monoty = tyapp_ (tycon_ "Unknown") tyint_ in
utest mapValues (findTypeParameterInstantiation polyty monoty)
with [tyint_] using eqSeq eqType in

let accMapTy = lam a. lam b. lam c.
  tyarrows_ [tyarrows_ [a, b, tytuple_ [a, c]], a, tyseq_ b, tytuple_ [a, tyseq_ c]]
in
let polyAccMapTy =
  tyall_ "a" (tyall_ "b" (tyall_ "c" (accMapTy (tyvar_ "a") (tyvar_ "b") (tyvar_ "c"))))
in
let intAccMapTy = accMapTy tyint_ tyint_ tyint_ in
utest mapValues (findTypeParameterInstantiation polyAccMapTy intAccMapTy)
with [tyint_, tyint_, tyint_] using eqSeq eqType in

let leftPolyTy =
  tyall_ "a" (tyall_ "b" (tyarrow_ (tyvar_ "a") (tyapps_ (tycon_ "Either") [tyvar_ "a", tyvar_ "b"])))
in
let rightPolyTy =
  tyall_ "a" (tyall_ "b" (tyarrow_ (tyvar_ "b") (tyapps_ (tycon_ "Either") [tyvar_ "a", tyvar_ "b"])))
in
let leftTy = lam tyArg. tyarrow_ tyArg (tyapps_ (tycon_ "Either") [tyArg, tyunknown_]) in
let rightTy = lam tyArg. tyarrow_ tyArg (tyapps_ (tycon_ "Either") [tyunknown_, tyArg]) in
utest mapValues (findTypeParameterInstantiation leftPolyTy (leftTy tyint_))
with [tyint_, tyunit_] using eqSeq eqType in
utest mapValues (findTypeParameterInstantiation rightPolyTy (rightTy tyint_))
with [tyunit_, tyint_] using eqSeq eqType in

-- Tests that the propagation of monomorphic instantiations works as expected.

let f = nameSym "f" in
let g = nameSym "g" in
let sequentialPoly = preprocess (bindall_ [
  nulet_ f (ulam_ "x" (var_ "x")),
  nulet_ g (ulam_ "x" (app_ (nvar_ f) (var_ "x"))),
  utuple_ [app_ (nvar_ g) (int_ 2), app_ (nvar_ g) (float_ 2.5), app_ (nvar_ f) (char_ 'a')]
]) in
let state = collectPolymorphic sequentialPoly in
let state = propagateInstantiations state sequentialPoly in
-- NOTE(larshum, 2023-08-02): We verify that the entries for bindings f and g
-- have one entry for each monomorphic instantiation in the above expression.
-- As g depends on f, all monomorphic instantiations of g should be propagated
-- to f.
match mapLookup f state with Some fEntry in
utest mapSize fEntry.map with 3 in
match mapLookup g state with Some gEntry in
utest mapSize gEntry.map with 2 in

let opt = nameSym "Option" in
let some = nameSym "Some" in
let none = nameSym "None" in
let optionUse = preprocess (bindall_ [
  ntype_ opt [nameSym "a"] (tyvariant_ []),
  ncondef_ some (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (ntycon_ opt) (tyvar_ "a")))),
  ncondef_ none (tyall_ "a" (tyarrow_ tyunit_ (tyapp_ (ntycon_ opt) (tyvar_ "a")))),
  ulet_ "isSome" (ulam_ "o" (
    match_ (var_ "o") (npcon_ some pvarw_) true_ false_)),
  utuple_ [
    app_ (var_ "isSome") (nconapp_ some (int_ 2)),
    app_ (var_ "isSome") (nconapp_ some (float_ 2.5)),
    app_ (var_ "isSome") (nconapp_ none uunit_)]
]) in
let state = collectPolymorphic optionUse in
let state = propagateInstantiations state optionUse in
match mapLookup opt state with Some optEntry in
utest mapSize optEntry.map with 3 in
match mapLookup some state with Some someEntry in
utest mapSize someEntry.map with 3 in
match mapLookup none state with Some noneEntry in
utest mapSize noneEntry.map with 1 in

-- Tests for the entire monomorphization pass.

-- TODO: start enabling the below tests once all passes are ready to go

let monoFun = preprocess (bindall_ [
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "addOne") (int_ 3)
]) in
utest isMonomorphic monoFun with true in

let idPoly = preprocess (bindall_ [
  ulet_ "id" (ulam_ "x" (var_ "x")),
  utuple_ [app_ (var_ "id") (int_ 2), app_ (var_ "id") (float_ 2.5)]
]) in
let expected = preprocess (bindall_ [
  let_ "id_float" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
  let_ "id_int" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
  utuple_ [app_ (var_ "id_int") (int_ 2), app_ (var_ "id_float") (float_ 2.5)]
]) in
let result = mm idPoly in
utest isMonomorphic idPoly with false in
utest isMonomorphic result with true in
utest isMonomorphic expected with true in
utest result with expected using eqExpr in

--let mapPoly = preprocess (bindall_ [
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  ulet_ "x1" (map_ (var_ "addOne") (seq_ [int_ 2])),
--  ulet_ "x2" (map_ (var_ "addHalf") (seq_ [float_ 2.5]))
--]) in
--let result = mm mapPoly in
--let expected = preprocess (bindall_ [
--  let_ "mapInt" (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
--    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
--  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
--  ulet_ "x1" (appf2_ (var_ "mapInt") (var_ "addOne") (seq_ [int_ 2])),
--  let_ "mapFloat" (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
--    (ulam_ "f" (ulam_ "s" (map_ (var_ "f") (var_ "s")))),
--  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
--  ulet_ "x2" (appf2_ (var_ "mapFloat") (var_ "addHalf") (seq_ [float_ 2.5]))
--]) in
--utest result with expected using eqExpr in -- fails
--
let seqPoly = preprocess (bindall_ [
  ulet_ "g" (ulam_ "x" (var_ "x")),
  ulet_ "f" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
  utuple_ [app_ (var_ "f") (int_ 2), app_ (var_ "f") (float_ 2.5)]
]) in
let result = mm seqPoly in
let expected = preprocess (bindall_ [
  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
  let_ "fFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (app_ (var_ "gFloat") (var_ "x"))),
  let_ "fInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (app_ (var_ "gInt") (var_ "x"))),
  utuple_ [app_ (var_ "fInt") (int_ 2), app_ (var_ "fFloat") (float_ 2.5)]
]) in
utest isMonomorphic seqPoly with false in
utest isMonomorphic result with true in
utest isMonomorphic expected with true in
utest result with expected using eqExpr in

let nestedPoly = preprocess (bindall_ [
  ulet_ "f" (ulam_ "g" (ulam_ "s" (bindall_ [
    ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
    map_ (var_ "h") (var_ "s")
  ]))),
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  utuple_ [
    appf2_ (var_ "f") (var_ "addOne") (seq_ [int_ 2]),
    appf2_ (var_ "f") (var_ "addHalf") (seq_ [float_ 2.5])]
]) in
let result = mm nestedPoly in
let expected = preprocess (bindall_ [
  let_ "fFloat"
    (tyarrows_ [tyarrow_ tyfloat_ tyfloat_, tyseq_ tyfloat_, tyseq_ tyfloat_])
    (ulam_ "g" (ulam_ "s" (bindall_ [
      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
      map_ (var_ "h") (var_ "s")
  ]))),
  let_ "fInt"
    (tyarrows_ [tyarrow_ tyint_ tyint_, tyseq_ tyint_, tyseq_ tyint_])
    (ulam_ "g" (ulam_ "s" (bindall_ [
      ulet_ "h" (ulam_ "x" (app_ (var_ "g") (var_ "x"))),
      map_ (var_ "h") (var_ "s")
  ]))),
  ulet_ "addOne" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "addHalf" (ulam_ "x" (addf_ (var_ "x") (float_ 0.5))),
  utuple_ [
    appf2_ (var_ "fInt") (var_ "addOne") (seq_ [int_ 2]),
    appf2_ (var_ "fFloat") (var_ "addHalf") (seq_ [float_ 2.5])]
]) in
utest isMonomorphic nestedPoly with false in
utest isMonomorphic result with true in
utest isMonomorphic expected with true in
utest result with expected using eqExpr in

let innerPoly = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (ulam_ "y" (bindall_ [
    ulet_ "g" (ulam_ "z" (var_ "z")),
    utuple_ [app_ (var_ "g") (var_ "x"), app_ (var_ "g") (var_ "y")]
  ]))),
  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
]) in
let result = mm innerPoly in
let expected = preprocess (bindall_ [
  let_ "f" (tyarrows_ [tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
    (ulam_ "x" (ulam_ "y" (bindall_ [
      let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "z" (var_ "z")),
      let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "z" (var_ "z")),
      utuple_ [app_ (var_ "gInt") (var_ "x"), app_ (var_ "gFloat") (var_ "y")]
  ]))),
  appf2_ (var_ "f") (int_ 2) (float_ 2.5)
]) in
utest isMonomorphic innerPoly with false in
utest isMonomorphic result with true in
utest isMonomorphic expected with true in
utest result with expected using eqExpr in

--let higherOrderPoly = preprocess (bindall_ [
--  let_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a"))) (ulam_ "x" (var_ "x")),
--  ulet_ "f" (lam_ "g" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
--    (ulam_ "x" (ulam_ "y" (bindall_ [
--      ulet_ "a" (app_ (var_ "g") (var_ "x")),
--      ulet_ "b" (app_ (var_ "g") (var_ "y")),
--      utuple_ [var_ "a", var_ "b"]
--  ])))),
--  ulet_ "x1" (int_ 2),
--  ulet_ "x2" (float_ 2.5),
--  ulet_ "y" (appf3_ (var_ "f") (freeze_ (var_ "g")) (var_ "x1") (var_ "x2"))
--]) in
--let result = mm higherOrderPoly in
--let expected = preprocess (bindall_ [
--  let_ "gInt" (tyarrow_ tyint_ tyint_) (ulam_ "x" (var_ "x")),
--  let_ "gFloat" (tyarrow_ tyfloat_ tyfloat_) (ulam_ "x" (var_ "x")),
--  ulet_ "x1" (int_ 2),
--  ulet_ "x2" (float_ 2.5),
--  let_ "fIntFloat"
--    (tyarrows_ [tyarrow_ tyint_ tyint_, tyarrow_ tyfloat_ tyfloat_, tyint_, tyfloat_, tytuple_ [tyint_, tyfloat_]])
--    (ulam_ "gInt" (ulam_ "gFloat" (ulam_ "x" (ulam_ "y" (bindall_ [
--      ulet_ "a" (app_ (var_ "gInt") (var_ "x")),
--      ulet_ "b" (app_ (var_ "gFloat") (var_ "y")),
--      utuple_ [var_ "a", var_ "b"]
--  ]))))),
--  ulet_ "y" (appf4_ (var_ "fIntFloat") (var_ "gInt") (var_ "gFloat") (var_ "x1") (var_ "x2"))
--]) in
--utest isMonomorphic higherOrderPoly with false in
--utest isMonomorphic result with true in -- fails
--utest isMonomorphic expected with true in
--utest result with expected using eqExpr in -- fails
--
let polyVariant = preprocess (bindall_ [
  type_ "Option" ["a"] (tyvariant_ []),
  condef_ "Some" (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
  condef_ "None" (tyall_ "a" (tyarrow_ (tytuple_ []) (tyapp_ (tycon_ "Option") (tyvar_ "a")))),
  ulet_ "isSome" (ulam_ "o" (
    match_ (var_ "o") (pcon_ "Some" pvarw_) true_ false_)),
  utuple_ [
    app_ (var_ "isSome") (conapp_ "Some" (int_ 2)),
    app_ (var_ "isSome") (conapp_ "Some" (float_ 2.5)),
    app_ (var_ "isSome") (conapp_ "None" uunit_)
  ]
]) in
let result = mm polyVariant in
-- NOTE(larshum, 2023-06-28): When type parameters are not used, they are set
-- to unknown. In this case, when constructing a None, we don't use the type
-- parameter. The monomorphization should replace it with the Unit type (empty
-- record).
let expected = preprocess (bindall_ [
  type_ "Option" [] (tyvariant_ []),
  type_ "Option1" [] (tyvariant_ []),
  type_ "Option2" [] (tyvariant_ []),
  condef_ "Some" (tyarrow_ tyunit_ (tycon_ "Option")),
  condef_ "Some1" (tyarrow_ tyfloat_ (tycon_ "Option1")),
  condef_ "Some2" (tyarrow_ tyint_ (tycon_ "Option2")),
  condef_ "None" (tyarrow_ (tytuple_ []) (tycon_ "Option")),
  -- TODO(larshum, 2023-08-02): Is it correct to not include these constructors
  -- in the monomorphization stage? They are never used; however, this means
  -- the resulting monomorphic types are "incomplete" in some sense. On the
  -- other hand, this may allow us to make additional optimizations.
  --condef_ "None1" (tyarrow_ (tytuple_ []) (tycon_ "Option1")),
  --condef_ "None2" (tyarrow_ (tytuple_ []) (tycon_ "Option2")),
  ulet_ "isSome"
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "Some" pvarw_) true_ false_)),
  ulet_ "isSome1"
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "Some1" pvarw_) true_ false_)),
  ulet_ "isSome2"
    (ulam_ "o" (
      match_ (var_ "o") (pcon_ "Some2" pvarw_) true_ false_)),
  utuple_ [
    app_ (var_ "isSome2") (conapp_ "Some2" (int_ 2)),
    app_ (var_ "isSome1") (conapp_ "Some1" (float_ 2.5)),
    app_ (var_ "isSome") (conapp_ "None" uunit_)
  ]
]) in
printLn (expr2str result);
printLn (expr2str expected);
utest isMonomorphic polyVariant with false in
utest isMonomorphic result with true in
--utest mexprToString result with mexprToString expected using eqString in -- fails

()
