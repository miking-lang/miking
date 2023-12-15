-- Unification of MExpr types.  See type-check.mc for an overview of
-- the type checker.

include "result.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"
include "mexpr/info.mc"
include "mexpr/type.mc"


----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = KindAst
  type UnifyEnv = {
    wrappedLhs: Type,  -- The currently examined left-hand subtype, before resolving aliases
    wrappedRhs: Type,  -- The currently examined right-hand subtype, before resolving aliases
    boundNames: BiNameMap  -- The bijective correspondence between bound variables in scope
  }

  syn UnifyError =
  | Types (Type, Type)
  | Rows (Map SID Type, Map SID Type)
  | Kinds (Kind, Kind)

  type Unifier u = {
    empty : u,
    combine : u -> u -> u,
    unify : UnifyEnv -> Type -> Type -> u,
    unifyRepr : UnifyEnv -> ReprVar -> ReprVar -> u,
    err : UnifyError -> u
  }

  -- Unify the types `ty1` and `ty2` under the assumptions of `env`.
  -- Takes an abstract type `u` satisfying the interface `Unifier` to
  -- perform the actual variable unifications.
  -- For an example usage, see `unifyPure` below.
  sem unifyTypes : all u. Unifier u -> UnifyEnv -> (Type, Type) -> u
  sem unifyTypes u env =
  | (ty1, ty2) ->
    unifyBase u
      {env with wrappedLhs = ty1, wrappedRhs = ty2}
      (unwrapType ty1, unwrapType ty2)

  -- unifyBase env (ty1, ty2) unifies ty1 and ty2 under the
  -- assumptions of env.
  -- IMPORTANT: Assumes that ty1 = unwrapType env.wrappedLhs and
  -- ty2 = unwrapType env.wrappedRhs.
  sem unifyBase : all u. Unifier u -> UnifyEnv -> (Type, Type) -> u
  sem unifyBase u env =
  | (ty1, ty2) ->
    u.err (Types (ty1, ty2))
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyRows = Unify
  -- Check that 'm1' is a subset of 'm2'
  sem unifyRowsSubset : all u. Unifier u -> UnifyEnv -> Map SID Type -> Map SID Type -> u
  sem unifyRowsSubset u env m1 =
  | m2 ->
    let f = lam acc. lam b.
      let unifier =
        match b with (k, tyfield1) in
        match mapLookup k m2 with Some tyfield2 then
          unifyTypes u env (tyfield1, tyfield2)
        else
          u.err (Rows (m1, m2))
      in
      u.combine acc unifier
    in
    foldl f u.empty (mapBindings m1)

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyRowsStrict : all u. Unifier u -> UnifyEnv -> Map SID Type -> Map SID Type -> u
  sem unifyRowsStrict u env m1 =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyRowsSubset u env m1 m2
    else
      u.err (Rows (m1, m2))

  -- Check that the intersection of 'm1' and 'm2' unifies, then return their union
  sem unifyRowsUnion : all u. Unifier u -> UnifyEnv -> Map SID Type -> Map SID Type -> (u, Map SID Type)
  sem unifyRowsUnion u env m1 =
  | m2 ->
    let f = lam acc. lam b.
      match b with (k, tyfield1) in
      match mapLookup k acc.1 with Some tyfield2 then
        (u.combine acc.0 (unifyTypes u env (tyfield1, tyfield2)), acc.1)
      else
        (acc.0, mapInsert k tyfield1 acc.1)
    in
    foldl f (u.empty, m2) (mapBindings m1)
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase u env =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then u.empty
    else if biMem (t1.ident, t2.ident) env.boundNames then u.empty
    else u.err (Types (ty1, ty2))
end

lang MetaVarTypeUnify = Unify + MetaVarTypeAst
  sem unifyBase u env =
  | (TyMetaVar _ & ty1, ty2) -> u.unify env ty1 ty2
  | (!TyMetaVar _ & ty1, TyMetaVar _ & ty2) ->
    unifyBase u {env with wrappedLhs = env.wrappedRhs, wrappedRhs = env.wrappedLhs} (ty2, ty1)
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase u env =
  | (TyArrow t1, TyArrow t2) ->
    u.combine
      (unifyTypes u env (t1.from, t2.from))
      (unifyTypes u env (t1.to, t2.to))
end

lang AppTypeUnify = Unify + AppTypeAst
  sem unifyBase u env =
  | (TyApp t1, TyApp t2) ->
    u.combine
      (unifyTypes u env (t1.lhs, t2.lhs))
      (unifyTypes u env (t1.rhs, t2.rhs))
end

lang AllTypeUnify = UnifyRows + AllTypeAst
  sem unifyBase u env =
  | (TyAll t1, TyAll t2) ->
    u.combine
      (match (t1.kind, t2.kind) with (Row r1, Row r2) then
        unifyRowsStrict u env r1.fields r2.fields
       else if eqi (constructorTag t1.kind) (constructorTag t2.kind) then u.empty
            else u.err (Kinds (t1.kind, t2.kind)))
      (let env = {env with boundNames = biInsert (t1.ident, t2.ident) env.boundNames} in
       unifyTypes u env (t1.ty, t2.ty))
end

lang ConTypeUnify = Unify + ConTypeAst
  sem unifyBase u env =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then u.empty
    else u.err (Types (ty1, ty2))
end

lang BoolTypeUnify = Unify + BoolTypeAst
  sem unifyBase u env =
  | (TyBool _, TyBool _) -> u.empty
end

lang IntTypeUnify = Unify + IntTypeAst
  sem unifyBase u env =
  | (TyInt _, TyInt _) -> u.empty
end

lang FloatTypeUnify = Unify + FloatTypeAst
  sem unifyBase u env =
  | (TyFloat _, TyFloat _) -> u.empty
end

lang CharTypeUnify = Unify + CharTypeAst
  sem unifyBase u env =
  | (TyChar _, TyChar _) -> u.empty
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase u env =
  | (TySeq t1, TySeq t2) ->
    unifyTypes u env (t1.ty, t2.ty)
end

lang TensorTypeUnify = Unify + TensorTypeAst
  sem unifyBase u env =
  | (TyTensor t1, TyTensor t2) ->
    unifyTypes u env (t1.ty, t2.ty)
end

lang RecordTypeUnify = UnifyRows + RecordTypeAst
  sem unifyBase u env =
  | (TyRecord t1, TyRecord t2) ->
    unifyRowsStrict u env t1.fields t2.fields
end

lang TyWildUnify = Unify + TyWildAst
  sem unifyBase u env =
  | (TyWild _, TyWild _) -> u.empty
end

lang ReprTypeUnify = ReprTypeAst + Unify
  sem unifyBase u env =
  | (TyRepr a, TyRepr b) ->
    u.combine
      (u.unifyRepr env a.repr b.repr)
      (unifyTypes u env (a.arg, b.arg))
end

-- A map representing the partitioning induced by a series of
-- unifications of variables. Variables have a concept of levels, such
-- that the representative element of each partition will have the
-- lowest level included in the partition. Each partition may also
-- have an `out` (e.g., a `Type` when working with type unification
-- variables) and multiple `extra`s (constraints that are suspended
-- until the partition gets an `out`).
type PUFContent k extra out
con PUFLink : all k. all extra. all out. k -> PUFContent k extra out
con PUFOut : all k. all extra. all out. out -> PUFContent k extra out
con PUFExtra : all k. all extra. all out. [extra] -> PUFContent k extra out
type PureUnionFind k extra out =
  Map k {level : Int, content : PUFContent k extra out}

let pufToDebug
  : all k. all extra. all out. all env.
  String
  -> (env -> k -> (env, String))
  -> (env -> extra -> (env, String))
  -> (env -> out -> (env, String))
  -> env
  -> PureUnionFind k extra out
  -> (env, String)
  = lam indent. lam pk. lam pextra. lam pout. lam env. lam puf.
    let f = lam acc. lam k. lam record.
      match acc with (env, str) in
      match pk env k with (env, k) in
      match switch record.content
        case PUFLink k then pk env k
        case PUFOut out then
          match pout env out with (env, out) in
          (env, concat "(out) " out)
        case PUFExtra extras then
          match mapAccumL pextra env extras with (env, extras) in
          (env, concat "(extras) " (strJoin ", " extras))
        end
      with (env, content) in
      (env, join [str, indent, k, "@", int2string record.level, " -> ", content, "\n"])
    in
    mapFoldWithKey f (env, "") puf

-- All operations that "modify" a PUF return this type, which
-- summarizes obligations to the user of the interface. The two extra
-- values represent unifications between `out`s of two partitions that
-- were merged by the operation, and `extra`s that now have an
-- assigned `out`, respectively.
type PUFResult k extra out =
  { newOutUnification : Option (out, out)
  , newExtraResolutions : Option (out, [extra])
  , puf : PureUnionFind k extra out
  }

type PUFResults k extra out =
  { newOutUnifications : [(out, out)]
  , newExtraResolutions : [(out, [extra])]
  , puf : PureUnionFind k extra out
  }

let pufEmptyResults = lam puf.
  { newOutUnifications = []
  , newExtraResolutions = []
  , puf = puf
  }

let pufBind : all k. all extra. all out
  . PUFResults k extra out
  -> (PureUnionFind k extra out -> PUFResult k extra out)
  -> PUFResults k extra out
  = lam res. lam f.
    let new = f res.puf in
    { newOutUnifications = optionMapOr res.newOutUnifications (snoc res.newOutUnifications) new.newOutUnification
    , newExtraResolutions = optionMapOr res.newExtraResolutions (snoc res.newExtraResolutions) new.newExtraResolutions
    , puf = new.puf
    }

let pufEmpty = mapEmpty

let _pufUnwrap : all k. all extra. all out.
  (k, Int)
  -> PureUnionFind k extra out
  -> {k : k, level : Int, content : Either out [extra]}
  = lam k. lam puf.
    recursive let work = lam k.
      switch mapLookup k.0 puf
      case Some {content = PUFLink n} then work (n, negi 0)
      case Some (a & {content = PUFOut out}) then {k = k.0, level = a.level, content = Left out}
      case Some (a & {content = PUFExtra extra}) then {k = k.0, level = a.level, content = Right extra}
      case None _ then {k = k.0, level = k.1, content = Right []}
      end
    in work k

let _pufWrap : all k. all extra. all out.
  {k : k, level : Int, content : Either out [extra]}
  -> {level : Int, content : PUFContent k extra out}
  = lam x. switch x.content
    case Left out then {level = x.level, content = PUFOut out}
    case Right extra then {level = x.level, content = PUFExtra extra}
    end

let pufUnwrapN : all k. all out. all extra. PureUnionFind k extra out -> (k, Int) -> (k, Int)
  = lam puf. lam k.
    let x = _pufUnwrap k puf in
    (x.k, x.level)

let pufUnwrap : all k. all out. all extra. PureUnionFind k extra out -> (k, Int) -> Either out (k, Int)
  = lam puf. lam k.
    switch _pufUnwrap k puf
    case {content = Left out} then Left out
    case x then Right (x.k, x.level)
    end

let pufAddExtra
  : all k. all out. all extra. all x. (k, Int) -> [extra] -> PureUnionFind k extra out -> PUFResult k extra out
  = lam k. lam extra. lam puf.
    switch _pufUnwrap k puf
    case {content = Left out} then
      { newOutUnification = None ()
      , newExtraResolutions = Some (out, extra)
      , puf = puf}
    case x & {content = Right prev} then
      let x = {x with content = Right (concat prev extra)} in
      { newOutUnification = None ()
      , newExtraResolutions = None ()
      , puf = mapInsert x.k (_pufWrap x) puf
      }
    end

let pufUnify
  : all k. all out. all extra. (k, Int) -> (k, Int) -> PureUnionFind k extra out -> PUFResult k extra out
  = lam l. lam r. lam puf.
    match (_pufUnwrap l puf, _pufUnwrap r puf) with (l, r) in
    if eqi 0 (mapGetCmpFun puf l.k r.k) then { newOutUnification = None (), newExtraResolutions = None (), puf = puf} else
    let cmpRes =
      let res = subi l.level r.level in
      if neqi res 0 then res else
      mapGetCmpFun puf l.k r.k in
    match if lti cmpRes 0 then (r, l) else (l, r) with (from, to) in
    match
      switch (from.content, to.content)
      case (Left out, Right extra) | (Right extra, Left out) then
        (Left out, None (), if null extra then None () else Some (out, extra))
      case (Left a, Left b) then
        (Left b, Some (a, b), None ())
      case (Right a, Right b) then
        (Right (concat a b), None (), None ())
      end
    with (content, newPair, newExtra) in
    { newOutUnification = newPair
    , newExtraResolutions = newExtra
    , puf = mapInsert from.k {level = from.level, content = PUFLink to.k}
      (mapInsert to.k (_pufWrap {to with content = content}) puf)
    }

let pufSetOut
  : all k. all out. all extra. (k, Int) -> out -> PureUnionFind k extra out -> PUFResult k extra out
  = lam k. lam out. lam puf.
    switch _pufUnwrap k puf
    case {content = Left prev} then
      { newOutUnification = Some (prev, out)
      , newExtraResolutions = None ()
      , puf = puf
      }
    case x & {content = Right extra} then
      { newOutUnification = None ()
      , newExtraResolutions = if null extra then None () else Some (out, extra)
      , puf = mapInsert x.k (_pufWrap {x with content = Left out}) puf
      }
    end

let pufFold
  : all k. all out. all extra. all acc
  .  (acc -> (k, Int) -> (k, Int) -> acc)
  -> (acc -> (k, Int) -> out -> acc)
  -> (acc -> (k, Int) -> [extra] -> acc)
  -> acc
  -> PureUnionFind k extra out
  -> acc
  = lam feq. lam fout. lam fextra. lam acc. lam puf.
    mapFoldWithKey
      (lam acc. lam k. lam kX.
        let k = (k, kX.level) in
        let x = _pufUnwrap k puf in
        switch (x.content, mapGetCmpFun puf k.0 x.k)
        case (Left out, _) then
          fout acc k out
        case (_, !0) then
          feq acc k (x.k, x.level)
        case (Right [], 0) then
          acc
        case (Right extra, 0) then
          fextra acc k extra
        end)
      acc
      puf

let pufMapK
  : all k1. all out1. all extra1. all k2. all out2. all extra2
  . (k2 -> k2 -> Int)
  -> ((k1, Int) -> (k2, Int))
  -> (out1 -> out2)
  -> (extra1 -> extra2)
  -> PureUnionFind k1 extra1 out1
  -> PUFResults k2 extra2 out2
  = lam cmp. lam fk. lam fout. lam fextra. lam puf.
    pufFold
      (lam acc. lam l. lam r. pufBind acc (pufUnify (fk l) (fk r)))
      (lam acc. lam l. lam out. pufBind acc (pufSetOut (fk l) (fout out)))
      (lam acc. lam l. lam extras. pufBind acc (pufAddExtra (fk l) (map fextra extras)))
      (pufEmptyResults (mapEmpty cmp))
      puf

let pufFilter
  : all k. all out. all extra
  . Int
  -> Set k
  -> PureUnionFind k extra out
  -> PureUnionFind k extra out
  = lam level. lam ks. lam puf.
    let shouldKeep = lam pair. lam ks.
      if lti pair.1 level then true
      else setMem pair.0 ks in
    let ks = pufFold
      (lam acc. lam from. lam to. if shouldKeep from ks
       then setInsert to.0 acc
       else acc)
      (lam acc. lam. lam. acc)
      (lam acc. lam. lam. acc)
      ks
      puf in
    -- NOTE(vipa, 2023-10-14): Here we know, by construction, that the
    -- extra outputs in PUFResult are empty.
    pufFold
      (lam acc. lam from. lam to. if shouldKeep from ks
       then (pufUnify from to acc).puf
       else acc)
      (lam acc. lam from. lam out. if shouldKeep from ks
       then (pufSetOut from out acc).puf
       else acc)
      (lam acc. lam from. lam extra. if shouldKeep from ks
       then (pufAddExtra from extra acc).puf
       else acc)
      (pufEmpty (mapGetCmpFun puf))
      puf

type Unification = use Ast in
  { reprs : PureUnionFind Symbol () Name
  , types : PureUnionFind Name () Type
  }

lang UnifyPure = Unify + MetaVarTypeAst + VarTypeSubstitute + ReprTypeAst + Cmp + PrettyPrint

  sem emptyUnification : () -> Unification
  sem emptyUnification = | _ ->
    { reprs = pufEmpty (lam a. lam b. subi (sym2hash a) (sym2hash b))
    , types = pufEmpty nameCmp
    }

  -- A partial order over unification environments. True if all
  -- assertions present in the second argument are true in the first.
  sem uniImplies : Unification -> Unification -> Bool
  sem uniImplies a = | b ->
    let rEq = eitherEq nameEq (lam l. lam r. and (eqsym l.0 r.0) (eqi l.1 r.1)) in
    let tyEq = eitherEq
      (lam l. lam r. eqi 0 (cmpType (pureApplyUniToType a l) (pureApplyUniToType a r)))
      (lam l. lam r. and (nameEq l.0 r.0) (eqi l.1 r.1)) in
    let reprImplied = pufFold
      (lam acc. lam r1. lam r2. if acc
       then rEq (pufUnwrap a.reprs r1) (pufUnwrap a.reprs r2)
       else false)
      (lam acc. lam r. lam out. if acc
       then rEq (pufUnwrap a.reprs r) (Left out)
       else false)
      (lam acc. lam. lam. acc)
      true
      b.reprs in
    if reprImplied then
      let typeImplied = pufFold
        (lam acc. lam ty1. lam ty2. if acc
         then tyEq (pufUnwrap a.types ty1) (pufUnwrap a.types ty2)
         else false)
        (lam acc. lam ty. lam out. if acc
         then tyEq (pufUnwrap a.types ty) (Left out)
         else false)
        (lam acc. lam. lam. acc)
        true
        b.types in
      typeImplied
    else false

  -- Apply the rewrites present in the `Unification` in the given type
  -- everywhere. The returned type will be "disconnected" from all
  -- other types, in the sense that none of its `TyMetaVar` or
  -- `ReprVar`s are shared, i.e., a side-effecting unification
  -- afterwards won't do the right thing.
  sem pureApplyUniToType : Unification -> Type -> Type
  sem pureApplyUniToType uni =
  | ty -> smap_Type_Type (pureApplyUniToType uni) ty
  | TyMetaVar x -> switch deref x.contents
    case Link ty then pureApplyUniToType uni ty
    case Unbound u then
      switch pufUnwrap uni.types (u.ident, u.level)
      case Left ty then pureApplyUniToType uni ty
      case Right (ident, level) then
        TyMetaVar {x with contents = ref (Unbound {u with ident = ident, level = level})}
      end
    end
  | TyRepr x ->
    let arg = pureApplyUniToType uni x.arg in
    switch deref (botRepr x.repr)
    case BotRepr {sym = sym, scope = scope} then
      match pufUnwrapN uni.reprs (sym, scope) with (sym, scope) in
      TyRepr {x with arg = arg, repr = ref (BotRepr {sym = sym, scope = scope})}
    case UninitRepr _ then
      TyRepr {x with arg = arg, repr = ref (UninitRepr ())}
    end

  sem _handlePufReprs : Unification -> PUFResults Symbol () Name -> Option Unification
  sem _handlePufReprs uni = | res ->
    if any (lam eq. not (nameEq eq.0 eq.1)) res.newOutUnifications then None () else
    Some {uni with reprs = res.puf}

  sem _handlePufTypes : Unification -> PUFResults Name () Type -> Option Unification
  sem _handlePufTypes uni = | res ->
    let uni = {uni with types = res.puf} in
    optionFoldlM (lam uni. lam eq. unifyPure uni eq.0 eq.1) uni res.newOutUnifications

  sem mergeUnifications : Unification -> Unification -> Option Unification
  sem mergeUnifications l = | r ->
    let juggle = lam f. lam acc. lam a. lam b. pufBind acc (f a b) in

    let reprRes = pufFold (juggle pufUnify) (juggle pufSetOut) (juggle pufAddExtra)
      (pufEmptyResults l.reprs)
      r.reprs in
    if any (lam eq. not (nameEq eq.0 eq.1)) reprRes.newOutUnifications then None () else

    let typeRes = pufFold (juggle pufUnify) (juggle pufSetOut) (juggle pufAddExtra)
      (pufEmptyResults l.types)
      r.types in
    let uni = {reprs = reprRes.puf, types = typeRes.puf} in
    optionFoldlM (lam uni. lam eq. unifyPure uni eq.0 eq.1) uni typeRes.newOutUnifications

  sem _handlePufRepr : Unification -> PUFResult Symbol () Name -> Option Unification
  sem _handlePufRepr uni = | x ->
    let pairOk = match x.newOutUnification with Some (a, b)
      then nameEq a b
      else true in
    -- NOTE(vipa, 2023-10-05): We would check if reprs can be applied
    -- to each of the `Repr` arguments they've been used with here, if
    -- we did it (they would be in x.newExtraResolutions)
    if pairOk then
      Some {uni with reprs = x.puf}
    else None ()

  sem _handlePufType : UnifyEnv -> Unification -> PUFResult Name () Type -> Option Unification
  sem _handlePufType env uni = | x ->
    let uni = {uni with types = x.puf} in
    match x.newOutUnification with Some (a, b) then unifyPureWithEnv env uni a b else Some uni

  sem unifyReprPure : Unification -> ReprVar -> ReprVar -> Option Unification
  sem unifyReprPure uni lr = | rr ->
    match (deref (botRepr lr), deref (botRepr rr)) with (BotRepr lr, BotRepr rr) in
    _handlePufRepr uni (pufUnify (lr.sym, lr.scope) (rr.sym, rr.scope) uni.reprs)

  sem unifySetReprPure : Unification -> ReprVar -> Name -> Option Unification
  sem unifySetReprPure uni r = | subst ->
    match deref (botRepr r) with BotRepr r in
    _handlePufRepr uni (pufSetOut (r.sym, r.scope) subst uni.reprs)

  sem unifyPureWithEnv : UnifyEnv -> Unification -> Type -> Type -> Option Unification
  sem unifyPureWithEnv env uni lty = | rty ->
    let uniRef = ref (Some uni) in
    let tyAsMeta = lam ty.
      match ty with TyMetaVar x then
        match deref x.contents with Unbound x in
        Right (x.ident, x.level)
      else Left ty in
    recursive
      let unifier = lam.
        { empty = ()
        , combine = lam. lam. ()
        , unify = lam env. lam lty. lam rty.
          match deref uniRef with Some uni then
            switch
              ( eitherBindRight (tyAsMeta lty) (pufUnwrap uni.types)
              , eitherBindRight (tyAsMeta rty) (pufUnwrap uni.types)
              )
            case (Left lty, Left rty) then
              modref uniRef (unifyPureWithEnv env uni lty rty)
            case (Left ty, Right n) | (Right n, Left ty) then
              modref uniRef (_handlePufType env uni (pufSetOut n ty uni.types))
            case (Right l, Right r) then
              modref uniRef (_handlePufType env uni (pufUnify l r uni.types))
            end
          else ()
        , unifyRepr = lam env. lam lvar. lam rvar.
          match deref uniRef with Some uni then
            modref uniRef (unifyReprPure uni lvar rvar)
          else ()
        , err = lam err. modref uniRef (None ())
        }
    in
    unifyTypes (unifier ()) env (lty, rty);
    deref uniRef

  sem unifyPure : Unification -> Type -> Type -> Option Unification
  sem unifyPure uni lty = | rty ->
    let env : UnifyEnv =
      { boundNames = biEmpty
      , wrappedLhs = lty
      , wrappedRhs = rty
      } in
    unifyPureWithEnv env uni lty rty

  sem substituteInUnification : ((Name, Int) -> (Name, Int)) -> ((Symbol, Int) -> (Symbol, Int)) -> (Type -> Type) -> Unification -> Option Unification
  sem substituteInUnification fn fs fty = | uni ->
    let reprRes = pufMapK (lam a. lam b. subi (sym2hash a) (sym2hash b)) fs (lam x. x) (lam x. x) uni.reprs in
    match _handlePufReprs uni reprRes with Some uni then
      let typeRes = pufMapK nameCmp fn fty (lam x. x) uni.types in
      _handlePufTypes uni typeRes
    else None ()

  sem filterUnification
    : {reprs : {scope : Int, syms : Set Symbol}, types : {level : Int, names : Set Name}}
    -> Unification
    -> Unification
  sem filterUnification filters = | uni ->
    { reprs = pufFilter filters.reprs.scope filters.reprs.syms uni.reprs
    , types = pufFilter filters.types.level filters.types.names uni.types
    }

  sem unificationToDebug : String -> PprintEnv -> Unification -> (PprintEnv, String)
  sem unificationToDebug indent env = | uni ->
    match pufToDebug (cons ' ' indent) (lam env. lam sym. (env, int2string (sym2hash sym))) (lam env. lam. (env, "")) pprintVarName env uni.reprs with (env, reprs) in
    match pufToDebug (cons ' ' indent) pprintVarName (lam env. lam. (env, "")) (getTypeStringCode 2) env uni.types with (env, types) in
    (env, join [indent, "reprs:\n", reprs, indent, "types:\n", types])
end

lang MExprUnify =
  VarTypeUnify + MetaVarTypeUnify + FunTypeUnify + AppTypeUnify + AllTypeUnify +
  ConTypeUnify + BoolTypeUnify + IntTypeUnify + FloatTypeUnify + CharTypeUnify +
  SeqTypeUnify + TensorTypeUnify + RecordTypeUnify
end

lang RepTypesUnify = TyWildUnify + ReprTypeUnify
end

lang TestLang = UnifyPure + MExprUnify + MExprCmp + MetaVarTypeCmp + MExprPrettyPrint + MetaVarTypePrettyPrint end

mexpr

use TestLang in

let a = nameSym "a" in
let b = nameSym "b" in

let wa =
  TyMetaVar {info = NoInfo (),
             contents = ref (Unbound {ident = a,
                                      level = 0,
                                      kind  = Mono ()})} in
let wb =
  TyMetaVar {info = NoInfo (),
             contents = ref (Unbound {ident = b,
                                      level = 0,
                                      kind  = Mono ()})} in
let testUnify = unifyPure (emptyUnification ()) in
let mkUni = lam eqs. optionFoldlM (lam uni. lam pair. unifyPure uni pair.0 pair.1) (emptyUnification ()) eqs in
let uniEq = lam a. lam b. if uniImplies a b then uniImplies b a else false in
let unifyEq = optionEq uniEq in

utest testUnify tyint_ tyint_ with mkUni [] using unifyEq in

utest testUnify tybool_ tyint_ with None () using unifyEq in

utest testUnify wa tyint_ with testUnify tyint_ wa using unifyEq in

utest testUnify (tyarrow_ wa wb) (tyarrow_ tyint_ tybool_)
  with mkUni [(wa, tyint_), (wb, tybool_)]
  using unifyEq
in

utest testUnify (tyarrow_ wa wa) (tyarrow_ tyint_ tybool_)
  with None ()
  using unifyEq
in

utest testUnify (tyarrow_ wa tybool_) (tyarrow_ wb wb)
  with mkUni [(wa, tybool_), (wb, tybool_)]
  using unifyEq
in

utest testUnify (tytuple_ [wa, wb]) (tytuple_ [wa, wa])
  with mkUni [(wb, wa)]
  using unifyEq
in

-- TODO(vipa, 2023-12-06): Regression that's a bit more annoying to
-- deal with in the current system: we loop forever on cyclic types

-- utest testUnify (tytuple_ [wa, wa]) (tytuple_ [tyseq_ wa, tyseq_ (tyseq_ wa)])
--   with mkUni [(wa, tyseq_ wa)]
--   using unifyEq
-- in

()
