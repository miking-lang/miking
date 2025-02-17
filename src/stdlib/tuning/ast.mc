include "mexpr/ast.mc"
include "mexpr/anf.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/boot-parser.mc"
include "mexpr/type-check.mc"

-- Defines AST nodes for holes.

let _lookupExit : all a. Info -> String -> Map String a -> a =
  lam info : Info. lam s : String. lam m : Map String a.
    mapLookupOrElse (lam. errorSingle [info] (concat s " not found")) s m

let _expectConstInt : use Ast in Info -> String -> Expr -> Int =
  lam info : Info. lam s. lam i.
    use IntAst in
    match i with TmConst {val = CInt {val = i}} then i
    else errorSingle [info] (concat "Expected a constant integer: " s)

lang HoleAstBase = IntAst + ANF + KeywordMaker + TypeCheck + Sym
  syn Hole =

  syn Expr =
  | TmHole {default : Expr,
            depth : Int,
            ty : Type,
            info : Info,
            inner : Hole}

  sem infoTm =
  | TmHole h -> h.info

  sem tyTm =
  | TmHole {ty = ty} -> ty

  sem withType (ty : Type) =
  | TmHole t -> TmHole {t with ty = ty}

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem default =
  | TmHole {default = default} -> default
  | t -> smap_Expr_Expr default t

  sem isAtomic =
  | TmHole _ -> false

  sem pprintHole =

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmHole t ->
    match pprintCode indent env t.default with (env, default) then
      match pprintHole t.inner with (keyword, bindings) then
        (env, join
          [ "hole ("
          , keyword
          , " {"
          , "depth = ", int2string t.depth, ", "
          , "default = ", default, ", "
          , strJoin ", "
            (map (lam b : (String, String). join [b.0, " = ", b.1])
               bindings)
          ,  "}"
          , ")"
          ])
      else never
    else never

  sem next (last : Option Expr) (stepSize : Int) =
  | TmHole {inner = inner} ->
    hnext last stepSize inner

  sem hnext (last : Option Expr) (stepSize : Int) =

  sem domainSize (stepSize : Int) =
  | TmHole {inner = inner} ->
    hdomainSize stepSize inner

  sem hdomainSize (stepSize : Int) =

  sem domain (stepSize : Int) =
  | TmHole {inner = inner} ->
    hdomain stepSize inner

  sem hdomain (stepSize : Int) =

  sem sample (stepSize : Int) =
  | TmHole {inner = inner} ->
    hsample stepSize inner

  sem hsample (stepSize : Int) =

  sem normalize (k : Expr -> Expr) =
  | TmHole ({default = default} & t) ->
    k (TmHole {t with default = normalizeTerm t.default})

  sem isKeyword =
  | TmHole _ -> true

  sem matchKeywordString (info : Info) =
  | "hole" -> Some (1, lam lst. head lst)

  sem _mkHole (info : Info) (hty : Type) (holeMap : Map String Expr -> Hole)
              (validate : Expr -> Expr) =
  | arg ->
    use RecordAst in
    match arg with TmRecord {bindings = bindings} then
      let bindings: Map String Expr = mapFromSeq cmpString
        (map (lam t : (SID, Expr). (sidToString t.0, t.1))
           (mapBindings bindings)) in
      let default = _lookupExit info "default" bindings in
      let depth = mapLookupOrElse (lam. int_ 0) "depth" bindings in
      validate
        (TmHole { default = default
                , depth = _expectConstInt info "depth" depth
                , info = info
                , ty = hty
                , inner = holeMap bindings})
    else error "impossible"

  sem hty : Info -> Hole -> Type

  sem typeCheckExpr (env: TCEnv) =
  | TmHole t ->
    let default = typeCheckExpr env t.default in
    let ty = hty t.info t.inner in
    unify env [t.info] ty (tyTm default);
    TmHole {{t with default = default}
               with ty = ty}

  sem fromInt =
  | TmHole t -> hfromInt t.inner

  sem toInt (e: Expr) =
  | TmHole t -> htoInt t.info e t.inner

  sem hfromInt : Hole -> (Expr -> Expr)

  sem htoInt : Info -> Expr -> Hole -> Int

end

-- A Boolean hole.
lang HoleBoolAst = BoolAst + HoleAstBase + BoolTypeAst
  syn Hole =
  | BoolHole {}

  sem hsample (stepSize : Int) =
  | BoolHole {} ->
    get [true_, false_] (randIntU 0 2)

  sem hnext (last : Option Expr) (stepSize : Int) =
  | BoolHole {} ->
    match last with None () then Some false_
    else match last with Some (TmConst {val = CBool {val = false}}) then
      Some true_
    else match last with Some (TmConst {val = CBool {val = true}}) then
      None ()
    else never

  sem hdomainSize (stepSize : Int) =
  | BoolHole {} -> 2

  sem hdomain (stepSize : Int) =
  | BoolHole {} -> [true_, false_]

  sem fromString =
  | "true" -> true
  | "false" -> false

  sem matchKeywordString (info : Info) =
  | "Boolean" ->
    Some (1,
      let validate = lam expr.
        match expr with TmHole {default = default} then
          match default with TmConst {val = CBool _} then expr
          else errorSingle [info] "Default value not a constant Boolean"
        else errorSingle [info] "Not a hole" in

      lam lst. _mkHole info tybool_ (lam. BoolHole {}) validate (get lst 0))

  sem pprintHole =
  | BoolHole {} ->
    ("Boolean", [])

  sem hty info =
  | BoolHole {} -> TyBool {info = info}

  sem hfromInt =
  | BoolHole {} ->
    lam e. neqi_ (int_ 0) e

  sem htoInt info v =
  | BoolHole {} ->
    match v with TmConst {val = CBool {val = b}} then
      if b then 1 else 0
    else errorSingle [info] "Expected a Boolean expression"

end

-- An integer hole (range of integers).
lang HoleIntRangeAst = IntAst + HoleAstBase + IntTypeAst
  syn Hole =
  | HIntRange {min : Int,
               max : Int}

  sem hsample (stepSize : Int) =
  | HIntRange h ->
    let size = hdomainSize stepSize (HIntRange h) in
    let i = randIntU 0 size in
    int_ (addi h.min (muli i stepSize))

  sem hnext (last : Option Expr) (stepSize : Int) =
  | HIntRange {min = min, max = max} ->
    match last with None () then Some (int_ min)
    else match last with Some (TmConst {val = CInt {val = i}}) then
      if eqi i max then
        None ()
      else
        let next = addi i stepSize in
        utest geqi next min with true in
        if leqi next max then Some (int_ next)
        else None ()
    else never

  sem hdomainSize (stepSize : Int) =
  | HIntRange {min = min, max = max} ->
    let len = addi (subi max min) 1 in
    let r = divi len stepSize in
    let m = if eqi 0 (modi len stepSize) then 0 else 1 in
    addi r m

  sem hdomain (stepSize : Int) =
  | HIntRange ({min = min} & h) ->
    map (lam i. int_ (addi min (muli i stepSize)))
      (create (hdomainSize stepSize (HIntRange h)) (lam i. i))

  sem matchKeywordString (info : Info) =
  | "IntRange" ->
    Some (1,
      let validate = lam expr.
        match expr
        with TmHole {default = TmConst {val = CInt {val = i}},
                     inner = HIntRange {min = min, max = max}}
        then
          if and (leqi min i) (geqi max i) then expr
          else errorSingle [info] "Default value is not within range"
        else errorSingle [info] "Not a hole" in

      lam lst. _mkHole info tyint_
        (lam m: Map String Expr.
           let min = _expectConstInt info "min" (_lookupExit info "min" m) in
           let max = _expectConstInt info "max" (_lookupExit info "max" m) in
           if leqi min max then
             HIntRange {min = min, max = max}
           else errorSingle [info] (join ["Empty domain: ", int2string min, "..", int2string max]))
        validate (get lst 0))

  sem pprintHole =
  | HIntRange {min = min, max = max} ->
    ("IntRange", [("min", int2string min), ("max", int2string max)])

  sem hty info =
  | HIntRange {} -> TyInt {info = info}

  sem hfromInt =
  | HIntRange {} ->
    lam e. e

  sem htoInt info v =
  | HIntRange {} ->
    match v with TmConst {val = CInt {val = i}} then i
    else errorSingle [info] "Expected an Int expression"


end

lang HoleAnnotation = Ast
  sem stripTuneAnnotations =
  | t -> smap_Expr_Expr stripTuneAnnotations t
end

-- Independency annotation
lang IndependentAst = HoleAnnotation + KeywordMaker + ANF + PrettyPrint
                    + TypeCheck
  syn Expr =
  | TmIndependent {lhs : Expr,
                   rhs : Expr,
                   info: Info,
                   ty : Type}

  sem stripTuneAnnotations =
  | TmIndependent t -> t.lhs

  sem isKeyword =
  | TmIndependent _ -> true

  sem matchKeywordString (info : Info) =
  | "independent" -> Some (2, lam lst.
    let e1 = get lst 0 in
    let e2 = get lst 1 in
    TmIndependent {lhs = e1, rhs = e2, info = info, ty = tyTm e1})

  sem normalize (k : Expr -> Expr) =
  | TmIndependent t ->
    normalizeName (lam l.
      normalizeName (lam r.
        k (TmIndependent {{t with lhs = l}
                             with rhs = r})
        )
      t.rhs)
    t.lhs

  sem infoTm =
  | TmIndependent {info = info} -> info

  sem tyTm =
  | TmIndependent {ty = ty} -> ty

  sem withType (ty : Type) =
  | TmIndependent t -> TmIndependent {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmIndependent t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, TmIndependent {{t with lhs = lhs} with rhs = rhs})
      else never
    else never

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmIndependent t ->
    match printParen indent env t.lhs with (env, lhs) in
    let aindent = pprintIncr indent in
    match printParen aindent env t.rhs with (env, rhs) in
    (env, join ["independent ", lhs, pprintNewline aindent, rhs])

  sem typeCheckExpr (env: TCEnv) =
  | TmIndependent t ->
    let lhs = typeCheckExpr env t.lhs in
    let rhs = typeCheckExpr env t.rhs in
    TmIndependent {{{t with lhs = lhs}
                       with rhs = rhs}
                       with ty = tyTm lhs}

end

let holeBool_ : use Ast in Bool -> Int -> Expr =
  use HoleBoolAst in
  lam default. lam depth.
  TmHole { default = bool_ default
         , depth = depth
         , ty = tybool_
         , info = NoInfo ()
         , inner = BoolHole {}}

let holeIntRange_ : use Ast in Int -> Int -> Int -> Int -> Expr =
  use HoleIntRangeAst in
  lam default. lam depth. lam min. lam max.
  TmHole { default = int_ default
         , depth = depth
         , ty = tyint_
         , info = NoInfo ()
         , inner = HIntRange {min = min, max = max}
         }

lang HoleAst = HoleAstBase + HoleBoolAst + HoleIntRangeAst + IndependentAst end

lang HoleANF = HoleAst + MExprANF end

lang HoleANFAll = HoleAst + MExprANFAll end

lang Test = HoleAst + MExprEq end

mexpr

use Test in

let h = holeBool_ true 0 in
utest domainSize 100 h with 2 in

let h = holeIntRange_ 5 0 1 10 in
utest domainSize 2 h with 5 in
utest domain 2 h with [int_ 1, int_ 3, int_ 5, int_ 7, int_ 9] using eqSeq eqExpr in

let h = holeIntRange_ 5 0 2 10 in
utest domainSize 2 h with 5 in
utest domain 2 h with [int_ 2, int_ 4, int_ 6, int_ 8, int_ 10] using eqSeq eqExpr in

let h = holeIntRange_ 5 0 2 9 in
utest domainSize 2 h with 4 in
utest domain 2 h with [int_ 2, int_ 4, int_ 6, int_ 8] using eqSeq eqExpr in

let h = holeIntRange_ 5 0 5 5 in
utest domainSize 100 h with 1 in
utest domain 100 h with [int_ 5] using eqSeq eqExpr in

let h = holeIntRange_ 2 0 1 3 in
utest
  let s = create 1000 (lam. sample 1 h) in
  [ optionIsSome (find (eqExpr (int_ 1)) s)
  , optionIsSome (find (eqExpr (int_ 2)) s)
  , optionIsSome (find (eqExpr (int_ 3)) s)
  ]
with [true, true, true] in

let h = holeIntRange_ 2 0 1 3 in
utest
  let s = create 1000 (lam. sample 2 h) in
  [ optionIsSome (find (eqExpr (int_ 1)) s)
  , optionIsSome (find (eqExpr (int_ 2)) s)
  , optionIsSome (find (eqExpr (int_ 3)) s)
  ]
with [true, false, true] in

()
