include "mexpr/ast.mc"
include "mexpr/anf.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/boot-parser.mc"

-- Defines AST nodes for holes.

let holeKeywords = ["hole", "Boolean", "IntRange"]

let _lookupExit = lam info : Info. lam s : String. lam m : Map String a.
  mapLookupOrElse (lam. infoErrorExit info (concat s " not found")) s m

let _expectConstInt = lam info : Info. lam s. lam i.
  use IntAst in
  match i with TmConst {val = CInt {val = i}} then i
  else infoErrorExit info (concat "Expected a constant integer: " s)

lang HoleAstBase = IntAst + ANF + KeywordMaker
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

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem default =
  | TmHole {default = default} -> default
  | t -> smap_Expr_Expr default t

  sem isAtomic =
  | TmHole _ -> false

  sem pprintHole =

  sem pprintCode (indent : Int) (env : SymEnv) =
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

  sem sample =
  | TmHole {inner = inner} ->
    hsample inner

  sem hsample =

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
      let bindings = mapFromSeq cmpString
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
end

-- A Boolean hole.
lang HoleBoolAst = BoolAst + HoleAstBase
  syn Hole =
  | BoolHole {}

  sem hsample =
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

  sem fromString =
  | "true" -> true
  | "false" -> false

  sem matchKeywordString (info : Info) =
  | "Boolean" ->
    Some (1,
      let validate = lam expr.
        match expr with TmHole {default = default} then
          match default with TmConst {val = CBool _} then expr
          else infoErrorExit info "Default value not a constant Boolean"
        else infoErrorExit info "Not a hole" in

      lam lst. _mkHole info tybool_ (lam. BoolHole {}) validate (get lst 0))

  sem pprintHole =
  | BoolHole {} ->
    ("Boolean", [])
end

-- An integer hole (range of integers).
lang HoleIntRangeAst = IntAst + HoleAstBase
  syn Hole =
  | HIntRange {min : Int,
              max : Int}

  sem hsample =
  | HIntRange {min = min, max = max} ->
    int_ (randIntU min (addi max 1))

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

  sem matchKeywordString (info : Info) =
  | "IntRange" ->
    Some (1,
      let validate = lam expr.
        match expr
        with TmHole {default = TmConst {val = CInt {val = i}},
                     inner = HIntRange {min = min, max = max}}
        then
          if and (leqi min i) (geqi max i) then expr
          else infoErrorExit info "Default value is not within range"
        else infoErrorExit info "Not a hole" in

      lam lst. _mkHole info tyint_
        (lam m.
           let min = _expectConstInt info "min" (_lookupExit info "min" m) in
           let max = _expectConstInt info "max" (_lookupExit info "max" m) in
           if leqi min max then
             HIntRange {min = min, max = max}
           else infoErrorExit info
             (join ["Empty domain: ", int2string min, "..", int2string max]))
        validate (get lst 0))

  sem pprintHole =
  | HIntRange {min = min, max = max} ->
    ("IntRange", [("min", int2string min), ("max", int2string max)])
end

let holeBool_ = use HoleBoolAst in
  lam default. lam depth.
  TmHole { default = default
         , depth = depth
         , ty = tybool_
         , info = NoInfo ()
         , inner = BoolHole {}}

let holeIntRange_ = use HoleIntRangeAst in
  lam default. lam depth. lam min. lam max.
  TmHole { default = default
         , depth = depth
         , ty = tyint_
         , info = NoInfo ()
         , inner = HIntRange {min = min, max = max}}

lang HoleAst = HoleAstBase + HoleBoolAst + HoleIntRangeAst end

lang HoleANF = HoleAst + MExprANF end

lang HoleANFAll = HoleAst + MExprANFAll end
