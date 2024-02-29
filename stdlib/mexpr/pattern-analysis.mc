include "math.mc"
include "seq.mc"
include "map.mc"
include "set.mc"
include "stringid.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

lang NormPat = Ast
  syn SimpleCon =
  syn SNPat =
  syn NPat =

  type NormPat = [NPat]

  sem simpleConCmp : SimpleCon -> SimpleCon -> Int
  sem simpleConCmp sc1 = | sc2 -> simpleConCmpH (sc1, sc2)

  sem simpleConCmpH : (SimpleCon, SimpleCon) -> Int
  sem simpleConCmpH =
  | (lhs, rhs) ->
    subi (constructorTag lhs) (constructorTag rhs)

  sem simpleConComplement : SimpleCon -> SNPat
  sem simpleConToPat : SimpleCon -> Pat

  sem snpatCmp : (SNPat, SNPat) -> Int
  sem snpatCmp =
  | (lhs, rhs) ->
    subi (constructorTag lhs) (constructorTag rhs)

  sem snpatToSimpleCon : SNPat -> Option SimpleCon
  sem snpatToSimpleCon =
  | _ -> None ()

  sem snpatComplement  : SNPat -> NormPat

  sem snpatIntersect   : (SNPat, SNPat) -> NormPat
  sem snpatIntersect =
  | _ -> []

  sem snpatToPat : SNPat -> Pat

  sem npatCmp  : NPat -> NPat -> Int
  sem npatCmp np1 = | np2 -> npatCmpH (np1, np2)

  sem npatCmpH : (NPat, NPat) -> Int
  sem npatCmpH =
  | (lhs, rhs) ->
    subi (constructorTag lhs) (constructorTag rhs)

  sem npatComplement : NPat -> NormPat
  sem npatIntersect  : (NPat, NPat) -> NormPat
  sem npatToPat : NPat -> Pat

  sem normpatComplement : NormPat -> NormPat
  sem normpatIntersect  : NormPat -> NormPat -> NormPat
  sem patToNormpat : Pat -> NormPat
  sem normpatToPat : NormPat -> Pat
end

lang NPatImpl = NormPat
  syn NPat =
  | SNPat SNPat
  | NPatNot (Set SimpleCon)

  sem npatCmpH =
  | (SNPat a, SNPat b) ->
    snpatCmp (a, b)
  | (NPatNot a, NPatNot b) ->
    setCmp a b

  sem npatComplement =
  | SNPat snp    -> snpatComplement snp
  | NPatNot cons ->
    setFold (lam ks. lam k. snoc ks (SNPat (simpleConComplement k)))
      [] cons

  sem npatIntersect =
  | (SNPat a, SNPat b) ->
    snpatIntersect (a, b)
  | (NPatNot cons, SNPat sp & pat)
  | (SNPat sp & pat, NPatNot cons) ->
    if optionMapOr false (lam x. setMem x cons) (snpatToSimpleCon sp)
    then []
    else [pat]
  | (NPatNot cons1, NPatNot cons2) ->
    [NPatNot (setUnion cons1 cons2)]

  sem npatToPat =
  | SNPat a -> snpatToPat a
  | NPatNot cons ->
    if setIsEmpty cons then
      pvarw_
    else
      pnot_ (foldl1 por_ (map simpleConToPat (setToSeq cons)))

  sem seqComplement : ([NPat] -> NPat) -> [NPat] -> NormPat
  sem seqComplement constr =
  | seq ->
    let nested : [[[NPat]]] =
      create (length seq)
        (lam target.
          mapi (lam i. lam p.
            if lti i target then
              [p]
            else
              if eqi i target then npatComplement p
              else [wildpat ()]) seq)
    in
    let distributed : [[NPat]] =
      joinMap (seqMapM (lam x. x)) nested in
    map constr distributed

  sem wildpat : () -> NPat
  sem wildpat =
  | () -> NPatNot (setEmpty simpleConCmp)

  sem notpatSimple : SimpleCon -> NPat
  sem notpatSimple =
  | c -> NPatNot (setOfSeq simpleConCmp [c])

end


lang NormPatImpl = NPatImpl
  sem normpatComplement =
  | [] -> [wildpat ()]
  | np ->
    foldl1 normpatIntersect (map npatComplement np)

  sem normpatIntersect np1 =
  | np2 ->
    join
      (seqLiftA2 (lam x. lam y. npatIntersect (x, y))
         np1 np2)

  sem normpatToPat =
  | [] -> pnot_ pvarw_
  | np ->
    foldl1 por_ (map npatToPat np)
end

lang IntNormPat = NPatImpl + IntPat
  syn SimpleCon =
  | IntCon Int

  syn SNPat =
  | NPatInt Int

  sem simpleConCmpH =
  | (IntCon a, IntCon b) -> subi a b

  sem simpleConComplement =
  | IntCon a -> NPatInt a

  sem simpleConToPat =
  | IntCon a -> pint_ a

  sem snpatCmp =
  | (NPatInt a, NPatInt b) -> subi a b

  sem snpatToSimpleCon =
  | NPatInt a -> Some (IntCon a)

  sem snpatComplement =
  | NPatInt a ->
    [notpatSimple (IntCon a)]

  sem snpatIntersect =
  | (NPatInt a & p, NPatInt b) ->
    if eqi a b
    then [SNPat p]
    else []

  sem snpatToPat =
  | NPatInt a -> pint_ a

  sem patToNormpat =
  | PatInt a ->
    [SNPat (NPatInt a.val)]
end

lang CharNormPat = NPatImpl + CharPat
  syn SimpleCon =
  | CharCon Char

  syn SNPat =
  | NPatChar Char

  sem simpleConCmpH =
  | (CharCon a, CharCon b) -> subi (char2int a) (char2int b)

  sem simpleConComplement =
  | CharCon a -> NPatChar a

  sem simpleConToPat =
  | CharCon a -> pchar_ a

  sem snpatCmp =
  | (NPatChar a, NPatChar b) -> subi (char2int a) (char2int b)

  sem snpatToSimpleCon =
  | NPatChar a -> Some (CharCon a)

  sem snpatComplement =
  | NPatChar a ->
    [notpatSimple (CharCon a)]

  sem snpatIntersect =
  | (NPatChar a & p, NPatChar b) ->
    if eqc a b
    then [SNPat p]
    else []

  sem snpatToPat =
  | NPatChar a -> pchar_ a

  sem patToNormpat =
  | PatChar a ->
    [SNPat (NPatChar a.val)]
end

lang BoolNormPat = NPatImpl + BoolPat
  syn SimpleCon =
  | BoolCon Bool

  syn SNPat =
  | NPatBool Bool

  sem simpleConCmpH =
  | (BoolCon a, BoolCon b) ->
    subi (if a then 1 else 0) (if b then 1 else 0)

  sem simpleConComplement =
  | BoolCon a -> NPatBool a

  sem simpleConToPat =
  | BoolCon a -> pbool_ a

  sem snpatCmp =
  | (NPatBool a, NPatBool b) ->
    subi (if a then 1 else 0) (if b then 1 else 0)

  sem snpatToSimpleCon =
  | NPatBool a -> Some (BoolCon a)

  sem snpatComplement =
  | NPatBool a ->
    [notpatSimple (BoolCon a)]

  sem snpatIntersect =
  | (NPatBool a & p, NPatBool b) ->
    if eqi (if a then 1 else 0) (if b then 1 else 0)
    then [SNPat p]
    else []

  sem snpatToPat =
  | NPatBool a -> pbool_ a

  sem patToNormpat =
  | PatBool a ->
    [SNPat (NPatBool a.val)]
end

lang ConNormPat = NPatImpl + DataPat
  syn SimpleCon =
  | ConCon Name

  syn SNPat =
  | NPatCon { ident : Name, subpat : NPat }

  sem simpleConCmpH =
  | (ConCon a, ConCon b) -> nameCmp a b

  sem simpleConComplement =
  | ConCon a ->
    NPatCon { ident = a, subpat = wildpat () }

  sem simpleConToPat =
  | ConCon a -> npcon_ a pvarw_

  sem snpatCmp =
  | (NPatCon a, NPatCon b) ->
    let nameRes = nameCmp a.ident b.ident in
    if eqi 0 nameRes then npatCmp a.subpat b.subpat
    else nameRes

  sem snpatToSimpleCon =
  | NPatCon a -> Some (ConCon a.ident)

  sem snpatComplement =
  | NPatCon {ident = c, subpat = p} ->
    cons
      (notpatSimple (ConCon c))
      (map
         (lam p. SNPat (NPatCon {ident = c, subpat = p}))
         (npatComplement p))

  sem snpatIntersect =
  | (NPatCon {ident = c1, subpat = p1},
     NPatCon {ident = c2, subpat = p2}) ->
    if nameEq c1 c2 then
      map
        (lam p. SNPat (NPatCon {ident = c1, subpat = p}))
        (npatIntersect (p1, p2))
    else
      []

  sem snpatToPat =
  | NPatCon {ident = c, subpat = p} ->
    npcon_ c (npatToPat p)

  sem patToNormpat =
  | PatCon {ident = c, subpat = p} ->
    map
      (lam p. SNPat (NPatCon {ident = c, subpat = p}))
      (patToNormpat p)
end

lang RecordNormPat = NPatImpl + RecordPat
  syn SNPat =
  | NPatRecord (Map SID NPat)

  sem snpatCmp =
  | (NPatRecord a, NPatRecord b) ->
    mapCmp npatCmp a b

  sem snpatComplement =
  | NPatRecord pats ->
    match unzip (mapBindings pats) with (labels, pats) in
    seqComplement
      (lam pats.
        SNPat (NPatRecord (mapFromSeq cmpSID (zip labels pats))))
      pats

  sem snpatIntersect =
  | (NPatRecord pats1, NPatRecord pats2) ->
    let merged =
      mapMerge
        (lam p1. lam p2.
          switch (p1, p2)
          case (None (), None ()) then None ()
          case (Some p, None ()) | (None (), Some p) then Some [p]
          case (Some p1, Some p2) then Some (npatIntersect (p1, p2))
          end)
        pats1 pats2
    in
    let bindings =
      seqMapM (lam kv. map (lam v. (kv.0, v)) kv.1) (mapBindings merged) in
    map (lam bs. SNPat (NPatRecord (mapFromSeq cmpSID bs))) bindings

  sem snpatToPat =
  | NPatRecord pats ->
    PatRecord {
      bindings = mapMap npatToPat pats,
      info = NoInfo (),
      ty = tyunknown_
    }

  sem patToNormpat =
  | PatRecord { bindings = bs } ->
    let nested = mapMap (lam p. patToNormpat p) bs in
    let bindings =
      seqMapM (lam kv. map (lam v. (kv.0, v)) kv.1) (mapBindings nested) in
    map (lam bs. SNPat (NPatRecord (mapFromSeq cmpSID bs))) bindings
end

lang SeqNormPat = NPatImpl + SeqTotPat + SeqEdgePat
  syn SNPat =
  | NPatSeqTot [NPat]
  | NPatSeqEdge { prefix : [NPat], disallowed : Set Int, postfix : [NPat] }

  sem snpatCmp =
  | (NPatSeqTot a, NPatSeqTot b) ->
    seqCmp npatCmp a b
  | (NPatSeqEdge a, NPatSeqEdge b) ->
    let preRes = seqCmp npatCmp a.prefix b.prefix in
    if eqi 0 preRes then
      let midRes = setCmp a.disallowed b.disallowed in
      if eqi 0 midRes then seqCmp npatCmp a.postfix b.postfix
      else midRes
    else preRes

  sem snpatComplement =
  | NPatSeqTot pats ->
    cons (SNPat (NPatSeqEdge { prefix = []
                             , disallowed = setOfSeq subi [length pats]
                             , postfix = [] }))
      (seqComplement (lam x. SNPat (NPatSeqTot x)) pats)
  | NPatSeqEdge { prefix = pre, disallowed = dis, postfix = post } ->
    match (length pre, length post) with (preLen, postLen) in
    let complementedProduct =
      seqComplement
        (lam pats.
          match splitAt pats preLen with (pre, post) in
          SNPat (NPatSeqEdge { prefix = pre
                             , disallowed = dis
                             , postfix = post }))
        (concat pre post)
    in
    let shortTotPats =
      create (addi preLen postLen)
        (lam n. SNPat (NPatSeqTot (make n (wildpat ()))))
    in
    let disTotPats =
      map (lam n. SNPat (NPatSeqTot (make n (wildpat ())))) (setToSeq dis)
    in
    join [complementedProduct, shortTotPats, disTotPats]

  sem snpatIntersect =
  | (NPatSeqTot pats1, NPatSeqTot pats2) ->
    match eqi (length pats1) (length pats2) with false
    then []
    else
      map (lam x. SNPat (NPatSeqTot x))
        (seqMapM (lam x. x)
           (zipWith (lam p1. lam p2. npatIntersect (p1, p2)) pats1 pats2))
  | (NPatSeqEdge { prefix = pre1, disallowed = dis1, postfix = post1},
     NPatSeqEdge { prefix = pre2, disallowed = dis2, postfix = post2}) ->
    let prePreLen = mini (length pre1) (length pre2) in
    match splitAt pre1 prePreLen with (prePre1, prePost1) in
    match splitAt pre2 prePreLen with (prePre2, prePost2) in
    match (length post1, length post2) with (postLen1, postLen2) in
    let postPostLen = mini postLen1 postLen2 in
    match splitAt post1 (subi postLen1 postPostLen) with (postPre1, postPost1) in
    match splitAt post2 (subi postLen2 postPostLen) with (postPre2, postPost2) in

    let prePre =
      seqMapM (lam x. x)
        (zipWith (lam p1. lam p2. npatIntersect (p1, p2)) prePre1 prePre2)
    in
    let postPost =
      seqMapM (lam x. x)
        (zipWith (lam p1. lam p2. npatIntersect (p1, p2)) postPost1 postPost2)
    in
    let prePost = concat prePost1 prePost2 in
    let postPre = concat postPre1 postPre2 in
    let dis =
      mapFilterWithKey (lam i. lam.
        geqi i (addi
                  (addi prePreLen (length prePost))
                  (addi (length postPre) postPostLen)))
        (setUnion dis1 dis2) in

    let simple =
      seqLiftA2 (lam pre. lam post.
        (SNPat (NPatSeqEdge { prefix = concat pre prePost
                            , disallowed = dis
                            , postfix = concat postPre post })))
        prePre postPost
    in

    let overlap =
      if eqSign
           (subi (length prePost1) (length prePost2))
           (subi (length postPre1) (length postPre2))
      then []
      else
        let k = subi (length prePost) (length postPre) in
        let m = maxi (length prePost) (length postPre) in
        let mids =
          join
            (create (absi k) (lam i.
              if setMem (foldl addi 0 [ prePreLen, m, i, postPostLen ]) dis
              then []
              else
                seqMapM (lam x. x)
                  (zipWith (lam p1. lam p2. npatIntersect (p1, p2))
                     (concat prePost (make (addi (maxi 0 (negi k)) i) (wildpat ())))
                     (concat (make (addi (maxi 0 k) i) (wildpat ())) postPre))))
        in
        seqLiftA3 (lam prePre. lam mid. lam postPost.
          SNPat (NPatSeqTot (join [prePre, mid, postPost])))
          prePre mids postPost
    in
    concat simple overlap

  | (NPatSeqEdge { prefix = pre, disallowed = dis, postfix = post },
     NPatSeqTot pats)
  | (NPatSeqTot pats,
     NPatSeqEdge { prefix = pre, disallowed = dis, postfix = post }) ->
    match (length pre, length post, length pats) with (preLen, postLen, patLen) in
    if setMem patLen dis then [] else
      if gti (addi preLen postLen) patLen then []
      else
        map (lam x. SNPat (NPatSeqTot x))
          (seqMapM (lam x. x)
             (zipWith (lam p1. lam p2. npatIntersect (p1, p2))
                (join [pre, make (subi (subi patLen preLen) postLen) (wildpat ()), post])
                pats))

  sem snpatToPat =
  | NPatSeqTot pats -> pseqtot_ (map npatToPat pats)
  | NPatSeqEdge {prefix = pre, disallowed = dis, postfix = post} ->
    let edgepat = pseqedgew_ (map npatToPat pre) (map npatToPat post) in
    if setIsEmpty dis then edgepat else
      pand_ edgepat
        (pnot_ (foldl1 por_ (map (lam n. pseqtot_ (make n pvarw_)) (setToSeq dis))))

  sem patToNormpat =
  | PatSeqTot { pats = ps } ->
    map (lam x. SNPat (NPatSeqTot x))
      (seqMapM (lam x. x) (map patToNormpat ps))
  | PatSeqEdge { prefix = pre, postfix = post } ->
    let pre  = seqMapM (lam x. x) (map patToNormpat pre)  in
    let post = seqMapM (lam x. x) (map patToNormpat post) in
    seqLiftA2 (lam pre. lam post.
      (SNPat (NPatSeqEdge { prefix = pre
                          , disallowed = setEmpty subi
                          , postfix = post })))
      pre post
end

lang NamedNormPat = NPatImpl + NamedPat
  sem patToNormpat =
  | PatNamed _ -> [wildpat ()]
end

lang AndNormPat = NPatImpl + AndPat
  sem patToNormpat =
  | PatAnd {lpat = l, rpat = r} ->
    normpatIntersect (patToNormpat l) (patToNormpat r)
end

lang OrNormPat = NPatImpl + OrPat
  sem patToNormpat =
  | PatOr {lpat = l, rpat = r} ->
    concat (patToNormpat l) (patToNormpat r)
end

lang NotNormPat = NPatImpl + NotPat
  sem patToNormpat =
  | PatNot {subpat = p} ->
    normpatComplement (patToNormpat p)
end


lang NormPatMatch = NPatImpl + VarAst
  sem matchNormpat : (Expr, NormPat) -> [Map Name NormPat]
  sem matchNormpat =
  | (e, np) ->
    mapOption (lam p. matchNPat (e, p)) np

  sem matchNPat : (Expr, NPat) -> Option (Map Name NormPat)
  sem matchNPat =
  | (TmVar x, p) -> Some (mapFromSeq nameCmp [(x.ident, [p])])
  | (!TmVar _ & e, SNPat p) -> matchSNPat (e, p)
  | (!TmVar _ & e, NPatNot cons) ->
    if optionMapOr false (lam x. setMem x cons) (exprToSimpleCon e) then None ()
    else Some (mapEmpty nameCmp)
  | _ ->
    error "Impossible match in matchNPat!"

  sem matchSNPat : (Expr, SNPat) -> Option (Map Name NormPat)
  sem matchSNPat =
  | (_, p) -> Some (mapEmpty nameCmp)

  sem exprToSimpleCon : Expr -> Option SimpleCon
  sem exprToSimpleCon =
  | _ -> None ()
end

lang IntNormPatMatch = NormPatMatch + IntAst + IntNormPat
  sem exprToSimpleCon =
  | TmConst { val = CInt i } -> Some (IntCon i.val)

  sem matchSNPat =
  | (TmConst {val = CInt i}, NPatInt j) ->
    if eqi i.val j then Some (mapEmpty nameCmp)
    else None ()
end

lang CharNormPatMatch = NormPatMatch + CharAst + CharNormPat
  sem exprToSimpleCon =
  | TmConst { val = CChar i } -> Some (CharCon i.val)

  sem matchSNPat =
  | (TmConst {val = CChar i}, NPatChar j) ->
    if eqc i.val j then Some (mapEmpty nameCmp)
    else None ()
end

lang BoolNormPatMatch = NormPatMatch + BoolAst + BoolNormPat
  sem exprToSimpleCon =
  | TmConst { val = CBool i } -> Some (BoolCon i.val)

  sem matchSNPat =
  | (TmConst {val = CBool i}, NPatBool j) ->
    if eqi (if i.val then 1 else 0) (if j then 1 else 0)
    then Some (mapEmpty nameCmp)
    else None ()
end

lang ConNormPatMatch = NormPatMatch + DataAst + ConNormPat
  sem exprToSimpleCon =
  | TmConApp { ident = cident } -> Some (ConCon cident)

  sem matchSNPat =
  | (TmConApp {ident = cident, body = b}, NPatCon {ident = pident, subpat = p}) ->
    if nameEq cident pident
    then matchNPat (b, p)
    else None ()
end

lang RecordNormPatMatch = NormPatMatch + RecordAst + RecordNormPat
  sem matchSNPat =
  | (TmRecord {bindings = bs}, NPatRecord pbs) ->
    mapFoldlOption
      (lam acc. lam. lam m. optionMap (mapUnionWith normpatIntersect acc) m)
      (mapEmpty nameCmp)
      (mapIntersectWith (lam e. lam p. matchNPat (e, p)) bs pbs)
end

lang SeqNormPatMatch = NormPatMatch + SeqAst + SeqNormPat
  sem matchSNPat =
  | (TmSeq {tms = tms}, NPatSeqTot pats) ->
    if eqi (length tms) (length pats) then
      optionFoldlM
        (lam acc. lam m. optionMap (mapUnionWith normpatIntersect acc) m)
        (mapEmpty nameCmp)
        (zipWith (lam e. lam p. matchNPat (e, p)) tms pats)
    else None ()
  | (TmSeq {tms = tms},
     NPatSeqEdge { prefix = pre, disallowed = dis, postfix = post }) ->
    match (length pre, length post, length tms) with (preLen, postLen, tmsLen) in
    if setMem tmsLen dis then None () else
      if gti (addi preLen postLen) tmsLen then None ()
      else
        match splitAt tms preLen with (preTm, tms) in
        match splitAt tms (subi (length tms) postLen) with (tms, postTm) in
        optionFoldlM
          (lam acc. lam m. optionMap (mapUnionWith normpatIntersect acc) m)
          (mapEmpty nameCmp)
          (zipWith (lam e. lam p. matchNPat (e, p))
             (concat preTm postTm) (concat pre post))
end

lang MExprPatAnalysis =
  NormPatImpl + IntNormPat + CharNormPat + BoolNormPat +
  ConNormPat + RecordNormPat + SeqNormPat + NamedNormPat +
  AndNormPat + OrNormPat + NotNormPat +

  NormPatMatch + IntNormPatMatch + CharNormPatMatch +
  BoolNormPatMatch + ConNormPatMatch + RecordNormPatMatch +
  SeqNormPatMatch
end
