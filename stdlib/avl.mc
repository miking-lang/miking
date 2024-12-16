-- Implementation of AVL trees.

include "option.mc"
include "string.mc"

lang AVLTreeImpl
  syn AVL k v =
  | Leaf ()
  | Node {key : k, value : v, l : AVL k v, r : AVL k v, h : Int}

  sem avlSize : all k. all v. AVL k v -> Int
  sem avlSize =
  | Leaf _ -> 0
  | Node {l = l, r = r} -> addi (addi (avlSize l) (avlSize r)) 1

  sem avlHeight : all k. all v. AVL k v -> Int
  sem avlHeight =
  | Leaf _ -> 0
  | Node {h = h} -> h

  sem avlEmpty : all k. all v. () -> AVL k v
  sem avlEmpty =
  | () -> Leaf ()

  sem avlIsEmpty : all k. all v. AVL k v -> Bool
  sem avlIsEmpty =
  | Leaf _ -> true
  | Node _ -> false

  sem avlCreate : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlCreate k v l =
  | r ->
    let lh = avlHeight l in
    let rh = avlHeight r in
    let h = addi (if geqi lh rh then lh else rh) 1 in
    Node {key = k, value = v, l = l, r = r, h = h}

  -- NOTE(larshum, 2023-03-04): The four rotation functions used for the AVL
  -- tree are defined below. These take the components of the tree, rather than
  -- a complete tree, as this avoids an extra allocation. Therefore, in two of
  -- the rotation functions, we reverse the argument order of the left and
  -- right subtrees to allow pattern matching on the subtree of interest.
  sem avlRotateLeft : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlRotateLeft k v l =
  | Node (rt & {l = rl, r = rr}) ->
    avlCreate rt.key rt.value (avlCreate k v l rl) rr
  | Leaf _ -> error "avlRotateLeft: empty tree"

  sem avlRotateRightLeft : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlRotateRightLeft k v l =
  | Node (rt & {l = Node rlt, r = rr}) ->
    avlCreate rlt.key rlt.value
      (avlCreate k v l rlt.l)
      (avlCreate rt.key rt.value rlt.r rr)
  | Node _ -> error "avlRotateRightLeft: invalid shape of tree"
  | Leaf _ -> error "avlRotateRightLeft: empty tree"

  sem avlRotateRight : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlRotateRight k v r =
  | Node (lt & {l = ll, r = lr}) ->
    avlCreate lt.key lt.value ll (avlCreate k v lr r)
  | Leaf _ -> error "avlRotateRight: empty tree"

  sem avlRotateLeftRight : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlRotateLeftRight k v r =
  | Node (lt & {l = ll, r = Node lrt}) ->
    avlCreate lrt.key lrt.value
      (avlCreate lt.key lt.value ll lrt.l)
      (avlCreate k v lrt.r r)
  | Node _ -> error "avlRotateLeftRight: invalid shape of tree"
  | Leaf _ -> error "avlRotateLeftRight: empty tree"

  -- NOTE(larshum, 2023-03-04): Joins two AVL trees where the provided key is
  -- greater than all keys in the left subtree and less than all keys in the
  -- right subtree. The resulting tree is balanced according to the balancing
  -- criteria of AVL trees.
  --
  -- We reverse the argument order (in avlJoinRight) to simplify pattern
  -- matching.
  sem avlJoin : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlJoin k v l =
  | r ->
    let lh = avlHeight l in
    let rh = avlHeight r in
    if gti lh (addi rh 1) then avlJoinRight k v r l
    else if gti rh (addi lh 1) then avlJoinLeft k v l r
    else avlCreate k v l r

  sem avlJoinLeft : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlJoinLeft k v l =
  | Node tr ->
    if leqi (avlHeight tr.l) (addi (avlHeight l) 1) then
      let t = avlCreate k v l tr.l in
      if leqi (avlHeight t) (addi (avlHeight tr.r) 1) then
        avlCreate tr.key tr.value t tr.r
      else
        avlRotateRight tr.key tr.value tr.r (avlRotateLeft k v l tr.l)
    else
      let tx = avlJoinLeft k v l tr.l in
      if leqi (avlHeight tx) (addi (avlHeight tr.r) 1) then
        avlCreate tr.key tr.value tx tr.r
      else
        avlRotateRight tr.key tr.value tr.r tx
  | Leaf _ ->  error "avlJoinLeft: empty tree"

  sem avlJoinRight : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlJoinRight k v r =
  | Node tl ->
    if leqi (avlHeight tl.r) (addi (avlHeight r) 1) then
      let t = avlCreate k v tl.r r in
      if leqi (avlHeight t) (addi (avlHeight tl.l) 1) then
        avlCreate tl.key tl.value tl.l t
      else
        avlRotateLeft tl.key tl.value tl.l (avlRotateRight k v r tl.r)
    else
      let tx = avlJoinRight k v r tl.r in
      if leqi (avlHeight tx) (addi (avlHeight tl.l) 1) then
        avlCreate tl.key tl.value tl.l tx
      else
        avlRotateLeft tl.key tl.value tl.l tx
  | Leaf _ -> error "avlJoinRight: empty tree"

  -- NOTE(larshum, 2023-03-04): Splits an AVL into two parts based on a
  -- provided key. Returns two trees consisting of all keys less than and
  -- greater than the provided key respectively. If the provided tree contains
  -- an entry for the given key, it also returns the value associated with that
  -- key.
  sem avlSplit : all k. all v.
    (k -> k -> Int) -> k -> AVL k v -> (AVL k v, Option v, AVL k v)
  sem avlSplit cmp k =
  | Leaf _ -> (Leaf (), None (), Leaf ())
  | Node t ->
    let d = cmp k t.key in
    if lti d 0 then
      match avlSplit cmp k t.l with (ll, v, lr) in
      (ll, v, avlJoin t.key t.value lr t.r)
    else if gti d 0 then
      match avlSplit cmp k t.r with (rl, v, rr) in
      (avlJoin t.key t.value t.l rl, v, rr)
    else
      (t.l, Some t.value, t.r)

  -- NOTE(larshum, 2023-03-04): Joins two subtrees where all keys in the left
  -- subtree are less than those in the right subtree, without a provided key
  -- and value. We split out the minimum element of the right subtree and use
  -- that key-value pair in the standard join function.
  sem avlJoin2 : all k. all v. AVL k v -> AVL k v -> AVL k v
  sem avlJoin2 l =
  | r ->
    switch (l, r)
    case (_, Leaf _) then l
    case (Leaf _, _) then r
    case _ then
      match avlSplitFirst r with (rk, rv, r) in
      avlJoin rk rv l r
    end

  sem avlSplitFirst : all k. all v. AVL k v -> (k, v, AVL k v)
  sem avlSplitFirst =
  | Node (t & {l = Leaf _}) -> (t.key, t.value, t.r)
  | Node t ->
    match avlSplitFirst t.l with (k, v, l) in
    let hd = subi (avlHeight l) (avlHeight t.r) in
    if lti hd (negi 1) then (k, v, avlBalanceRight t.key t.value l t.r)
    else (k, v, avlCreate t.key t.value l t.r)
  | Leaf _ -> error "avlSplitLast: empty tree"

  sem avlBalanceRight : all k. all v. k -> v -> AVL k v -> AVL k v -> AVL k v
  sem avlBalanceRight k v l =
  | r & (Node rt) ->
    if geqi (avlHeight rt.r) (avlHeight rt.l) then avlRotateLeft k v l r
    else avlRotateRightLeft k v l r
  | Leaf _ -> error "avlBalanceRight: empty tree"

  -- NOTE(larshum, 2023-03-04): We use a join-based implementation, where the
  -- insertion and deletion operations are defined in terms of the join
  -- function above.
  sem avlInsert : all k. all v. (k -> k -> Int) -> k -> v -> AVL k v -> AVL k v
  sem avlInsert cmp k v =
  | Leaf _ ->
    Node {key = k, value = v, l = Leaf (), r = Leaf (), h = 1}
  | Node t ->
    let d = cmp k t.key in
    if lti d 0 then avlJoin t.key t.value (avlInsert cmp k v t.l) t.r
    else if gti d 0 then avlJoin t.key t.value t.l (avlInsert cmp k v t.r)
    else Node {t with value = v}

  sem avlRemove : all k. all v. (k -> k -> Int) -> k -> AVL k v -> AVL k v
  sem avlRemove cmp k =
  | Leaf _ ->
    Leaf ()
  | Node t ->
    let d = cmp k t.key in
    if lti d 0 then avlJoin t.key t.value (avlRemove cmp k t.l) t.r
    else if gti d 0 then avlJoin t.key t.value t.l (avlRemove cmp k t.r)
    else avlJoin2 t.l t.r

  sem avlLookup : all k. all v. (k -> k -> Int) -> k -> AVL k v -> Option v
  sem avlLookup cmp k =
  | Leaf _ ->
    None ()
  | Node t ->
    let d = cmp k t.key in
    if lti d 0 then avlLookup cmp k t.l
    else if gti d 0 then avlLookup cmp k t.r
    else Some t.value

  -- `avlFindUpper cmp k t` returns (k', v) in the tree `t`, where k' is the
  -- minimum key in the tree and k≤k', according to `cmp`. Returns `None ()` if
  -- no such key k' exists in the tree.
  sem avlFindUpper : all k. all v. (k -> k -> Int) -> k -> AVL k v -> Option (k, v)
  sem avlFindUpper cmp k =
  | Node t ->
    let d = cmp k t.key in
    if gti d 0 then avlFindUpper cmp k t.r
    else
      switch avlFindUpper cmp k t.l
        case None _ then Some (t.key, t.value)
        case value then value
      end
  | Leaf _ -> None ()

  -- `avlFindLower cmp k t` returns (k', v) in the tree `t`, where k' is the
  -- maximum key in the tree and k≥k', according to `cmp`. Returns `None ()` if
  -- no such key k' exists in the tree.
  sem avlFindLower : all k. all v. (k -> k -> Int) -> k -> AVL k v -> Option (k, v)
  sem avlFindLower cmp k =
  | Node t ->
    let d = cmp k t.key in
    if lti d 0 then avlFindLower cmp k t.l
    else
      switch avlFindLower cmp k t.r
        case None _ then Some (t.key, t.value)
        case value then value
      end
  | Leaf _ -> None ()

  sem avlChoose : all k. all v. AVL k v -> Option (k, v)
  sem avlChoose =
  | Leaf _ -> None ()
  | Node t -> Some (t.key, t.value)

  sem avlMap : all k. all a. all b. (k -> a -> b) -> AVL k a -> AVL k b
  sem avlMap f =
  | Leaf _ ->
    Leaf ()
  | Node t ->
    Node { key = t.key, value = f t.key t.value,
           l = avlMap f t.l, r = avlMap f t.r, h = t.h }

  sem avlFold : all a. all k. all v. (a -> k -> v -> a) -> a -> AVL k v -> a
  sem avlFold f acc =
  | Leaf _ ->
    acc
  | Node t ->
    let acc = avlFold f acc t.l in
    let acc = f acc t.key t.value in
    avlFold f acc t.r

  sem avlToSeq : all k. all v. [(k, v)] -> AVL k v -> [(k, v)]
  sem avlToSeq acc =
  | Leaf _ ->
    acc
  | Node t ->
    let acc = avlToSeq acc t.r in
    let acc = cons (t.key, t.value) acc in
    avlToSeq acc t.l

  sem avlFromSeq : all k. all v. (k -> k -> Int) -> [(k, v)] -> AVL k v
  sem avlFromSeq cmp =
  | [] ->
    Leaf ()
  | [(k, v)] ->
    Node {key = k, value = v, l = Leaf (), r = Leaf (), h = 1}
  | s ->
    let mid = divi (length s) 2 in
    match splitAt s mid with (lhs, rhs) in
    let l = avlFromSeq cmp lhs in
    let r = avlFromSeq cmp rhs in
    avlUnionWith cmp (lam. lam rv. rv) l r

  -- NOTE(larshum, 2023-03-05): We can represent equivalent AVL trees in
  -- multiple ways. Therefore, we do not want to compare the structure of the
  -- trees, but only the values found in these. By making use of this auxiliary
  -- data structure, we compare the key-value pairs of the trees in a
  -- left-to-right order.
  syn AuxTree k v =
  | Cont {key : k, value : v, r : AVL k v, next : AuxTree k v}
  | End ()

  sem avlToAux : all k. all v. AuxTree k v -> AVL k v -> AuxTree k v
  sem avlToAux acc =
  | Node t ->
    avlToAux (Cont {key = t.key, value = t.value, r = t.r, next = acc}) t.l
  | Leaf _ ->
    acc

  sem avlEq : all k. all v.
    (k -> k -> Int) -> (v -> v -> Bool) -> AVL k v -> AVL k v -> Bool
  sem avlEq cmpk eqv l =
  | r -> avlEqH cmpk eqv (avlToAux (End ()) l, avlToAux (End ()) r)

  sem avlEqH : all k. all v.
    (k -> k -> Int) -> (v -> v -> Bool) -> (AuxTree k v, AuxTree k v) -> Bool
  sem avlEqH cmpk eqv =
  | (End _, End _) -> true
  | (End _, Cont _) -> false
  | (Cont _, End _) -> false
  | (Cont l, Cont r) ->
    if eqi (cmpk l.key r.key) 0 then
      if eqv l.value r.value then
        avlEqH cmpk eqv (avlToAux l.next l.r, avlToAux r.next r.r)
      else false
    else false

  sem avlCmp : all k. all v.
    (k -> k -> Int) -> (v -> v -> Int) -> AVL k v -> AVL k v -> Int
  sem avlCmp cmpk cmpv l =
  | r -> avlCmpH cmpk cmpv (avlToAux (End ()) l, avlToAux (End ()) r)

  sem avlCmpH : all k. all v.
    (k -> k -> Int) -> (v -> v -> Int) -> (AuxTree k v, AuxTree k v) -> Int
  sem avlCmpH cmpk cmpv =
  | (End _, End _) -> 0
  | (End _, Cont _) -> negi 1
  | (Cont _, End _) -> 1
  | (Cont l, Cont r) ->
    let dk = cmpk l.key r.key in
    if neqi dk 0 then dk else
    let dv = cmpv l.value r.value in
    if neqi dv 0 then dv else
    avlCmpH cmpk cmpv (avlToAux l.next l.r, avlToAux r.next r.r)

  -- NOTE(larshum, 2023-03-04): Efficient operations for general merging of
  -- maps, as well as specialized versions for union, intersection, and
  -- difference.
  -- OPT(larshum, 2023-03-04): Many of the functions below are trivially
  -- parallelizable, but such functions cannot be used from the boot
  -- interpreter so they are left sequential for now.
  sem avlMerge : all k. all a. all b. all c.
    (k -> k -> Int) -> (Option a -> Option b -> Option c) -> AVL k a ->
    AVL k b -> AVL k c
  sem avlMerge cmp f l = | r -> avlMergeWithKey cmp (lam. f) l r
  sem avlMergeWithKey : all k. all a. all b. all c.
    (k -> k -> Int) -> (k -> Option a -> Option b -> Option c) -> AVL k a ->
    AVL k b -> AVL k c
  sem avlMergeWithKey cmp f l =
  | r ->
    match (l, r) with (Leaf _, Leaf _) then Leaf ()
    else if geqi (avlHeight l) (avlHeight r) then
      match l with Node lt then
        match avlSplit cmp lt.key r with (rl, rv, rr) in
        let lhs = avlMergeWithKey cmp f lt.l rl in
        let rhs = avlMergeWithKey cmp f lt.r rr in
        match f lt.key (Some lt.value) rv with Some v then avlJoin lt.key v lhs rhs
        else avlJoin2 lhs rhs
      else error "avlMergeWithKey: empty left tree"
    else
      match r with Node rt then
        match avlSplit cmp rt.key l with (ll, lv, lr) in
        let lhs = avlMergeWithKey cmp f ll rt.l in
        let rhs = avlMergeWithKey cmp f lr rt.r in
        match f rt.key lv (Some rt.value) with Some v then avlJoin rt.key v lhs rhs
        else avlJoin2 lhs rhs
      else error "avlMergeWithKey: empty right tree"

  sem avlUnionWith : all k. all v.
    (k -> k -> Int) -> (v -> v -> v) -> AVL k v -> AVL k v -> AVL k v
  sem avlUnionWith cmp f l =
  | r ->
    match l with Leaf _ then r
    else match r with Leaf _ then l
    else if geqi (avlHeight l) (avlHeight r) then
      match l with Node lt then
        match avlSplit cmp lt.key r with (rl, rv, rr) in
        let lhs = avlUnionWith cmp f lt.l rl in
        let rhs = avlUnionWith cmp f lt.r rr in
        let value = match rv with Some x then f lt.value x else lt.value in
        avlJoin lt.key value lhs rhs
      else error "avlUnionWith: empty left tree"
    else
      match r with Node rt then
        match avlSplit cmp rt.key l with (ll, lv, lr) in
        let lhs = avlUnionWith cmp f ll rt.l in
        let rhs = avlUnionWith cmp f lr rt.r in
        let value = match lv with Some x then f x rt.value else rt.value in
        avlJoin rt.key value lhs rhs
      else error "avlUnionWith: empty right tree"

  sem avlIntersectWith : all k. all a. all b. all c.
    (k -> k -> Int) -> (a -> b -> c) -> AVL k a -> AVL k b -> AVL k c
  sem avlIntersectWith cmp f l =
  | r ->
    match l with Leaf _ then Leaf ()
    else match r with Leaf _ then Leaf ()
    else if geqi (avlHeight l) (avlHeight r) then
      match l with Node lt then
        match avlSplit cmp lt.key r with (rl, rv, rr) in
        let lhs = avlIntersectWith cmp f lt.l rl in
        let rhs = avlIntersectWith cmp f lt.r rr in
        match rv with Some x then
          avlJoin lt.key (f lt.value x) lhs rhs
        else
          avlJoin2 lhs rhs
      else error "avlIntersectWith: empty left tree"
    else
      match r with Node rt then
        match avlSplit cmp rt.key l with (ll, lv, lr) in
        let lhs = avlIntersectWith cmp f ll rt.l in
        let rhs = avlIntersectWith cmp f lr rt.r in
        match lv with Some x then
          avlJoin rt.key (f x rt.value) lhs rhs
        else
          avlJoin2 lhs rhs
      else error "avlIntersectWith: empty right tree"

  sem avlDifference : all k. all a. all b. (k -> k -> Int) -> AVL k a -> AVL k b -> AVL k a
  sem avlDifference cmp l =
  | r ->
    match l with Leaf _ then Leaf ()
    else match r with Leaf _ then l
    else
      match l with Node lt then
        match avlSplit cmp lt.key r with (rl, rv, rr) in
        let lhs = avlDifference cmp lt.l rl in
        let rhs = avlDifference cmp lt.r rr in
        match rv with Some x then
          avlJoin2 lhs rhs
        else
          avlJoin lt.key lt.value lhs rhs
      else error "avlDifference: empty left tree"

  sem avlMapOption : all k. all a. all b. (k -> a -> Option b) -> AVL k a -> AVL k b
  sem avlMapOption f =
  | Node t ->
    let lhs = avlMapOption f t.l in
    let rhs = avlMapOption f t.r in
    match f t.key t.value with Some value then avlJoin t.key value lhs rhs
    else avlJoin2 lhs rhs
  | Leaf _ ->
    Leaf ()

  sem avlFilter : all k. all v. (k -> v -> Bool) -> AVL k v -> AVL k v
  sem avlFilter p =
  | Node t ->
    let lhs = avlFilter p t.l in
    let rhs = avlFilter p t.r in
    if p t.key t.value then avlJoin t.key t.value lhs rhs
    else avlJoin2 lhs rhs
  | Leaf _ ->
    Leaf ()

  -- NOTE(larshum, 2023-03-05): Validates the provided AVL tree by:
  -- 1. For each node in the tree, ensuring that the height of its left and
  --    right subtrees differ by at most one.
  -- 2. Ensuring that the keys are in sorted order.
  --
  -- The function returns true if the AVL tree is found to be valid, and false
  -- otherwise.
  sem avlValidate : all k. all v. (k -> k -> Int) -> AVL k v -> Bool
  sem avlValidate cmp =
  | t ->
    if avlValidateHeight t then
      let keys = avlFold (lam acc. lam k. lam. snoc acc k) [] t in
      eqSeq (lam l. lam r. eqi (cmp l r) 0) keys (sort cmp keys)
    else false

  sem avlValidateHeight : all k. all v. AVL k v -> Bool
  sem avlValidateHeight =
  | Node t ->
    let lh = avlHeight t.l in
    let rh = avlHeight t.r in
    if or (gti lh (addi rh 1)) (gti rh (addi lh 1)) then false
    else and (avlValidateHeight t.l) (avlValidateHeight t.r)
  | Leaf _ ->
    true
end

mexpr

use AVLTreeImpl in

let t1 = avlEmpty () in
let t2 : AVL Int Char = avlCreate 0 '0' (avlEmpty ()) (avlEmpty ()) in
utest avlSize t1 with 0 in
utest avlHeight t1 with 0 in
utest avlSize t2 with 1 in
utest avlHeight t2 with 1 in

let mknode = lam k. lam l. lam r. avlCreate k () l r in
let mkleaf = lam k. mknode k (avlEmpty ()) (avlEmpty ()) in
let deconstruct = lam n.
  match n with Node t then (t.key, t.value, t.l, t.r)
  else error "Cannot deconstruct empty tree"
in
let eqset = lam cmpk. lam l. lam r. avlEq cmpk (lam. lam. true) l r in

-- NOTE(larshum, 2023-03-04): Tests that the rotations behave as expected.
let lt = mknode 2 (mknode 1 (mkleaf 0) (mkleaf 3)) (mkleaf 4) in
match deconstruct lt with (lk, lv, ll, lr) in
let rt = mknode 1 (mkleaf 0) (mknode 2 (mkleaf 3) (mkleaf 4)) in
match deconstruct rt with (rk, rv, rl, rr) in
utest avlRotateRight lk lv lr ll with rt using eqset subi in
utest avlRotateLeft rk rv rl rr with lt using eqset subi in

let bal =
  mknode 3 (mknode 1 (mkleaf 0) (mkleaf 2)) (mknode 5 (mkleaf 4) (mkleaf 6))
in
let lt =
  mknode 5 (mknode 1 (mkleaf 0) (mknode 3 (mkleaf 2) (mkleaf 4))) (mkleaf 6)
in
match deconstruct lt with (lk, lv, ll, lr) in
let rt =
  mknode 1 (mkleaf 0) (mknode 5 (mknode 3 (mkleaf 2) (mkleaf 4)) (mkleaf 6))
in
match deconstruct rt with (rk, rv, rl, rr) in
utest avlRotateLeftRight lk lv lr ll with bal using eqset subi in
utest avlRotateRightLeft rk rv rl rr with bal using eqset subi in

let l = mknode 1 (mkleaf 0) (mkleaf 2) in
let r = mknode 5 (mkleaf 4) (mkleaf 6) in
utest avlJoin 3 () l r with bal using eqset subi in
let joined = mknode 4 l (mknode 5 (avlEmpty ()) (mkleaf 6)) in
utest avlJoin2 l r with joined using eqset subi in

-- NOTE(larshum, 2023-03-05): Below are a couple of carefully designed tests
-- that ensures the latter paths of the avlJoinLeft and avlJoinRight functions
-- runs. For simplicity, I use a validation function to ensure that the tree
-- remains valid after the joining, rather than testing on the exact shape of
-- the resulting tree.
let ll1 =
  mknode 1 (mkleaf 0) (mkleaf 2)
in
let ll2 =
  mknode 3 ll1 (mkleaf 4)
in
let lr =
  mknode 9
    (mknode 7 (mkleaf 6) (mkleaf 8))
    (mknode 11 (mkleaf 10) (mkleaf 12))
in
let r = mkleaf 14 in
let rr1 =
  mknode 13 (mkleaf 12) (mkleaf 14)
in
let rr2 =
  mknode 15 rr1 (mkleaf 16)
in
let rl =
  mknode 7
    (mknode 5 (mkleaf 4) (mkleaf 6))
    (mknode 9 (mkleaf 8) (mkleaf 10))
in
let l = mkleaf 0 in
utest avlValidate subi ll1 with true in
utest avlValidate subi ll2 with true in
utest avlValidate subi lr with true in
utest avlValidate subi r with true in
utest avlValidate subi (avlJoin 13 () (mknode 5 ll1 lr) r) with true in
utest avlValidate subi (avlJoin 13 () (mknode 5 ll2 lr) r) with true in
utest avlValidate subi rr1 with true in
utest avlValidate subi rr2 with true in
utest avlValidate subi rl with true in
utest avlValidate subi l with true in
utest avlValidate subi (avlJoin 2 () l (mknode 11 rl rr1)) with true in
utest avlValidate subi (avlJoin 2 () l (mknode 11 rl rr2)) with true in

let l = mknode 1 (mkleaf 0) (mkleaf 2) in
let r = mknode 5 (mkleaf 4) (mkleaf 6) in
match avlSplit subi 3 l with (lhs, v, rhs) in
utest lhs with l using eqset subi in
utest v with None () in
utest rhs with avlEmpty () using eqset subi in
match avlSplit subi 5 r with (lhs, v, rhs) in
utest lhs with mkleaf 4 using eqset subi in
utest v with Some () in
utest rhs with mkleaf 6 using eqset subi in

match avlSplitFirst l with (k, _, rest) in
utest k with 0 in
utest rest with mknode 1 (avlEmpty ()) (mkleaf 2) using eqset subi in
match avlSplitFirst joined with (k, _, rest2) in
utest k with 0 in
utest rest2 with mknode 4 rest (mknode 5 (avlEmpty ()) (mkleaf 6)) using eqset subi in

let t1 = avlInsert subi 0 '0' (avlEmpty ()) in
utest avlSize t1 with 1 in
utest avlLookup subi 0 t1 with Some '0' in

let t2 = avlInsert subi 7 '7' t1 in
utest avlSize t2 with 2 in
utest avlLookup subi 7 t2 with Some '7' in

let t3 = avlInsert subi 4 '4' t2 in
utest avlSize t3 with 3 in
utest avlLookup subi 4 t3 with Some '4' in

let t4 = avlInsert subi 0 '2' t3 in
utest avlSize t4 with 3 in
utest avlLookup subi 0 t4 with Some '2' in
utest avlToSeq [] t4 with [(0, '2'), (4, '4'), (7, '7')] in

let t5 = avlRemove subi 4 t4 in
utest avlSize t5 with 2 in
utest avlLookup subi 4 t4 with Some '4' in
utest avlLookup subi 4 t5 with None () in
utest avlToSeq [] t5 with [(0, '2'), (7, '7')] in

let f = lam k. lam. addi k 1 in
let t6 = avlMap f t4 in
utest avlSize t6 with 3 in
utest avlLookup subi 0 t6 with Some 1 in
utest avlToSeq [] t6 with [(0, 1), (4, 5), (7, 8)] in

utest avlChoose (avlEmpty ()) with None () using optionEq (lam. lam. true) in
utest optionIsSome (avlChoose t5) with true in

let f = lam acc. lam. lam v. addi acc v in
let tot = avlFold f 0 t6 in
utest tot with 14 in

let lhs = mknode 1 (mkleaf 0) (avlEmpty ()) in
let rhs = mknode 0 (avlEmpty ()) (mkleaf 1) in
utest lhs with rhs using eqset subi in

utest avlCmp subi cmpChar t3 t4 with 0 using lti in
utest avlCmp subi cmpChar t4 t3 with 0 using gti in
utest avlCmp subi cmpChar t3 t3 with 0 in

let eqAvlSeq = lam cmpk. lam eqv. lam avl. lam seq.
  avlEq cmpk eqv avl (avlFromSeq cmpk seq)
in
let t1 = avlFromSeq subi [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)] in
let t2 = avlFromSeq subi [(3, 2), (4, 3), (5, 4)] in
let t3 = avlFromSeq subi [(negi 1, 1), (1, 3), (2, 4)] in
let chooseLeft = lam l. lam. l in
let chooseRight = lam. lam r. r in

utest avlToSeq [] (avlUnionWith subi chooseLeft t1 t2)
with [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 4)] in
utest avlToSeq [] (avlUnionWith subi chooseRight t1 t2)
with [(0, 1), (1, 2), (2, 3), (3, 2), (4, 3), (5, 4)] in
utest avlUnionWith subi chooseLeft t2 t3 with avlUnionWith subi chooseRight t2 t3
using avlEq subi eqi in

-- NOTE(larshum, 2023-03-14): Test that avlFromSeq chooses the rightmost value,
-- to make 'mapFromSeq' consistent with 'mapUnion'.
utest avlLookup subi 0 (avlFromSeq subi [(0, 0), (0, 1)]) with Some 1 in

utest avlIntersectWith subi chooseLeft t1 t2 with [(3, 4), (4, 5)] using eqAvlSeq subi eqi in
utest avlIntersectWith subi chooseRight t1 t2 with [(3, 2), (4, 3)] using eqAvlSeq subi eqi in
utest avlIntersectWith subi chooseLeft t1 t3 with [(1, 2), (2, 3)] using eqAvlSeq subi eqi in
utest avlIntersectWith subi chooseLeft t2 t3 with avlEmpty () using avlEq subi eqi in

utest avlDifference subi t1 t2 with [(0, 1), (1, 2), (2, 3)] using eqAvlSeq subi eqi in
utest avlDifference subi t2 t1 with [(5, 4)] using eqAvlSeq subi eqi in
utest avlDifference subi t3 t1 with [(negi 1, 1)] using eqAvlSeq subi eqi in
utest avlDifference subi t2 t3 with t2 using avlEq subi eqi in
utest avlDifference subi t3 t2 with t3 using avlEq subi eqi in

let evenKey = lam k. lam. eqi (modi k 2) 0 in
let sumLessThanFive = lam k. lam v. lti (addi k v) 5 in
let falseFn = lam. lam. false in
utest avlFilter evenKey t1 with [(0, 1), (2, 3), (4, 5)] using eqAvlSeq subi eqi in
utest avlFilter sumLessThanFive t1 with [(0, 1), (1, 2)] using eqAvlSeq subi eqi in
utest avlFilter falseFn t1 with avlEmpty () using avlEq subi eqi in

let cmp = lam a. lam b. if ltf a b then -1 else if gtf a b then 1 else 0 in
let t = avlFromSeq cmp [(0., 0), (1., 1), (2., 2), (3., 3), (4., 4)] in
utest avlFindUpper cmp 4.5 t with None () in
utest avlFindUpper cmp 4. t with Some (4., 4) in
utest avlFindUpper cmp 3.5 t with Some (4., 4) in
utest avlFindUpper cmp 3. t with Some (3., 3) in
utest avlFindUpper cmp 2.5 t with Some (3., 3) in
utest avlFindUpper cmp 2. t with Some (2., 2) in
utest avlFindUpper cmp 1.5 t with Some (2., 2) in
utest avlFindUpper cmp 1. t with Some (1., 1) in
utest avlFindUpper cmp 0.5 t with Some (1., 1) in
utest avlFindUpper cmp 0. t with Some (0., 0) in
utest avlFindLower cmp 4.5 t with Some (4., 4) in
utest avlFindLower cmp 4. t with Some (4., 4) in
utest avlFindLower cmp 3.5 t with Some (3., 3) in
utest avlFindLower cmp 3. t with Some (3., 3) in
utest avlFindLower cmp 2.5 t with Some (2., 2) in
utest avlFindLower cmp 2. t with Some (2., 2) in
utest avlFindLower cmp 1.5 t with Some (1., 1) in
utest avlFindLower cmp 1. t with Some (1., 1) in
utest avlFindLower cmp 0.5 t with Some (0., 0) in
utest avlFindLower cmp 0. t with Some (0., 0) in
utest avlFindLower cmp -1. t with None () in

()
