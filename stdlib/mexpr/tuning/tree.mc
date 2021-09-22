
include "seq.mc"
include "set.mc"
include "common.mc"

type Tree
con Node : { root : a, ids : [Int], children : Map a Tree } -> Tree
con Leaf : Int -> Tree

let treeEmpty = lam cmp. lam sentinel.
  Node {root = sentinel, children = mapEmpty cmp, ids = []}

let treeInsert = lam cmp. lam tree. lam id : Int. lam path.
  let eq = lam x. lam y. eqi 0 (cmp x y) in
  match tree with Node t then
    -- Use sentinel value as leaf key as this will never be used as a key in a
    -- map
    let treeLeafKey = t.root in
    let n = length path in
    recursive let insert = lam children. lam i.
      if eqi i n then
        utest mapMem treeLeafKey children with false in
        mapInsert treeLeafKey (Leaf id) children
      else
        let p = get path i in
        match mapLookup p children with Some c then
          -- equal
          match c with Node {root = root, children = cs, ids = ids} then
            let newNode = Node {root = root, children = insert cs (addi i 1), ids = cons id ids} in
            mapInsert p newNode children
          else never
        else
          let newNode = Node {root = p, ids = [id], children = insert (mapEmpty cmp) (addi i 1)} in
          mapInsert p newNode children
    in Node {{t with children = insert t.children 0} with ids = cons id t.ids}
else error "missing sentinel node"

let treeInsertMany = lam cmp. lam tree. lam ids. lam paths.
  -- Faster zip for Rope implementation
  let zip = lam l. lam r.
    mapi (lam i. lam x. (x, get r i)) l
  in
  utest zip [1,2,3] [4,5,6] with [(1,4),(2,5),(3,6)] in

  let z = zip ids paths in
  foldl (lam acc. lam idPath : (Int, a). treeInsert cmp acc idPath.0 idPath.1) tree z

let treeGetIds = lam tree.
  switch tree
  case Leaf id then [id]
  case Node {ids = ids} then ids
  end

let treeGetChildren = lam cmp. lam tree.
  switch tree
  case Leaf _ then mapEmpty cmp
  case Node {children = children} then children
  end

let treeIdsOfDepth = lam cmp. lam depth. lam tree.
  recursive let work = lam d. lam children.
    if eqi d depth then
      [foldl concat [] (map treeGetIds (mapValues children))]
    else
      let grandChildren = map (treeGetChildren cmp) (mapValues children) in
      foldl concat [] (map (work (addi d 1)) grandChildren)
  in
  match tree with Node t then
    filter (lam s. not (null s)) (work 0 t.children)
  else error "missing sentinel node"

recursive let treeEq = lam cmp. lam t1. lam t2.
  match (t1, t2) with (Leaf i1, Leaf i2) then eqi i1 i2
  else match (t1, t2) with (Node n1, Node n2) then
    all (lam x. x)
      [ eqi 0 (cmp n1.root n2.root)
      , eqSeq eqi n1.ids n2.ids
      , eqSeq (treeEq cmp) (mapValues n1.children) (mapValues n2.children)
      ]
  else false
end

mexpr

let empty = treeEmpty subi 0 in
let treeLeafKey = 0 in

utest treeInsert subi empty 0 []
with Node {root = 0, ids = [0], children = mapFromSeq subi [(treeLeafKey, Leaf 0)]}
using treeEq subi
in

utest treeInsert subi empty 0 [1]
with Node
{ root = 0
, ids = [0]
, children = mapFromSeq subi [(1, Node { root = 1
                                       , ids = [0]
                                       , children = mapFromSeq subi [(treeLeafKey, Leaf 0)]})]}
using treeEq subi
in

utest treeInsertMany subi empty [0,1] [[1],[1,2]]
with Node
{ root = 0
, ids = [1,0]
, children =
  mapFromSeq subi [(1,
  Node { root = 1
       , ids = [1,0]
       , children =
         mapFromSeq subi [(treeLeafKey, Leaf 0), (2,
         Node { root = 2
              , ids = [1]
              , children =
                mapFromSeq subi [(treeLeafKey, Leaf 1)]})]})]
}
using treeEq subi
in

let t = treeInsertMany subi empty [0,1,2] [[1],[1,2],[3]] in
utest t
with Node
{ root = 0
, ids = [2,1,0]
, children =
  mapFromSeq subi
  [ (1,
    Node { root = 1
         , ids = [1,0]
         , children =
           mapFromSeq subi [(treeLeafKey, Leaf 0), (2,
           Node { root = 2
                , ids = [1]
                , children =
                  mapFromSeq subi [(treeLeafKey, Leaf 1)]})]})
  , (3, Node { root = 3
             , ids = [2]
             , children =
               mapFromSeq subi [(treeLeafKey, Leaf 2)]
             })
  ]
}
using treeEq subi
in

utest treeIdsOfDepth subi 0 t with [[1,0,2]] in
utest treeIdsOfDepth subi 1 t with [[0,1],[2]] in
utest treeIdsOfDepth subi 2 t with [[1]] in
utest treeIdsOfDepth subi 3 t with [] in

()
