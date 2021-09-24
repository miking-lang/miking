include "seq.mc"
include "set.mc"
include "common.mc"

-- Gives a compact representation of a set of strings (where a string is a
-- sequence of elements of any type). All children of a node have a common
-- prefix. Each string is identified by an integer.

-- The type of a prefix tree. A node has an element, the set of id's rooted in
-- that subtree, and a set of children. A leaf has an identifier.
type PTree
con Node : { root : a, ids : [Int], children : Map a PTree } -> PTree
con Leaf : Int -> PTree

-- 'prefixTreeEmpty cmp sentinel' creates an empty prefix tree, where 'sentinel' may
-- not be used as value in any string to be added to the tree.
let prefixTreeEmpty = lam cmp : a -> a -> Int. lam sentinel : a.
  Node {root = sentinel, children = mapEmpty cmp, ids = []}

-- 'prefixTreeInsert cmp tree id path' inserts 'path' into the 'tree'.
let prefixTreeInsert = lam cmp. lam tree. lam id : Int. lam path : [a].
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

-- 'prefixTreeInsertMany cmp tree ids paths' inserts the 'paths' into the 'tree'.
let prefixTreeInsertMany = lam cmp. lam tree. lam ids : [Int]. lam paths.
  -- Faster zip for Rope implementation
  let zip = lam l. lam r.
    mapi (lam i. lam x. (x, get r i)) l
  in
  utest zip [1,2,3] [4,5,6] with [(1,4),(2,5),(3,6)] in

  let z = zip ids paths in
  foldl (lam acc. lam idPath : (Int, a). prefixTreeInsert cmp acc idPath.0 idPath.1) tree z

recursive let prefixTreeEq = lam cmp. lam t1. lam t2.
  match (t1, t2) with (Leaf i1, Leaf i2) then eqi i1 i2
  else match (t1, t2) with (Node n1, Node n2) then
    all (lam x. x)
      [ eqi 0 (cmp n1.root n2.root)
      , eqSeq eqi n1.ids n2.ids
      , eqSeq (prefixTreeEq cmp) (mapValues n1.children) (mapValues n2.children)
      ]
  else false
end

mexpr

let empty = prefixTreeEmpty subi 0 in
let treeLeafKey = 0 in

utest prefixTreeInsert subi empty 0 []
with Node {root = 0, ids = [0], children = mapFromSeq subi [(treeLeafKey, Leaf 0)]}
using prefixTreeEq subi
in

utest prefixTreeInsert subi empty 0 [1]
with Node
{ root = 0
, ids = [0]
, children = mapFromSeq subi [(1, Node { root = 1
                                       , ids = [0]
                                       , children = mapFromSeq subi [(treeLeafKey, Leaf 0)]})]}
using prefixTreeEq subi
in

utest prefixTreeInsertMany subi empty [0,1] [[1],[1,2]]
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
using prefixTreeEq subi
in

let t = prefixTreeInsertMany subi empty [0,1,2] [[1],[1,2],[3]] in
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
using prefixTreeEq subi
in

()
