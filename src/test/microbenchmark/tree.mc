
include "benchmarkcommon.mc"

mexpr

type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in

recursive
  let count = lam tree.
    match tree with Node t then
      let left = t.0 in
      let right = t.1 in
      addi (count left) (count right)
    else match tree with Leaf v then
      v
    else error "Unknown node"
in

let tree = Node(Node(Leaf(3),Node(Leaf(2),Leaf(6))),Leaf(12)) in

bc_repeat (lam. count tree)
