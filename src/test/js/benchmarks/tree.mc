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

let tree = Node(
  Node(
    Node(Node(Node(Leaf(5),Leaf(4)),Leaf(6)), Node(Node(Node(Leaf(5),Leaf(6)),Leaf(6)),Node(Leaf(5),Node(Leaf(5),Node(Node(Node(Leaf(5),Leaf(6)),Leaf(2)),Leaf(6)))))),
    Node(Node(Leaf(12),Node(Node(Node(Node(Leaf(1),Leaf(2)),Leaf(3)),Leaf(4)),Node(Node(Node(Leaf(5),Leaf(6)),Leaf(7)),Leaf(3)))),Node(Node(Leaf(5),Leaf(6)),Leaf(7)))
  ),
  Node(
    Node(
      Node(Leaf(1),Node(Node(Node(Leaf(2),Leaf(3)),Leaf(4)),Node(Node(Node(Leaf(5),Leaf(6)),Leaf(7)),Node(Node(Leaf(5),Leaf(6)),Leaf(6))))),
      Node(Node(Node(Node(Leaf(1),Node(Leaf(5),Leaf(6))),Leaf(3)),Node(Node(Node(Leaf(5),Leaf(6)),Node(Leaf(5),Leaf(6))),Leaf(8))),Leaf(1))
    ),
    Node(
      Node(Leaf(1),Node(Node(Node(Leaf(2),Leaf(3)),Node(Leaf(5),Leaf(6))),Node(Node(Node(Leaf(5),Leaf(6)),Leaf(7)),Leaf(8)))),
      Node(Node(Node(Node(Leaf(1),Node(Leaf(2),Leaf(6))),Leaf(3)),Node(Node(Node(Leaf(5),Leaf(6)),Leaf(7)),Leaf(8))),Leaf(6))
    )
  )
 ) in

let r = repeat (lam. count tree) in
utest r with 300 using eqi in
()
