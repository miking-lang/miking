const { repeat, utest } = require("./benchmarkcommon");

function Node(t1,t2) { return [t1, t2]; }
function Leaf(i) { return i; }

function count(tree) {
    if (Array.isArray(tree)) {
        return count(tree[0]) + count(tree[1]);
    } else if (typeof tree === "number") {
        return tree;
    } else throw new Error("Unknown node");
}

const tree = Node(
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
 )

const r = repeat(() => count(tree));
utest(r, 300);
