
let holeBool
  : {default : Bool, depth : Int} -> Bool
  = lam r.
    r.default

let holeIntRange
  : {default : Bool, depth : Int, min : Int, max : Int} -> Bool
  = lam r.
    r.default
