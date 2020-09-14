


type Info
con Info : {filename: String, row1: Int, col1: Int, row2: Int, col2: Int} -> Info
con NoInfo : () -> Info

type Pos = {filename: String, row: Int, col: Int}

let initPos : String -> Pos = lam filename.
  {filename = filename, row = 1, col = 0}

let posVal : String -> Int -> Int = lam filename. lam row. lam col.
  {filename = filename, row = row, col = col}

let advanceCol : Pos -> Int -> Pos = lam p. lam n.
  {p with col = addi p.col n}

let advanceRow : Pos -> Int -> Pos = lam p. lam n.
  {{p with row = addi p.row n} with col = 0}
