mexpr

type Expr in
con Record : {binds : [(String, Expr)], info : ()} -> Expr in
con Integer : Int -> Expr in

let r = Record {binds = [("x", Integer 2)], info = ()} in
match r with Record {binds = b} in
dprint b;
print "\n"
