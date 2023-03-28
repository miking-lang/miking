

mexpr


let filename = "test.txt" in

let myString = lam y.
  let str = prerun (readFile filename) in
  map (lam x. if eqc ' ' x then y else x) str
in

dprint(myString);
print "\n----\n";
print (myString '*')
