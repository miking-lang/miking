include "string.mc"
include "common.mc"

mexpr
	let a = 1 in
	(match {c = {b = a}, b = 2} with {c = {b = b}} then
		printLn (join [int2string b, " == ", int2string a]);
		printLn (if eqi a b then "true" else "false")
	else
    let obj = {c = {b = a}} in
    let a = obj.c.b in
    printLn (int2string a);
		printLn "false"
  );
()
