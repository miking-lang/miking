include "string.mc"
include "common.mc"

mexpr
	let a = 1 in
	match {c = {b = a}, b = 2} with {c = {b = b}} then
		printLn join [int2string b, " == ", int2string a];
		printLn eqi a b
	else
		printLn false
